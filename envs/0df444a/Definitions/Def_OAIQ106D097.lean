-- Prove2me | Definitions.Def_OAIQ106D097
-- name    : OAIQ106D097
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T13:00:15.042736+00:00
-- url     : https://prove2.me/theorems/014272d4-8e4a-413f-bf3d-c5ac72bcbc12
-- title:
--   Definitions bundle OAIQ106D097 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 381 declarations of OpenAI's Lean: 381 definitions. The definitions and types are `OAI.MUB6.Certificate.GramRows.rawRow15547`, `OAI.MUB6.Certificate.GramRows.rawRow15548`, `OAI.MUB6.Certificate.GramRows.rawRow15549`, `OAI.MUB6.Certificate.GramRows.rawRow15550`, `OAI.MUB6.Certificate.GramRows.rawRow15551`, `OAI.MUB6.Certificate.GramRows.rawRow15552`, `OAI.MUB6.Certificate.GramRows.rawRow15553`, `OAI.MUB6.Certificate.GramRows.rawRow15554`, `OAI.MUB6.Certificate.GramRows.rawRow15556`, `OAI.MUB6.Certificate.GramRows.rawRow15557`, `OAI.MUB6.Certificate.GramRows.rawRow15558`, `OAI.MUB6.Certificate.GramRows.rawRow15559`, `OAI.MUB6.Certificate.GramRows.rawRow15560`, `OAI.MUB6.Certificate.GramRows.rawRow15591`, `OAI.MUB6.Certificate.GramRows.rawRow15592`, `OAI.MUB6.Certificate.GramRows.rawRow15593`, `OAI.MUB6.Certificate.GramRows.rawRow15594`, `OAI.MUB6.Certificate.GramRows.rawRow15595`, `OAI.MUB6.Certificate.GramRows.rawRow15596`, `OAI.MUB6.Certificate.GramRows.rawRow15633`, `OAI.MUB6.Certificate.GramRows.rawRow15634`, `OAI.MUB6.Certificate.GramRows.rawRow15635`, `OAI.MUB6.Certificate.GramRows.rawRow15636`, `OAI.MUB6.Certificate.GramRows.rawRow15637`, `OAI.MUB6.Certificate.GramRows.rawRow15638`, `OAI.MUB6.Certificate.GramRows.rawRow15639`, `OAI.MUB6.Certificate.GramRows.rawRow15640`, `OAI.MUB6.Certificate.GramRows.rawRow15641`, `OAI.MUB6.Certificate.GramRows.rawRow15642`, `OAI.MUB6.Certificate.GramRows.rawRow15643`, `OAI.MUB6.Certificate.GramRows.rawRow15644`, `OAI.MUB6.Certificate.GramRows.rawRow15657`, `OAI.MUB6.Certificate.GramRows.rawRow15658`, `OAI.MUB6.Certificate.GramRows.rawRow15659`, `OAI.MUB6.Certificate.GramRows.rawRow15660`, `OAI.MUB6.Certificate.GramRows.rawRow15661`, `OAI.MUB6.Certificate.GramRows.rawRow15662`, `OAI.MUB6.Certificate.GramRows.rawRow15663`, `OAI.MUB6.Certificate.GramRows.rawRow15664`, `OAI.MUB6.Certificate.GramRows.rawRow15665` and 341 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_GramRows_Block0`, `MutuallyUnbiased_GramRows_Block1`, `MutuallyUnbiased_GramRows_Block145`, `MutuallyUnbiased_GramRows_Block146`, `MutuallyUnbiased_GramRows_Block147`, `MutuallyUnbiased_GramRows_Block148`, `MutuallyUnbiased_GramRows_Block149`, `MutuallyUnbiased_GramRows_Block150`, `MutuallyUnbiased_GramRows_Block151`, `MutuallyUnbiased_GramRows_Block2`, `MutuallyUnbiased_GramRows_Block93`, `MutuallyUnbiased_MixedSemantics_Values18`, `MutuallyUnbiased_MixedSemantics_Values25`.
--
--   **Imports.** It imports the bundles `OAIQ106D000`, `OAIQ106D001` and `OAIQ106D002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ106D209`, `OAIQ106D210`, `OAIQ106D211`, `OAIQ106D214`, `OAIQ106D215` and `OAIQ106D217`; the proofs of `OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow0`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow2`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow12`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_13`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_0`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_10`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_12`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_13`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_14`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_6`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_0`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_10`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_12`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_13`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_14`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_15`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_6`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_0`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_2` and `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_6`.
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

def rawRow16 : Integer.Sparse Key := [(key328, -1), (key319, -1), (key316, 2), (key340, 1), (key335, 1), (key316, -1), (key302, -1), (key335, -2), (key319, 1), (key305, 1), (key418, 1), (key409, 1), (key406, -2), (key583, -1), (key578, -1), (key406, 1), (key236, 1), (key418, 2), (key409, -1), (key239, -1), (key595, -1), (key442, -1), (key435, 1), (key316, 1), (key601, 1), (key450, 1), (key435, -1), (key248, -1), (key450, -1), (key328, -1), (key442, 1), (key260, 1), (key469, 2), (key467, -1), (key335, -1), (key475, -2), (key467, 1), (key267, 1), (key475, 1), (key340, 1), (key469, -1), (key271, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow158 : Integer.Sparse Key := [(key1896, -1), (key1896, -1), (key1899, 2), (key1903, 1), (key1903, 1), (key1920, -1), (key1920, -1), (key1911, -2), (key1926, 1), (key1926, 1), (key1351, 1), (key1351, 1), (key1354, -2), (key1472, -1), (key1472, -1), (key1683, 1), (key1683, 1), (key1480, 2), (key1689, -1), (key1689, -1), (key1298, -1), (key1298, -1), (key1326, 1), (key1326, 1), (key1393, 1), (key1393, 1), (key1556, -1), (key1556, -1), (key1444, -1), (key1444, -1), (key1593, 1), (key1593, 1), (key1292, 2), (key1312, -1), (key1312, -1), (key1387, -2), (key1542, 1), (key1542, 1), (key1420, 1), (key1420, 1), (key1569, -1), (key1569, -1)]

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

def rawRow15547 : Integer.Sparse Key := [(key2807, 2), (key2827, 2), (key2801, 2), (key2918, -1), (key2922, -1), (key2784, -1), (key2868, -1), (key2778, -1), (key2851, -1), (key2704, 2), (key2724, 2), (key2698, 2), (key3021, -1), (key3025, -1), (key2630, -1), (key2868, -1), (key2624, -1), (key2851, -1), (key2752, -1), (key2757, -1), (key2669, -1), (key2724, -1), (key2663, -1), (key2698, -1), (key3011, -1), (key3016, -1), (key2614, -1), (key2827, -1), (key2608, -1), (key2801, -1), (key2724, 2), (key3025, 2), (key2638, 2), (key3022, 2), (key2624, 2), (key2698, 2)]

def rawRow15548 : Integer.Sparse Key := [(key2827, 2), (key2807, 2), (key2801, 2), (key2922, -1), (key2918, -1), (key2868, -1), (key2784, -1), (key2851, -1), (key2778, -1), (key2724, 2), (key2704, 2), (key2698, 2), (key3025, -1), (key3021, -1), (key2868, -1), (key2630, -1), (key2851, -1), (key2624, -1), (key2757, -1), (key2752, -1), (key2724, -1), (key2669, -1), (key2698, -1), (key2663, -1), (key3016, -1), (key3011, -1), (key2827, -1), (key2614, -1), (key2801, -1), (key2608, -1), (key3025, 2), (key2724, 2), (key3022, 2), (key2638, 2), (key2698, 2), (key2624, 2)]

def rawRow15549 : Integer.Sparse Key := [(key2851, 2), (key2858, 2), (key2868, 2), (key2778, -1), (key2792, -1), (key2801, -1), (key2919, -1), (key2827, -1), (key2922, -1), (key2851, 2), (key2858, 2), (key2868, 2), (key2624, -1), (key2638, -1), (key2698, -1), (key3022, -1), (key2724, -1), (key3025, -1), (key2778, -1), (key2792, -1), (key2801, -1), (key2919, -1), (key2827, -1), (key2922, -1), (key2624, -1), (key2638, -1), (key2698, -1), (key3022, -1), (key2724, -1), (key3025, -1), (key2608, 2), (key2659, 2), (key2663, 2), (key2757, 2), (key3009, 2), (key3016, 2)]

def rawRow15550 : Integer.Sparse Key := [(key2858, 2), (key2851, 2), (key2868, 2), (key2792, -1), (key2778, -1), (key2919, -1), (key2801, -1), (key2922, -1), (key2827, -1), (key2858, 2), (key2851, 2), (key2868, 2), (key2638, -1), (key2624, -1), (key3022, -1), (key2698, -1), (key3025, -1), (key2724, -1), (key2792, -1), (key2778, -1), (key2919, -1), (key2801, -1), (key2922, -1), (key2827, -1), (key2638, -1), (key2624, -1), (key3022, -1), (key2698, -1), (key3025, -1), (key2724, -1), (key2659, 2), (key2608, 2), (key2757, 2), (key2663, 2), (key3016, 2), (key3009, 2)]

def rawRow15551 : Integer.Sparse Key := [(key2851, 2), (key2868, 2), (key2858, 2), (key2801, -1), (key2827, -1), (key2778, -1), (key2922, -1), (key2792, -1), (key2919, -1), (key2851, 2), (key2868, 2), (key2858, 2), (key2698, -1), (key2724, -1), (key2624, -1), (key3025, -1), (key2638, -1), (key3022, -1), (key2801, -1), (key2827, -1), (key2778, -1), (key2922, -1), (key2792, -1), (key2919, -1), (key2698, -1), (key2724, -1), (key2624, -1), (key3025, -1), (key2638, -1), (key3022, -1), (key2663, 2), (key2757, 2), (key2608, 2), (key3016, 2), (key2659, 2), (key2757, 2)]

def rawRow15552 : Integer.Sparse Key := [(key2868, 2), (key2851, 2), (key2858, 2), (key2827, -1), (key2801, -1), (key2922, -1), (key2778, -1), (key2919, -1), (key2792, -1), (key2868, 2), (key2851, 2), (key2858, 2), (key2724, -1), (key2698, -1), (key3025, -1), (key2624, -1), (key3022, -1), (key2638, -1), (key2827, -1), (key2801, -1), (key2922, -1), (key2778, -1), (key2919, -1), (key2792, -1), (key2724, -1), (key2698, -1), (key3025, -1), (key2624, -1), (key3022, -1), (key2638, -1), (key2757, 2), (key2663, 2), (key3016, 2), (key2608, 2), (key2757, 2), (key2659, 2)]

def rawRow15553 : Integer.Sparse Key := [(key2858, 2), (key2868, 2), (key2851, 2), (key2919, -1), (key2922, -1), (key2792, -1), (key2827, -1), (key2778, -1), (key2801, -1), (key2858, 2), (key2868, 2), (key2851, 2), (key3022, -1), (key3025, -1), (key2638, -1), (key2724, -1), (key2624, -1), (key2698, -1), (key2919, -1), (key2922, -1), (key2792, -1), (key2827, -1), (key2778, -1), (key2801, -1), (key3022, -1), (key3025, -1), (key2638, -1), (key2724, -1), (key2624, -1), (key2698, -1), (key3009, 2), (key3016, 2), (key2659, 2), (key2757, 2), (key2608, 2), (key2663, 2)]

def rawRow15554 : Integer.Sparse Key := [(key2868, 2), (key2858, 2), (key2851, 2), (key2922, -1), (key2919, -1), (key2827, -1), (key2792, -1), (key2801, -1), (key2778, -1), (key2868, 2), (key2858, 2), (key2851, 2), (key3025, -1), (key3022, -1), (key2724, -1), (key2638, -1), (key2698, -1), (key2624, -1), (key2922, -1), (key2919, -1), (key2827, -1), (key2792, -1), (key2801, -1), (key2778, -1), (key3025, -1), (key3022, -1), (key2724, -1), (key2638, -1), (key2698, -1), (key2624, -1), (key3016, 2), (key3009, 2), (key2757, 2), (key2659, 2), (key2663, 2), (key2608, 2)]

def rawRow15556 : Integer.Sparse Key := [(key2889, 4), (key2772, 4), (key2889, 4), (key2843, -2), (key2887, -2), (key2766, -2), (key2887, -2), (key2766, -2), (key2843, -2), (key2968, -2), (key2995, -2), (key2931, -2), (key2995, -2), (key2931, -2), (key2968, -2), (key2966, 4), (key2929, 4), (key2966, 4)]

def rawRow15557 : Integer.Sparse Key := [(key2889, 4), (key2889, 4), (key2772, 4), (key2887, -2), (key2843, -2), (key2887, -2), (key2766, -2), (key2843, -2), (key2766, -2), (key2995, -2), (key2968, -2), (key2995, -2), (key2931, -2), (key2968, -2), (key2931, -2), (key2966, 4), (key2966, 4), (key2929, 4)]

def rawRow15558 : Integer.Sparse Key := [(key2411, 4), (key2484, 4), (key2484, 4), (key2443, -2), (key2443, -2), (key2509, -2), (key2509, -2), (key2524, -2), (key2524, -2), (key2406, -2), (key2406, -2), (key2472, -2), (key2472, -2), (key2480, -2), (key2480, -2), (key2437, 4), (key2503, 4), (key2503, 4)]

def rawRow15559 : Integer.Sparse Key := [(key2484, 4), (key2411, 4), (key2484, 4), (key2509, -2), (key2524, -2), (key2443, -2), (key2524, -2), (key2443, -2), (key2509, -2), (key2472, -2), (key2480, -2), (key2406, -2), (key2480, -2), (key2406, -2), (key2472, -2), (key2503, 4), (key2437, 4), (key2503, 4)]

def rawRow15560 : Integer.Sparse Key := [(key2484, 4), (key2484, 4), (key2411, 4), (key2524, -2), (key2509, -2), (key2524, -2), (key2443, -2), (key2509, -2), (key2443, -2), (key2480, -2), (key2472, -2), (key2480, -2), (key2406, -2), (key2472, -2), (key2406, -2), (key2503, 4), (key2503, 4), (key2437, 4)]

def rawRow15591 : Integer.Sparse Key := [(key2669, -1), (key2669, -1), (key2704, -1), (key2704, -1), (key2752, -1), (key2752, -1), (key2663, 2), (key2698, 2), (key2698, 2), (key2792, -1), (key2792, -1), (key2858, -1), (key2858, -1), (key2919, -1), (key2919, -1), (key2784, 2), (key2784, 2), (key2807, 2), (key2807, 2), (key2918, 2), (key2918, 2), (key2778, -1), (key2778, -1), (key2801, -1), (key2801, -1), (key2851, -1), (key2851, -1), (key3009, 2), (key3022, 2), (key3022, 2), (key3007, -1), (key3007, -1), (key3011, -1), (key3011, -1), (key3021, -1), (key3021, -1)]

def rawRow15592 : Integer.Sparse Key := [(key2704, -1), (key2752, -1), (key2669, -1), (key2752, -1), (key2669, -1), (key2704, -1), (key2698, 2), (key2663, 2), (key2698, 2), (key2858, -1), (key2919, -1), (key2792, -1), (key2919, -1), (key2792, -1), (key2858, -1), (key2807, 2), (key2918, 2), (key2784, 2), (key2918, 2), (key2784, 2), (key2807, 2), (key2801, -1), (key2851, -1), (key2778, -1), (key2851, -1), (key2778, -1), (key2801, -1), (key3022, 2), (key3009, 2), (key3022, 2), (key3011, -1), (key3021, -1), (key3007, -1), (key3021, -1), (key3007, -1), (key3011, -1)]

def rawRow15593 : Integer.Sparse Key := [(key2752, -1), (key2704, -1), (key2752, -1), (key2669, -1), (key2704, -1), (key2669, -1), (key2698, 2), (key2698, 2), (key2663, 2), (key2919, -1), (key2858, -1), (key2919, -1), (key2792, -1), (key2858, -1), (key2792, -1), (key2918, 2), (key2807, 2), (key2918, 2), (key2784, 2), (key2807, 2), (key2784, 2), (key2851, -1), (key2801, -1), (key2851, -1), (key2778, -1), (key2801, -1), (key2778, -1), (key3022, 2), (key3022, 2), (key3009, 2), (key3021, -1), (key3011, -1), (key3021, -1), (key3007, -1), (key3011, -1), (key3007, -1)]

def rawRow15594 : Integer.Sparse Key := [(key2752, -1), (key2752, -1), (key2918, -1), (key2918, -1), (key2919, -1), (key2919, -1), (key2757, 2), (key2922, 2), (key2922, 2), (key2669, -1), (key2669, -1), (key2784, -1), (key2784, -1), (key2792, -1), (key2792, -1), (key2704, 2), (key2704, 2), (key2807, 2), (key2807, 2), (key2858, 2), (key2858, 2), (key2724, -1), (key2724, -1), (key2827, -1), (key2827, -1), (key2868, -1), (key2868, -1), (key2663, 2), (key2698, 2), (key2698, 2), (key2778, -1), (key2778, -1), (key2801, -1), (key2801, -1), (key2851, -1), (key2851, -1)]

def rawRow15595 : Integer.Sparse Key := [(key2918, -1), (key2919, -1), (key2752, -1), (key2919, -1), (key2752, -1), (key2918, -1), (key2922, 2), (key2757, 2), (key2922, 2), (key2784, -1), (key2792, -1), (key2669, -1), (key2792, -1), (key2669, -1), (key2784, -1), (key2807, 2), (key2858, 2), (key2704, 2), (key2858, 2), (key2704, 2), (key2807, 2), (key2827, -1), (key2868, -1), (key2724, -1), (key2868, -1), (key2724, -1), (key2827, -1), (key2698, 2), (key2663, 2), (key2698, 2), (key2801, -1), (key2851, -1), (key2778, -1), (key2851, -1), (key2778, -1), (key2801, -1)]

def rawRow15596 : Integer.Sparse Key := [(key2919, -1), (key2918, -1), (key2919, -1), (key2752, -1), (key2918, -1), (key2752, -1), (key2922, 2), (key2922, 2), (key2757, 2), (key2792, -1), (key2784, -1), (key2792, -1), (key2669, -1), (key2784, -1), (key2669, -1), (key2858, 2), (key2807, 2), (key2858, 2), (key2704, 2), (key2807, 2), (key2704, 2), (key2868, -1), (key2827, -1), (key2868, -1), (key2724, -1), (key2827, -1), (key2724, -1), (key2698, 2), (key2698, 2), (key2663, 2), (key2851, -1), (key2801, -1), (key2851, -1), (key2778, -1), (key2801, -1), (key2778, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block146
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow15633 : Integer.Sparse Key := [(key2668, -1), (key2668, -1), (key2703, -1), (key2703, -1), (key2736, -1), (key2736, -1), (key2664, 2), (key2699, 2), (key2699, 2), (key2791, -1), (key2791, -1), (key2857, -1), (key2857, -1), (key2896, -1), (key2896, -1), (key2783, 2), (key2783, 2), (key2806, 2), (key2806, 2), (key2894, 2), (key2894, 2), (key2779, -1), (key2779, -1), (key2802, -1), (key2802, -1), (key2852, -1), (key2852, -1), (key2942, 2), (key2975, 2), (key2975, 2), (key2937, -1), (key2937, -1), (key2949, -1), (key2949, -1), (key2973, -1), (key2973, -1)]

def rawRow15634 : Integer.Sparse Key := [(key2703, -1), (key2736, -1), (key2668, -1), (key2736, -1), (key2668, -1), (key2703, -1), (key2699, 2), (key2664, 2), (key2699, 2), (key2857, -1), (key2896, -1), (key2791, -1), (key2896, -1), (key2791, -1), (key2857, -1), (key2806, 2), (key2894, 2), (key2783, 2), (key2894, 2), (key2783, 2), (key2806, 2), (key2802, -1), (key2852, -1), (key2779, -1), (key2852, -1), (key2779, -1), (key2802, -1), (key2975, 2), (key2942, 2), (key2975, 2), (key2949, -1), (key2973, -1), (key2937, -1), (key2973, -1), (key2937, -1), (key2949, -1)]

def rawRow15635 : Integer.Sparse Key := [(key2736, -1), (key2703, -1), (key2736, -1), (key2668, -1), (key2703, -1), (key2668, -1), (key2699, 2), (key2699, 2), (key2664, 2), (key2896, -1), (key2857, -1), (key2896, -1), (key2791, -1), (key2857, -1), (key2791, -1), (key2894, 2), (key2806, 2), (key2894, 2), (key2783, 2), (key2806, 2), (key2783, 2), (key2852, -1), (key2802, -1), (key2852, -1), (key2779, -1), (key2802, -1), (key2779, -1), (key2975, 2), (key2975, 2), (key2942, 2), (key2973, -1), (key2949, -1), (key2973, -1), (key2937, -1), (key2949, -1), (key2937, -1)]

def rawRow15636 : Integer.Sparse Key := [(key2613, -1), (key2613, -1), (key2806, -1), (key2806, -1), (key2949, -1), (key2949, -1), (key2609, 2), (key2802, 2), (key2802, 2), (key2637, -1), (key2637, -1), (key2857, -1), (key2857, -1), (key2975, -1), (key2975, -1), (key2629, 2), (key2629, 2), (key2703, 2), (key2703, 2), (key2973, 2), (key2973, 2), (key2625, -1), (key2625, -1), (key2699, -1), (key2699, -1), (key2852, -1), (key2852, -1), (key2652, 2), (key2896, 2), (key2896, 2), (key2647, -1), (key2647, -1), (key2736, -1), (key2736, -1), (key2894, -1), (key2894, -1)]

def rawRow15637 : Integer.Sparse Key := [(key2806, -1), (key2949, -1), (key2613, -1), (key2949, -1), (key2613, -1), (key2806, -1), (key2802, 2), (key2609, 2), (key2802, 2), (key2857, -1), (key2975, -1), (key2637, -1), (key2975, -1), (key2637, -1), (key2857, -1), (key2703, 2), (key2973, 2), (key2629, 2), (key2973, 2), (key2629, 2), (key2703, 2), (key2699, -1), (key2852, -1), (key2625, -1), (key2852, -1), (key2625, -1), (key2699, -1), (key2896, 2), (key2652, 2), (key2896, 2), (key2736, -1), (key2894, -1), (key2647, -1), (key2894, -1), (key2647, -1), (key2736, -1)]

def rawRow15638 : Integer.Sparse Key := [(key2949, -1), (key2806, -1), (key2949, -1), (key2613, -1), (key2806, -1), (key2613, -1), (key2802, 2), (key2802, 2), (key2609, 2), (key2975, -1), (key2857, -1), (key2975, -1), (key2637, -1), (key2857, -1), (key2637, -1), (key2973, 2), (key2703, 2), (key2973, 2), (key2629, 2), (key2703, 2), (key2629, 2), (key2852, -1), (key2699, -1), (key2852, -1), (key2625, -1), (key2699, -1), (key2625, -1), (key2896, 2), (key2896, 2), (key2652, 2), (key2894, -1), (key2736, -1), (key2894, -1), (key2647, -1), (key2736, -1), (key2647, -1)]

def rawRow15639 : Integer.Sparse Key := [(key2791, -1), (key2791, -1), (key2857, -1), (key2857, -1), (key2896, -1), (key2896, -1), (key2942, 2), (key2975, 2), (key2975, 2), (key2668, -1), (key2668, -1), (key2703, -1), (key2703, -1), (key2736, -1), (key2736, -1), (key2783, 2), (key2783, 2), (key2806, 2), (key2806, 2), (key2894, 2), (key2894, 2), (key2937, -1), (key2937, -1), (key2949, -1), (key2949, -1), (key2973, -1), (key2973, -1), (key2664, 2), (key2699, 2), (key2699, 2), (key2779, -1), (key2779, -1), (key2802, -1), (key2802, -1), (key2852, -1), (key2852, -1)]

def rawRow15640 : Integer.Sparse Key := [(key2857, -1), (key2896, -1), (key2791, -1), (key2896, -1), (key2791, -1), (key2857, -1), (key2975, 2), (key2942, 2), (key2975, 2), (key2703, -1), (key2736, -1), (key2668, -1), (key2736, -1), (key2668, -1), (key2703, -1), (key2806, 2), (key2894, 2), (key2783, 2), (key2894, 2), (key2783, 2), (key2806, 2), (key2949, -1), (key2973, -1), (key2937, -1), (key2973, -1), (key2937, -1), (key2949, -1), (key2699, 2), (key2664, 2), (key2699, 2), (key2802, -1), (key2852, -1), (key2779, -1), (key2852, -1), (key2779, -1), (key2802, -1)]

def rawRow15641 : Integer.Sparse Key := [(key2896, -1), (key2857, -1), (key2896, -1), (key2791, -1), (key2857, -1), (key2791, -1), (key2975, 2), (key2975, 2), (key2942, 2), (key2736, -1), (key2703, -1), (key2736, -1), (key2668, -1), (key2703, -1), (key2668, -1), (key2894, 2), (key2806, 2), (key2894, 2), (key2783, 2), (key2806, 2), (key2783, 2), (key2973, -1), (key2949, -1), (key2973, -1), (key2937, -1), (key2949, -1), (key2937, -1), (key2699, 2), (key2699, 2), (key2664, 2), (key2852, -1), (key2802, -1), (key2852, -1), (key2779, -1), (key2802, -1), (key2779, -1)]

def rawRow15642 : Integer.Sparse Key := [(key2637, -1), (key2637, -1), (key2857, -1), (key2857, -1), (key2975, -1), (key2975, -1), (key2652, 2), (key2896, 2), (key2896, 2), (key2613, -1), (key2613, -1), (key2806, -1), (key2806, -1), (key2949, -1), (key2949, -1), (key2629, 2), (key2629, 2), (key2703, 2), (key2703, 2), (key2973, 2), (key2973, 2), (key2647, -1), (key2647, -1), (key2736, -1), (key2736, -1), (key2894, -1), (key2894, -1), (key2609, 2), (key2802, 2), (key2802, 2), (key2625, -1), (key2625, -1), (key2699, -1), (key2699, -1), (key2852, -1), (key2852, -1)]

def rawRow15643 : Integer.Sparse Key := [(key2857, -1), (key2975, -1), (key2637, -1), (key2975, -1), (key2637, -1), (key2857, -1), (key2896, 2), (key2652, 2), (key2896, 2), (key2806, -1), (key2949, -1), (key2613, -1), (key2949, -1), (key2613, -1), (key2806, -1), (key2703, 2), (key2973, 2), (key2629, 2), (key2973, 2), (key2629, 2), (key2703, 2), (key2736, -1), (key2894, -1), (key2647, -1), (key2894, -1), (key2647, -1), (key2736, -1), (key2802, 2), (key2609, 2), (key2802, 2), (key2699, -1), (key2852, -1), (key2625, -1), (key2852, -1), (key2625, -1), (key2699, -1)]

def rawRow15644 : Integer.Sparse Key := [(key2975, -1), (key2857, -1), (key2975, -1), (key2637, -1), (key2857, -1), (key2637, -1), (key2896, 2), (key2896, 2), (key2652, 2), (key2949, -1), (key2806, -1), (key2949, -1), (key2613, -1), (key2806, -1), (key2613, -1), (key2973, 2), (key2703, 2), (key2973, 2), (key2629, 2), (key2703, 2), (key2629, 2), (key2894, -1), (key2736, -1), (key2894, -1), (key2647, -1), (key2736, -1), (key2647, -1), (key2802, 2), (key2802, 2), (key2609, 2), (key2852, -1), (key2699, -1), (key2852, -1), (key2625, -1), (key2699, -1), (key2625, -1)]

def rawRow15657 : Integer.Sparse Key := [(key2383, 2), (key2394, 2), (key2394, 2), (key2378, -2), (key2378, -2), (key2390, -2), (key2880, 2), (key2910, 2), (key2910, 2), (key2766, -1), (key2766, -1), (key2843, -1), (key2843, -1), (key2887, -1), (key2887, -1), (key2989, -2), (key2989, -2), (key3002, -2), (key2931, -1), (key2931, -1), (key2968, -1), (key2968, -1), (key2995, -1), (key2995, -1), (key2929, 4), (key2966, 4), (key2966, 4)]

def rawRow15658 : Integer.Sparse Key := [(key2394, 2), (key2383, 2), (key2394, 2), (key2378, -2), (key2390, -2), (key2378, -2), (key2910, 2), (key2880, 2), (key2910, 2), (key2843, -1), (key2887, -1), (key2766, -1), (key2887, -1), (key2766, -1), (key2843, -1), (key2989, -2), (key3002, -2), (key2989, -2), (key2968, -1), (key2995, -1), (key2931, -1), (key2995, -1), (key2931, -1), (key2968, -1), (key2966, 4), (key2929, 4), (key2966, 4)]

def rawRow15659 : Integer.Sparse Key := [(key2394, 2), (key2394, 2), (key2383, 2), (key2390, -2), (key2378, -2), (key2378, -2), (key2910, 2), (key2910, 2), (key2880, 2), (key2887, -1), (key2843, -1), (key2887, -1), (key2766, -1), (key2843, -1), (key2766, -1), (key3002, -2), (key2989, -2), (key2989, -2), (key2995, -1), (key2968, -1), (key2995, -1), (key2931, -1), (key2968, -1), (key2931, -1), (key2966, 4), (key2966, 4), (key2929, 4)]

def rawRow15660 : Integer.Sparse Key := [(key2411, 2), (key2443, 2), (key2443, 2), (key2406, -2), (key2406, -2), (key2437, -2), (key2880, 2), (key2989, 2), (key2989, 2), (key2587, -1), (key2587, -1), (key2843, -1), (key2843, -1), (key2966, -1), (key2966, -1), (key2910, -2), (key2910, -2), (key3002, -2), (key2600, -1), (key2600, -1), (key2889, -1), (key2889, -1), (key2995, -1), (key2995, -1), (key2598, 4), (key2887, 4), (key2887, 4)]

def rawRow15661 : Integer.Sparse Key := [(key2443, 2), (key2411, 2), (key2443, 2), (key2406, -2), (key2437, -2), (key2406, -2), (key2989, 2), (key2880, 2), (key2989, 2), (key2843, -1), (key2966, -1), (key2587, -1), (key2966, -1), (key2587, -1), (key2843, -1), (key2910, -2), (key3002, -2), (key2910, -2), (key2889, -1), (key2995, -1), (key2600, -1), (key2995, -1), (key2600, -1), (key2889, -1), (key2887, 4), (key2598, 4), (key2887, 4)]

def rawRow15662 : Integer.Sparse Key := [(key2443, 2), (key2443, 2), (key2411, 2), (key2437, -2), (key2406, -2), (key2406, -2), (key2989, 2), (key2989, 2), (key2880, 2), (key2966, -1), (key2843, -1), (key2966, -1), (key2587, -1), (key2843, -1), (key2587, -1), (key3002, -2), (key2910, -2), (key2910, -2), (key2995, -1), (key2889, -1), (key2995, -1), (key2600, -1), (key2889, -1), (key2600, -1), (key2887, 4), (key2887, 4), (key2598, 4)]

def rawRow15663 : Integer.Sparse Key := [(key2569, 2), (key2571, 2), (key2571, 2), (key2576, -2), (key2576, -2), (key2580, -2), (key2383, 2), (key2394, 2), (key2394, 2), (key2443, -1), (key2443, -1), (key2509, -1), (key2509, -1), (key2524, -1), (key2524, -1), (key2378, -2), (key2378, -2), (key2390, -2), (key2406, -1), (key2406, -1), (key2472, -1), (key2472, -1), (key2480, -1), (key2480, -1), (key2437, 4), (key2503, 4), (key2503, 4)]

def rawRow15664 : Integer.Sparse Key := [(key2571, 2), (key2569, 2), (key2571, 2), (key2576, -2), (key2580, -2), (key2576, -2), (key2394, 2), (key2383, 2), (key2394, 2), (key2509, -1), (key2524, -1), (key2443, -1), (key2524, -1), (key2443, -1), (key2509, -1), (key2378, -2), (key2390, -2), (key2378, -2), (key2472, -1), (key2480, -1), (key2406, -1), (key2480, -1), (key2406, -1), (key2472, -1), (key2503, 4), (key2437, 4), (key2503, 4)]

def rawRow15665 : Integer.Sparse Key := [(key2571, 2), (key2571, 2), (key2569, 2), (key2580, -2), (key2576, -2), (key2576, -2), (key2394, 2), (key2394, 2), (key2383, 2), (key2524, -1), (key2509, -1), (key2524, -1), (key2443, -1), (key2509, -1), (key2443, -1), (key2390, -2), (key2378, -2), (key2378, -2), (key2480, -1), (key2472, -1), (key2480, -1), (key2406, -1), (key2472, -1), (key2406, -1), (key2503, 4), (key2503, 4), (key2437, 4)]

def rawRow15666 : Integer.Sparse Key := [(key2569, 2), (key2576, 2), (key2576, 2), (key2571, -2), (key2571, -2), (key2580, -2), (key2411, 2), (key2443, 2), (key2443, 2), (key2394, -1), (key2394, -1), (key2484, -1), (key2484, -1), (key2524, -1), (key2524, -1), (key2406, -2), (key2406, -2), (key2437, -2), (key2378, -1), (key2378, -1), (key2472, -1), (key2472, -1), (key2503, -1), (key2503, -1), (key2390, 4), (key2480, 4), (key2480, 4)]

def rawRow15667 : Integer.Sparse Key := [(key2576, 2), (key2569, 2), (key2576, 2), (key2571, -2), (key2580, -2), (key2571, -2), (key2443, 2), (key2411, 2), (key2443, 2), (key2484, -1), (key2524, -1), (key2394, -1), (key2524, -1), (key2394, -1), (key2484, -1), (key2406, -2), (key2437, -2), (key2406, -2), (key2472, -1), (key2503, -1), (key2378, -1), (key2503, -1), (key2378, -1), (key2472, -1), (key2480, 4), (key2390, 4), (key2480, 4)]

def rawRow15668 : Integer.Sparse Key := [(key2576, 2), (key2576, 2), (key2569, 2), (key2580, -2), (key2571, -2), (key2571, -2), (key2443, 2), (key2443, 2), (key2411, 2), (key2524, -1), (key2484, -1), (key2524, -1), (key2394, -1), (key2484, -1), (key2394, -1), (key2437, -2), (key2406, -2), (key2406, -2), (key2503, -1), (key2472, -1), (key2503, -1), (key2378, -1), (key2472, -1), (key2378, -1), (key2480, 4), (key2480, 4), (key2390, 4)]

def rawRow15669 : Integer.Sparse Key := [(key2657, 2), (key2657, 2), (key2659, 2), (key2614, -1), (key2614, -1), (key2630, -1), (key2630, -1), (key2638, -1), (key2638, -1), (key2724, 2), (key2724, 2), (key2757, 2), (key2669, -1), (key2669, -1), (key2704, -1), (key2704, -1), (key2752, -1), (key2752, -1), (key2827, -1), (key2827, -1), (key2868, -1), (key2868, -1), (key2922, -1), (key2922, -1), (key2792, -1), (key2792, -1), (key2858, -1), (key2858, -1), (key2919, -1), (key2919, -1), (key2784, 2), (key2784, 2), (key2807, 2), (key2807, 2), (key2918, 2), (key2918, 2)]

def rawRow15670 : Integer.Sparse Key := [(key2657, 2), (key2659, 2), (key2657, 2), (key2630, -1), (key2638, -1), (key2614, -1), (key2638, -1), (key2614, -1), (key2630, -1), (key2724, 2), (key2757, 2), (key2724, 2), (key2704, -1), (key2752, -1), (key2669, -1), (key2752, -1), (key2669, -1), (key2704, -1), (key2868, -1), (key2922, -1), (key2827, -1), (key2922, -1), (key2827, -1), (key2868, -1), (key2858, -1), (key2919, -1), (key2792, -1), (key2919, -1), (key2792, -1), (key2858, -1), (key2807, 2), (key2918, 2), (key2784, 2), (key2918, 2), (key2784, 2), (key2807, 2)]

def rawRow15671 : Integer.Sparse Key := [(key2659, 2), (key2657, 2), (key2657, 2), (key2638, -1), (key2630, -1), (key2638, -1), (key2614, -1), (key2630, -1), (key2614, -1), (key2757, 2), (key2724, 2), (key2724, 2), (key2752, -1), (key2704, -1), (key2752, -1), (key2669, -1), (key2704, -1), (key2669, -1), (key2922, -1), (key2868, -1), (key2922, -1), (key2827, -1), (key2868, -1), (key2827, -1), (key2919, -1), (key2858, -1), (key2919, -1), (key2792, -1), (key2858, -1), (key2792, -1), (key2918, 2), (key2807, 2), (key2918, 2), (key2784, 2), (key2807, 2), (key2784, 2)]

def rawRow15672 : Integer.Sparse Key := [(key2752, 2), (key2752, 2), (key2757, 2), (key2669, -1), (key2669, -1), (key2704, -1), (key2704, -1), (key2724, -1), (key2724, -1), (key3011, 2), (key3011, 2), (key3016, 2), (key2614, -1), (key2614, -1), (key2807, -1), (key2807, -1), (key2827, -1), (key2827, -1), (key2724, -1), (key2724, -1), (key2868, -1), (key2868, -1), (key3025, -1), (key3025, -1), (key2638, -1), (key2638, -1), (key2858, -1), (key2858, -1), (key3022, -1), (key3022, -1), (key2630, 2), (key2630, 2), (key2704, 2), (key2704, 2), (key3021, 2), (key3021, 2)]

def rawRow15673 : Integer.Sparse Key := [(key2752, 2), (key2757, 2), (key2752, 2), (key2704, -1), (key2724, -1), (key2669, -1), (key2724, -1), (key2669, -1), (key2704, -1), (key3011, 2), (key3016, 2), (key3011, 2), (key2807, -1), (key2827, -1), (key2614, -1), (key2827, -1), (key2614, -1), (key2807, -1), (key2868, -1), (key3025, -1), (key2724, -1), (key3025, -1), (key2724, -1), (key2868, -1), (key2858, -1), (key3022, -1), (key2638, -1), (key3022, -1), (key2638, -1), (key2858, -1), (key2704, 2), (key3021, 2), (key2630, 2), (key3021, 2), (key2630, 2), (key2704, 2)]

def rawRow15674 : Integer.Sparse Key := [(key2757, 2), (key2752, 2), (key2752, 2), (key2724, -1), (key2704, -1), (key2724, -1), (key2669, -1), (key2704, -1), (key2669, -1), (key3016, 2), (key3011, 2), (key3011, 2), (key2827, -1), (key2807, -1), (key2827, -1), (key2614, -1), (key2807, -1), (key2614, -1), (key3025, -1), (key2868, -1), (key3025, -1), (key2724, -1), (key2868, -1), (key2724, -1), (key3022, -1), (key2858, -1), (key3022, -1), (key2638, -1), (key2858, -1), (key2638, -1), (key3021, 2), (key2704, 2), (key3021, 2), (key2630, 2), (key2704, 2), (key2630, 2)]

def rawRow15675 : Integer.Sparse Key := [(key3007, 2), (key3007, 2), (key3009, 2), (key3011, -1), (key3011, -1), (key3021, -1), (key3021, -1), (key3022, -1), (key3022, -1), (key2657, 2), (key2657, 2), (key2659, 2), (key2752, -1), (key2752, -1), (key2918, -1), (key2918, -1), (key2919, -1), (key2919, -1), (key2614, -1), (key2614, -1), (key2630, -1), (key2630, -1), (key2638, -1), (key2638, -1), (key2669, -1), (key2669, -1), (key2784, -1), (key2784, -1), (key2792, -1), (key2792, -1), (key2704, 2), (key2704, 2), (key2807, 2), (key2807, 2), (key2858, 2), (key2858, 2)]

def rawRow15676 : Integer.Sparse Key := [(key3007, 2), (key3009, 2), (key3007, 2), (key3021, -1), (key3022, -1), (key3011, -1), (key3022, -1), (key3011, -1), (key3021, -1), (key2657, 2), (key2659, 2), (key2657, 2), (key2918, -1), (key2919, -1), (key2752, -1), (key2919, -1), (key2752, -1), (key2918, -1), (key2630, -1), (key2638, -1), (key2614, -1), (key2638, -1), (key2614, -1), (key2630, -1), (key2784, -1), (key2792, -1), (key2669, -1), (key2792, -1), (key2669, -1), (key2784, -1), (key2807, 2), (key2858, 2), (key2704, 2), (key2858, 2), (key2704, 2), (key2807, 2)]

def rawRow15677 : Integer.Sparse Key := [(key3009, 2), (key3007, 2), (key3007, 2), (key3022, -1), (key3021, -1), (key3022, -1), (key3011, -1), (key3021, -1), (key3011, -1), (key2659, 2), (key2657, 2), (key2657, 2), (key2919, -1), (key2918, -1), (key2919, -1), (key2752, -1), (key2918, -1), (key2752, -1), (key2638, -1), (key2630, -1), (key2638, -1), (key2614, -1), (key2630, -1), (key2614, -1), (key2792, -1), (key2784, -1), (key2792, -1), (key2669, -1), (key2784, -1), (key2669, -1), (key2858, 2), (key2807, 2), (key2858, 2), (key2704, 2), (key2807, 2), (key2704, 2)]

def rawRow15678 : Integer.Sparse Key := [(key3011, 2), (key3011, 2), (key3016, 2), (key3007, -1), (key3007, -1), (key3021, -1), (key3021, -1), (key3025, -1), (key3025, -1), (key2752, 2), (key2752, 2), (key2757, 2), (key2657, -1), (key2657, -1), (key2918, -1), (key2918, -1), (key2922, -1), (key2922, -1), (key2669, -1), (key2669, -1), (key2704, -1), (key2704, -1), (key2724, -1), (key2724, -1), (key2614, -1), (key2614, -1), (key2807, -1), (key2807, -1), (key2827, -1), (key2827, -1), (key2630, 2), (key2630, 2), (key2784, 2), (key2784, 2), (key2868, 2), (key2868, 2)]

def rawRow15679 : Integer.Sparse Key := [(key3011, 2), (key3016, 2), (key3011, 2), (key3021, -1), (key3025, -1), (key3007, -1), (key3025, -1), (key3007, -1), (key3021, -1), (key2752, 2), (key2757, 2), (key2752, 2), (key2918, -1), (key2922, -1), (key2657, -1), (key2922, -1), (key2657, -1), (key2918, -1), (key2704, -1), (key2724, -1), (key2669, -1), (key2724, -1), (key2669, -1), (key2704, -1), (key2807, -1), (key2827, -1), (key2614, -1), (key2827, -1), (key2614, -1), (key2807, -1), (key2784, 2), (key2868, 2), (key2630, 2), (key2868, 2), (key2630, 2), (key2784, 2)]

def rawRow15680 : Integer.Sparse Key := [(key3016, 2), (key3011, 2), (key3011, 2), (key3025, -1), (key3021, -1), (key3025, -1), (key3007, -1), (key3021, -1), (key3007, -1), (key2757, 2), (key2752, 2), (key2752, 2), (key2922, -1), (key2918, -1), (key2922, -1), (key2657, -1), (key2918, -1), (key2657, -1), (key2724, -1), (key2704, -1), (key2724, -1), (key2669, -1), (key2704, -1), (key2669, -1), (key2827, -1), (key2807, -1), (key2827, -1), (key2614, -1), (key2807, -1), (key2614, -1), (key2868, 2), (key2784, 2), (key2868, 2), (key2630, 2), (key2784, 2), (key2630, 2)]

def rawRow15681 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, -1), (key2638, -1), (key2657, -1), (key2659, -1), (key2614, 2), (key2630, 2), (key2638, 2), (key2663, 1), (key2669, 1), (key2698, 1), (key2724, 1), (key2752, 1), (key2757, 1), (key2669, -2), (key2704, -2), (key2724, -2), (key2801, -1), (key2807, -1), (key2851, -1), (key2858, -1), (key2918, -1), (key2919, -1), (key2778, 1), (key2784, 1), (key2851, 1), (key2868, 1), (key2918, 1), (key2922, 1), (key3011, 2), (key3021, 2), (key3022, 2), (key3007, -2), (key3021, -2), (key3025, -2)]

def rawRow15682 : Integer.Sparse Key := [(key2614, -1), (key2608, -1), (key2638, -1), (key2624, -1), (key2659, -1), (key2657, -1), (key2614, 2), (key2638, 2), (key2630, 2), (key2669, 1), (key2663, 1), (key2724, 1), (key2698, 1), (key2757, 1), (key2752, 1), (key2669, -2), (key2724, -2), (key2704, -2), (key2807, -1), (key2801, -1), (key2858, -1), (key2851, -1), (key2919, -1), (key2918, -1), (key2784, 1), (key2778, 1), (key2868, 1), (key2851, 1), (key2922, 1), (key2918, 1), (key3011, 2), (key3022, 2), (key3021, 2), (key3007, -2), (key3025, -2), (key3021, -2)]

def rawRow15683 : Integer.Sparse Key := [(key2624, -1), (key2638, -1), (key2608, -1), (key2659, -1), (key2614, -1), (key2638, -1), (key2630, 2), (key2614, 2), (key2638, 2), (key2698, 1), (key2752, 1), (key2663, 1), (key2757, 1), (key2669, 1), (key2724, 1), (key2704, -2), (key2669, -2), (key2724, -2), (key2851, -1), (key2918, -1), (key2801, -1), (key2919, -1), (key2807, -1), (key2858, -1), (key2851, 1), (key2918, 1), (key2778, 1), (key2922, 1), (key2784, 1), (key2868, 1), (key3021, 2), (key3011, 2), (key3022, 2), (key3021, -2), (key3007, -2), (key3025, -2)]

def rawRow15684 : Integer.Sparse Key := [(key2638, -1), (key2624, -1), (key2659, -1), (key2608, -1), (key2638, -1), (key2614, -1), (key2630, 2), (key2638, 2), (key2614, 2), (key2752, 1), (key2698, 1), (key2757, 1), (key2663, 1), (key2724, 1), (key2669, 1), (key2704, -2), (key2724, -2), (key2669, -2), (key2918, -1), (key2851, -1), (key2919, -1), (key2801, -1), (key2858, -1), (key2807, -1), (key2918, 1), (key2851, 1), (key2922, 1), (key2778, 1), (key2868, 1), (key2784, 1), (key3021, 2), (key3022, 2), (key3011, 2), (key3021, -2), (key3025, -2), (key3007, -2)]

def rawRow15685 : Integer.Sparse Key := [(key2657, -1), (key2659, -1), (key2614, -1), (key2638, -1), (key2608, -1), (key2624, -1), (key2638, 2), (key2614, 2), (key2630, 2), (key2724, 1), (key2757, 1), (key2669, 1), (key2752, 1), (key2663, 1), (key2698, 1), (key2724, -2), (key2669, -2), (key2704, -2), (key2858, -1), (key2919, -1), (key2807, -1), (key2918, -1), (key2801, -1), (key2851, -1), (key2868, 1), (key2922, 1), (key2784, 1), (key2918, 1), (key2778, 1), (key2851, 1), (key3022, 2), (key3011, 2), (key3021, 2), (key3025, -2), (key3007, -2), (key3021, -2)]

def rawRow15686 : Integer.Sparse Key := [(key2659, -1), (key2657, -1), (key2638, -1), (key2614, -1), (key2624, -1), (key2608, -1), (key2638, 2), (key2630, 2), (key2614, 2), (key2757, 1), (key2724, 1), (key2752, 1), (key2669, 1), (key2698, 1), (key2663, 1), (key2724, -2), (key2704, -2), (key2669, -2), (key2919, -1), (key2858, -1), (key2918, -1), (key2807, -1), (key2851, -1), (key2801, -1), (key2922, 1), (key2868, 1), (key2918, 1), (key2784, 1), (key2851, 1), (key2778, 1), (key3022, 2), (key3021, 2), (key3011, 2), (key3025, -2), (key3021, -2), (key3007, -2)]

def rawRow15687 : Integer.Sparse Key := [(key2614, -1), (key2614, -1), (key2630, -1), (key2630, -1), (key2638, -1), (key2638, -1), (key2608, 2), (key2624, 2), (key2624, 2), (key2669, 1), (key2669, 1), (key2704, 1), (key2704, 1), (key2752, 1), (key2752, 1), (key2663, -2), (key2698, -2), (key2698, -2), (key2827, -1), (key2827, -1), (key2868, -1), (key2868, -1), (key2922, -1), (key2922, -1), (key2792, 1), (key2792, 1), (key2858, 1), (key2858, 1), (key2919, 1), (key2919, 1), (key3016, 2), (key3025, 2), (key3025, 2), (key3009, -2), (key3022, -2), (key3022, -2)]

def rawRow15688 : Integer.Sparse Key := [(key2630, -1), (key2638, -1), (key2614, -1), (key2638, -1), (key2614, -1), (key2630, -1), (key2624, 2), (key2608, 2), (key2624, 2), (key2704, 1), (key2752, 1), (key2669, 1), (key2752, 1), (key2669, 1), (key2704, 1), (key2698, -2), (key2663, -2), (key2698, -2), (key2868, -1), (key2922, -1), (key2827, -1), (key2922, -1), (key2827, -1), (key2868, -1), (key2858, 1), (key2919, 1), (key2792, 1), (key2919, 1), (key2792, 1), (key2858, 1), (key3025, 2), (key3016, 2), (key3025, 2), (key3022, -2), (key3009, -2), (key3022, -2)]

def rawRow15689 : Integer.Sparse Key := [(key2638, -1), (key2630, -1), (key2638, -1), (key2614, -1), (key2630, -1), (key2614, -1), (key2624, 2), (key2624, 2), (key2608, 2), (key2752, 1), (key2704, 1), (key2752, 1), (key2669, 1), (key2704, 1), (key2669, 1), (key2698, -2), (key2698, -2), (key2663, -2), (key2922, -1), (key2868, -1), (key2922, -1), (key2827, -1), (key2868, -1), (key2827, -1), (key2919, 1), (key2858, 1), (key2919, 1), (key2792, 1), (key2858, 1), (key2792, 1), (key3025, 2), (key3025, 2), (key3016, 2), (key3022, -2), (key3022, -2), (key3009, -2)]

def rawRow15690 : Integer.Sparse Key := [(key2663, -1), (key2669, -1), (key2698, -1), (key2752, -1), (key2724, -1), (key2757, -1), (key2669, 2), (key2704, 2), (key2752, 2), (key2608, 1), (key2614, 1), (key2801, 1), (key2827, 1), (key3011, 1), (key3016, 1), (key2614, -2), (key2807, -2), (key2827, -2), (key2698, -1), (key2704, -1), (key2851, -1), (key2858, -1), (key3021, -1), (key3022, -1), (key2624, 1), (key2630, 1), (key2851, 1), (key2868, 1), (key3021, 1), (key3025, 1), (key2752, 2), (key2918, 2), (key2919, 2), (key2657, -2), (key2918, -2), (key2922, -2)]

def rawRow15691 : Integer.Sparse Key := [(key2669, -1), (key2663, -1), (key2752, -1), (key2698, -1), (key2757, -1), (key2724, -1), (key2669, 2), (key2752, 2), (key2704, 2), (key2614, 1), (key2608, 1), (key2827, 1), (key2801, 1), (key3016, 1), (key3011, 1), (key2614, -2), (key2827, -2), (key2807, -2), (key2704, -1), (key2698, -1), (key2858, -1), (key2851, -1), (key3022, -1), (key3021, -1), (key2630, 1), (key2624, 1), (key2868, 1), (key2851, 1), (key3025, 1), (key3021, 1), (key2752, 2), (key2919, 2), (key2918, 2), (key2657, -2), (key2922, -2), (key2918, -2)]

def rawRow15692 : Integer.Sparse Key := [(key2698, -1), (key2724, -1), (key2663, -1), (key2757, -1), (key2669, -1), (key2752, -1), (key2704, 2), (key2669, 2), (key2752, 2), (key2801, 1), (key2827, 1), (key2608, 1), (key3016, 1), (key2614, 1), (key2827, 1), (key2807, -2), (key2614, -2), (key2827, -2), (key2851, -1), (key3021, -1), (key2698, -1), (key3022, -1), (key2704, -1), (key2858, -1), (key2851, 1), (key3021, 1), (key2624, 1), (key3025, 1), (key2630, 1), (key2868, 1), (key2918, 2), (key2752, 2), (key2919, 2), (key2918, -2), (key2657, -2), (key2922, -2)]

def rawRow15693 : Integer.Sparse Key := [(key2724, -1), (key2698, -1), (key2757, -1), (key2663, -1), (key2752, -1), (key2669, -1), (key2704, 2), (key2752, 2), (key2669, 2), (key2827, 1), (key2801, 1), (key3016, 1), (key2608, 1), (key2827, 1), (key2614, 1), (key2807, -2), (key2827, -2), (key2614, -2), (key3021, -1), (key2851, -1), (key3022, -1), (key2698, -1), (key2858, -1), (key2704, -1), (key3021, 1), (key2851, 1), (key3025, 1), (key2624, 1), (key2868, 1), (key2630, 1), (key2918, 2), (key2919, 2), (key2752, 2), (key2918, -2), (key2922, -2), (key2657, -2)]

def rawRow15694 : Integer.Sparse Key := [(key2752, -1), (key2757, -1), (key2669, -1), (key2724, -1), (key2663, -1), (key2698, -1), (key2752, 2), (key2669, 2), (key2704, 2), (key3011, 1), (key3016, 1), (key2614, 1), (key2827, 1), (key2608, 1), (key2801, 1), (key2827, -2), (key2614, -2), (key2807, -2), (key2858, -1), (key3022, -1), (key2704, -1), (key3021, -1), (key2698, -1), (key2851, -1), (key2868, 1), (key3025, 1), (key2630, 1), (key3021, 1), (key2624, 1), (key2851, 1), (key2919, 2), (key2752, 2), (key2918, 2), (key2922, -2), (key2657, -2), (key2918, -2)]

def rawRow15695 : Integer.Sparse Key := [(key2757, -1), (key2752, -1), (key2724, -1), (key2669, -1), (key2698, -1), (key2663, -1), (key2752, 2), (key2704, 2), (key2669, 2), (key3016, 1), (key3011, 1), (key2827, 1), (key2614, 1), (key2801, 1), (key2608, 1), (key2827, -2), (key2807, -2), (key2614, -2), (key3022, -1), (key2858, -1), (key3021, -1), (key2704, -1), (key2851, -1), (key2698, -1), (key3025, 1), (key2868, 1), (key3021, 1), (key2630, 1), (key2851, 1), (key2624, 1), (key2919, 2), (key2918, 2), (key2752, 2), (key2922, -2), (key2918, -2), (key2657, -2)]

def rawRow15696 : Integer.Sparse Key := [(key2669, -1), (key2669, -1), (key2704, -1), (key2704, -1), (key2724, -1), (key2724, -1), (key2663, 2), (key2698, 2), (key2698, 2), (key2614, 1), (key2614, 1), (key2807, 1), (key2807, 1), (key2827, 1), (key2827, 1), (key2608, -2), (key2801, -2), (key2801, -2), (key2724, -1), (key2724, -1), (key2868, -1), (key2868, -1), (key3025, -1), (key3025, -1), (key2638, 1), (key2638, 1), (key2858, 1), (key2858, 1), (key3022, 1), (key3022, 1), (key2757, 2), (key2922, 2), (key2922, 2), (key2659, -2), (key2919, -2), (key2919, -2)]

def rawRow15697 : Integer.Sparse Key := [(key2704, -1), (key2724, -1), (key2669, -1), (key2724, -1), (key2669, -1), (key2704, -1), (key2698, 2), (key2663, 2), (key2698, 2), (key2807, 1), (key2827, 1), (key2614, 1), (key2827, 1), (key2614, 1), (key2807, 1), (key2801, -2), (key2608, -2), (key2801, -2), (key2868, -1), (key3025, -1), (key2724, -1), (key3025, -1), (key2724, -1), (key2868, -1), (key2858, 1), (key3022, 1), (key2638, 1), (key3022, 1), (key2638, 1), (key2858, 1), (key2922, 2), (key2757, 2), (key2922, 2), (key2919, -2), (key2659, -2), (key2919, -2)]

def rawRow15698 : Integer.Sparse Key := [(key2724, -1), (key2704, -1), (key2724, -1), (key2669, -1), (key2704, -1), (key2669, -1), (key2698, 2), (key2698, 2), (key2663, 2), (key2827, 1), (key2807, 1), (key2827, 1), (key2614, 1), (key2807, 1), (key2614, 1), (key2801, -2), (key2801, -2), (key2608, -2), (key3025, -1), (key2868, -1), (key3025, -1), (key2724, -1), (key2868, -1), (key2724, -1), (key3022, 1), (key2858, 1), (key3022, 1), (key2638, 1), (key2858, 1), (key2638, 1), (key2922, 2), (key2922, 2), (key2757, 2), (key2919, -2), (key2919, -2), (key2659, -2)]

def rawRow15699 : Integer.Sparse Key := [(key2801, -1), (key2807, -1), (key2851, -1), (key2918, -1), (key2858, -1), (key2919, -1), (key2827, 2), (key2868, 2), (key2922, 2), (key2698, 1), (key2704, 1), (key2851, 1), (key3021, 1), (key2858, 1), (key3022, 1), (key2724, -2), (key2868, -2), (key3025, -2), (key2608, -1), (key2614, -1), (key2624, -1), (key2638, -1), (key2657, -1), (key2659, -1), (key2663, 1), (key2669, 1), (key2698, 1), (key2724, 1), (key2752, 1), (key2757, 1), (key2614, 2), (key2630, 2), (key2638, 2), (key2669, -2), (key2704, -2), (key2724, -2)]

def rawRow15700 : Integer.Sparse Key := [(key2807, -1), (key2801, -1), (key2918, -1), (key2851, -1), (key2919, -1), (key2858, -1), (key2827, 2), (key2922, 2), (key2868, 2), (key2704, 1), (key2698, 1), (key3021, 1), (key2851, 1), (key3022, 1), (key2858, 1), (key2724, -2), (key3025, -2), (key2868, -2), (key2614, -1), (key2608, -1), (key2638, -1), (key2624, -1), (key2659, -1), (key2657, -1), (key2669, 1), (key2663, 1), (key2724, 1), (key2698, 1), (key2757, 1), (key2752, 1), (key2614, 2), (key2638, 2), (key2630, 2), (key2669, -2), (key2724, -2), (key2704, -2)]

def rawRow15701 : Integer.Sparse Key := [(key2851, -1), (key2858, -1), (key2801, -1), (key2919, -1), (key2807, -1), (key2918, -1), (key2868, 2), (key2827, 2), (key2922, 2), (key2851, 1), (key2858, 1), (key2698, 1), (key3022, 1), (key2704, 1), (key3021, 1), (key2868, -2), (key2724, -2), (key3025, -2), (key2624, -1), (key2638, -1), (key2608, -1), (key2659, -1), (key2614, -1), (key2638, -1), (key2698, 1), (key2752, 1), (key2663, 1), (key2757, 1), (key2669, 1), (key2724, 1), (key2630, 2), (key2614, 2), (key2638, 2), (key2704, -2), (key2669, -2), (key2724, -2)]

def rawRow15702 : Integer.Sparse Key := [(key2858, -1), (key2851, -1), (key2919, -1), (key2801, -1), (key2918, -1), (key2807, -1), (key2868, 2), (key2922, 2), (key2827, 2), (key2858, 1), (key2851, 1), (key3022, 1), (key2698, 1), (key3021, 1), (key2704, 1), (key2868, -2), (key3025, -2), (key2724, -2), (key2638, -1), (key2624, -1), (key2659, -1), (key2608, -1), (key2638, -1), (key2614, -1), (key2752, 1), (key2698, 1), (key2757, 1), (key2663, 1), (key2724, 1), (key2669, 1), (key2630, 2), (key2638, 2), (key2614, 2), (key2704, -2), (key2724, -2), (key2669, -2)]

def rawRow15703 : Integer.Sparse Key := [(key2918, -1), (key2919, -1), (key2807, -1), (key2858, -1), (key2801, -1), (key2851, -1), (key2922, 2), (key2827, 2), (key2868, 2), (key3021, 1), (key3022, 1), (key2704, 1), (key2858, 1), (key2698, 1), (key2851, 1), (key3025, -2), (key2724, -2), (key2868, -2), (key2657, -1), (key2659, -1), (key2614, -1), (key2638, -1), (key2608, -1), (key2624, -1), (key2724, 1), (key2757, 1), (key2669, 1), (key2752, 1), (key2663, 1), (key2698, 1), (key2638, 2), (key2614, 2), (key2630, 2), (key2724, -2), (key2669, -2), (key2704, -2)]

def rawRow15704 : Integer.Sparse Key := [(key2919, -1), (key2918, -1), (key2858, -1), (key2807, -1), (key2851, -1), (key2801, -1), (key2922, 2), (key2868, 2), (key2827, 2), (key3022, 1), (key3021, 1), (key2858, 1), (key2704, 1), (key2851, 1), (key2698, 1), (key3025, -2), (key2868, -2), (key2724, -2), (key2659, -1), (key2657, -1), (key2638, -1), (key2614, -1), (key2624, -1), (key2608, -1), (key2757, 1), (key2724, 1), (key2752, 1), (key2669, 1), (key2698, 1), (key2663, 1), (key2638, 2), (key2630, 2), (key2614, 2), (key2724, -2), (key2704, -2), (key2669, -2)]

def rawRow15705 : Integer.Sparse Key := [(key2778, -1), (key2784, -1), (key2851, -1), (key2918, -1), (key2868, -1), (key2922, -1), (key2792, 2), (key2858, 2), (key2919, 2), (key2624, 1), (key2630, 1), (key2851, 1), (key3021, 1), (key2868, 1), (key3025, 1), (key2638, -2), (key2858, -2), (key3022, -2), (key2663, -1), (key2669, -1), (key2698, -1), (key2752, -1), (key2724, -1), (key2757, -1), (key2608, 1), (key2614, 1), (key2801, 1), (key2827, 1), (key3011, 1), (key3016, 1), (key2669, 2), (key2784, 2), (key2792, 2), (key2614, -2), (key2807, -2), (key2827, -2)]

def rawRow15706 : Integer.Sparse Key := [(key2784, -1), (key2778, -1), (key2918, -1), (key2851, -1), (key2922, -1), (key2868, -1), (key2792, 2), (key2919, 2), (key2858, 2), (key2630, 1), (key2624, 1), (key3021, 1), (key2851, 1), (key3025, 1), (key2868, 1), (key2638, -2), (key3022, -2), (key2858, -2), (key2669, -1), (key2663, -1), (key2752, -1), (key2698, -1), (key2757, -1), (key2724, -1), (key2614, 1), (key2608, 1), (key2827, 1), (key2801, 1), (key3016, 1), (key3011, 1), (key2669, 2), (key2792, 2), (key2784, 2), (key2614, -2), (key2827, -2), (key2807, -2)]

def rawRow15707 : Integer.Sparse Key := [(key2851, -1), (key2868, -1), (key2778, -1), (key2922, -1), (key2784, -1), (key2918, -1), (key2858, 2), (key2792, 2), (key2919, 2), (key2851, 1), (key2868, 1), (key2624, 1), (key3025, 1), (key2630, 1), (key3021, 1), (key2858, -2), (key2638, -2), (key3022, -2), (key2698, -1), (key2724, -1), (key2663, -1), (key2757, -1), (key2669, -1), (key2752, -1), (key2801, 1), (key2827, 1), (key2608, 1), (key3016, 1), (key2614, 1), (key2827, 1), (key2784, 2), (key2669, 2), (key2792, 2), (key2807, -2), (key2614, -2), (key2827, -2)]

def rawRow15708 : Integer.Sparse Key := [(key2868, -1), (key2851, -1), (key2922, -1), (key2778, -1), (key2918, -1), (key2784, -1), (key2858, 2), (key2919, 2), (key2792, 2), (key2868, 1), (key2851, 1), (key3025, 1), (key2624, 1), (key3021, 1), (key2630, 1), (key2858, -2), (key3022, -2), (key2638, -2), (key2724, -1), (key2698, -1), (key2757, -1), (key2663, -1), (key2752, -1), (key2669, -1), (key2827, 1), (key2801, 1), (key3016, 1), (key2608, 1), (key2827, 1), (key2614, 1), (key2784, 2), (key2792, 2), (key2669, 2), (key2807, -2), (key2827, -2), (key2614, -2)]

def rawRow15709 : Integer.Sparse Key := [(key2918, -1), (key2922, -1), (key2784, -1), (key2868, -1), (key2778, -1), (key2851, -1), (key2919, 2), (key2792, 2), (key2858, 2), (key3021, 1), (key3025, 1), (key2630, 1), (key2868, 1), (key2624, 1), (key2851, 1), (key3022, -2), (key2638, -2), (key2858, -2), (key2752, -1), (key2757, -1), (key2669, -1), (key2724, -1), (key2663, -1), (key2698, -1), (key3011, 1), (key3016, 1), (key2614, 1), (key2827, 1), (key2608, 1), (key2801, 1), (key2792, 2), (key2669, 2), (key2784, 2), (key2827, -2), (key2614, -2), (key2807, -2)]

def rawRow15710 : Integer.Sparse Key := [(key2922, -1), (key2918, -1), (key2868, -1), (key2784, -1), (key2851, -1), (key2778, -1), (key2919, 2), (key2858, 2), (key2792, 2), (key3025, 1), (key3021, 1), (key2868, 1), (key2630, 1), (key2851, 1), (key2624, 1), (key3022, -2), (key2858, -2), (key2638, -2), (key2757, -1), (key2752, -1), (key2724, -1), (key2669, -1), (key2698, -1), (key2663, -1), (key3016, 1), (key3011, 1), (key2827, 1), (key2614, 1), (key2801, 1), (key2608, 1), (key2792, 2), (key2784, 2), (key2669, 2), (key2827, -2), (key2807, -2), (key2614, -2)]

def rawRow15711 : Integer.Sparse Key := [(key3011, -1), (key3011, -1), (key3021, -1), (key3021, -1), (key3022, -1), (key3022, -1), (key3016, 2), (key3025, 2), (key3025, 2), (key2752, 1), (key2752, 1), (key2918, 1), (key2918, 1), (key2919, 1), (key2919, 1), (key2757, -2), (key2922, -2), (key2922, -2), (key2614, -1), (key2614, -1), (key2630, -1), (key2630, -1), (key2638, -1), (key2638, -1), (key2669, 1), (key2669, 1), (key2784, 1), (key2784, 1), (key2792, 1), (key2792, 1), (key2608, 2), (key2624, 2), (key2624, 2), (key2663, -2), (key2698, -2), (key2698, -2)]

def rawRow15712 : Integer.Sparse Key := [(key3021, -1), (key3022, -1), (key3011, -1), (key3022, -1), (key3011, -1), (key3021, -1), (key3025, 2), (key3016, 2), (key3025, 2), (key2918, 1), (key2919, 1), (key2752, 1), (key2919, 1), (key2752, 1), (key2918, 1), (key2922, -2), (key2757, -2), (key2922, -2), (key2630, -1), (key2638, -1), (key2614, -1), (key2638, -1), (key2614, -1), (key2630, -1), (key2784, 1), (key2792, 1), (key2669, 1), (key2792, 1), (key2669, 1), (key2784, 1), (key2624, 2), (key2608, 2), (key2624, 2), (key2698, -2), (key2663, -2), (key2698, -2)]

def rawRow15713 : Integer.Sparse Key := [(key3022, -1), (key3021, -1), (key3022, -1), (key3011, -1), (key3021, -1), (key3011, -1), (key3025, 2), (key3025, 2), (key3016, 2), (key2919, 1), (key2918, 1), (key2919, 1), (key2752, 1), (key2918, 1), (key2752, 1), (key2922, -2), (key2922, -2), (key2757, -2), (key2638, -1), (key2630, -1), (key2638, -1), (key2614, -1), (key2630, -1), (key2614, -1), (key2792, 1), (key2784, 1), (key2792, 1), (key2669, 1), (key2784, 1), (key2669, 1), (key2624, 2), (key2624, 2), (key2608, 2), (key2698, -2), (key2698, -2), (key2663, -2)]

def rawRow15714 : Integer.Sparse Key := [(key3007, -1), (key3007, -1), (key3021, -1), (key3021, -1), (key3025, -1), (key3025, -1), (key3009, 2), (key3022, 2), (key3022, 2), (key2657, 1), (key2657, 1), (key2918, 1), (key2918, 1), (key2922, 1), (key2922, 1), (key2659, -2), (key2919, -2), (key2919, -2), (key2669, -1), (key2669, -1), (key2704, -1), (key2704, -1), (key2724, -1), (key2724, -1), (key2614, 1), (key2614, 1), (key2807, 1), (key2807, 1), (key2827, 1), (key2827, 1), (key2663, 2), (key2698, 2), (key2698, 2), (key2608, -2), (key2801, -2), (key2801, -2)]

def rawRow15715 : Integer.Sparse Key := [(key3021, -1), (key3025, -1), (key3007, -1), (key3025, -1), (key3007, -1), (key3021, -1), (key3022, 2), (key3009, 2), (key3022, 2), (key2918, 1), (key2922, 1), (key2657, 1), (key2922, 1), (key2657, 1), (key2918, 1), (key2919, -2), (key2659, -2), (key2919, -2), (key2704, -1), (key2724, -1), (key2669, -1), (key2724, -1), (key2669, -1), (key2704, -1), (key2807, 1), (key2827, 1), (key2614, 1), (key2827, 1), (key2614, 1), (key2807, 1), (key2698, 2), (key2663, 2), (key2698, 2), (key2801, -2), (key2608, -2), (key2801, -2)]

def rawRow15716 : Integer.Sparse Key := [(key3025, -1), (key3021, -1), (key3025, -1), (key3007, -1), (key3021, -1), (key3007, -1), (key3022, 2), (key3022, 2), (key3009, 2), (key2922, 1), (key2918, 1), (key2922, 1), (key2657, 1), (key2918, 1), (key2657, 1), (key2919, -2), (key2919, -2), (key2659, -2), (key2724, -1), (key2704, -1), (key2724, -1), (key2669, -1), (key2704, -1), (key2669, -1), (key2827, 1), (key2807, 1), (key2827, 1), (key2614, 1), (key2807, 1), (key2614, 1), (key2698, 2), (key2698, 2), (key2663, 2), (key2801, -2), (key2801, -2), (key2608, -2)]

def rawRow15717 : Integer.Sparse Key := [(key2406, 4), (key2480, 4), (key2543, 4), (key2406, -2), (key2409, -2), (key2472, -2), (key2538, -2), (key2482, -2), (key2543, -2), (key2437, -2), (key2440, -2), (key2503, -2), (key2554, -2), (key2522, -2), (key2563, -2), (key2440, 4), (key2506, 4), (key2554, 4)]

def rawRow15718 : Integer.Sparse Key := [(key2406, 4), (key2543, 4), (key2480, 4), (key2409, -2), (key2406, -2), (key2538, -2), (key2472, -2), (key2543, -2), (key2482, -2), (key2440, -2), (key2437, -2), (key2554, -2), (key2503, -2), (key2563, -2), (key2522, -2), (key2440, 4), (key2554, 4), (key2506, 4)]

def rawRow15719 : Integer.Sparse Key := [(key2480, 4), (key2406, 4), (key2543, 4), (key2472, -2), (key2482, -2), (key2406, -2), (key2543, -2), (key2409, -2), (key2538, -2), (key2503, -2), (key2522, -2), (key2437, -2), (key2563, -2), (key2440, -2), (key2554, -2), (key2506, 4), (key2440, 4), (key2554, 4)]

def rawRow15720 : Integer.Sparse Key := [(key2480, 4), (key2543, 4), (key2406, 4), (key2482, -2), (key2472, -2), (key2543, -2), (key2406, -2), (key2538, -2), (key2409, -2), (key2522, -2), (key2503, -2), (key2563, -2), (key2437, -2), (key2554, -2), (key2440, -2), (key2506, 4), (key2554, 4), (key2440, 4)]

def rawRow15721 : Integer.Sparse Key := [(key2543, 4), (key2406, 4), (key2480, 4), (key2538, -2), (key2543, -2), (key2409, -2), (key2482, -2), (key2406, -2), (key2472, -2), (key2554, -2), (key2563, -2), (key2440, -2), (key2522, -2), (key2437, -2), (key2503, -2), (key2554, 4), (key2440, 4), (key2506, 4)]

def rawRow15722 : Integer.Sparse Key := [(key2543, 4), (key2480, 4), (key2406, 4), (key2543, -2), (key2538, -2), (key2482, -2), (key2409, -2), (key2472, -2), (key2406, -2), (key2563, -2), (key2554, -2), (key2522, -2), (key2440, -2), (key2503, -2), (key2437, -2), (key2554, 4), (key2506, 4), (key2440, 4)]

def rawRow15723 : Integer.Sparse Key := [(key2409, 4), (key2482, 4), (key2482, 4), (key2406, -2), (key2406, -2), (key2472, -2), (key2472, -2), (key2480, -2), (key2480, -2), (key2440, -2), (key2440, -2), (key2506, -2), (key2506, -2), (key2522, -2), (key2522, -2), (key2437, 4), (key2503, 4), (key2503, 4)]

def rawRow15724 : Integer.Sparse Key := [(key2482, 4), (key2409, 4), (key2482, 4), (key2472, -2), (key2480, -2), (key2406, -2), (key2480, -2), (key2406, -2), (key2472, -2), (key2506, -2), (key2522, -2), (key2440, -2), (key2522, -2), (key2440, -2), (key2506, -2), (key2503, 4), (key2437, 4), (key2503, 4)]

def rawRow15725 : Integer.Sparse Key := [(key2482, 4), (key2482, 4), (key2409, 4), (key2480, -2), (key2472, -2), (key2480, -2), (key2406, -2), (key2472, -2), (key2406, -2), (key2522, -2), (key2506, -2), (key2522, -2), (key2440, -2), (key2506, -2), (key2440, -2), (key2503, 4), (key2503, 4), (key2437, 4)]

def rawRow15726 : Integer.Sparse Key := [(key2406, 4), (key2480, 4), (key2543, 4), (key2437, -2), (key2440, -2), (key2503, -2), (key2554, -2), (key2522, -2), (key2563, -2), (key2406, -2), (key2409, -2), (key2472, -2), (key2538, -2), (key2482, -2), (key2543, -2), (key2440, 4), (key2506, 4), (key2554, 4)]

def rawRow15727 : Integer.Sparse Key := [(key2406, 4), (key2543, 4), (key2480, 4), (key2440, -2), (key2437, -2), (key2554, -2), (key2503, -2), (key2563, -2), (key2522, -2), (key2409, -2), (key2406, -2), (key2538, -2), (key2472, -2), (key2543, -2), (key2482, -2), (key2440, 4), (key2554, 4), (key2506, 4)]

def rawRow15728 : Integer.Sparse Key := [(key2480, 4), (key2406, 4), (key2543, 4), (key2503, -2), (key2522, -2), (key2437, -2), (key2563, -2), (key2440, -2), (key2554, -2), (key2472, -2), (key2482, -2), (key2406, -2), (key2543, -2), (key2409, -2), (key2538, -2), (key2506, 4), (key2440, 4), (key2554, 4)]

def rawRow15729 : Integer.Sparse Key := [(key2480, 4), (key2543, 4), (key2406, 4), (key2522, -2), (key2503, -2), (key2563, -2), (key2437, -2), (key2554, -2), (key2440, -2), (key2482, -2), (key2472, -2), (key2543, -2), (key2406, -2), (key2538, -2), (key2409, -2), (key2506, 4), (key2554, 4), (key2440, 4)]

def rawRow15730 : Integer.Sparse Key := [(key2543, 4), (key2406, 4), (key2480, 4), (key2554, -2), (key2563, -2), (key2440, -2), (key2522, -2), (key2437, -2), (key2503, -2), (key2538, -2), (key2543, -2), (key2409, -2), (key2482, -2), (key2406, -2), (key2472, -2), (key2554, 4), (key2440, 4), (key2506, 4)]

def rawRow15731 : Integer.Sparse Key := [(key2543, 4), (key2480, 4), (key2406, 4), (key2563, -2), (key2554, -2), (key2522, -2), (key2440, -2), (key2503, -2), (key2437, -2), (key2543, -2), (key2538, -2), (key2482, -2), (key2409, -2), (key2472, -2), (key2406, -2), (key2554, 4), (key2506, 4), (key2440, 4)]

def rawRow15732 : Integer.Sparse Key := [(key2409, 4), (key2482, 4), (key2482, 4), (key2440, -2), (key2440, -2), (key2506, -2), (key2506, -2), (key2522, -2), (key2522, -2), (key2406, -2), (key2406, -2), (key2472, -2), (key2472, -2), (key2480, -2), (key2480, -2), (key2437, 4), (key2503, 4), (key2503, 4)]

def rawRow15733 : Integer.Sparse Key := [(key2482, 4), (key2409, 4), (key2482, 4), (key2506, -2), (key2522, -2), (key2440, -2), (key2522, -2), (key2440, -2), (key2506, -2), (key2472, -2), (key2480, -2), (key2406, -2), (key2480, -2), (key2406, -2), (key2472, -2), (key2503, 4), (key2437, 4), (key2503, 4)]

def rawRow15734 : Integer.Sparse Key := [(key2482, 4), (key2482, 4), (key2409, 4), (key2522, -2), (key2506, -2), (key2522, -2), (key2440, -2), (key2506, -2), (key2440, -2), (key2480, -2), (key2472, -2), (key2480, -2), (key2406, -2), (key2472, -2), (key2406, -2), (key2503, 4), (key2503, 4), (key2437, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block147
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow15825 : Integer.Sparse Key := [(key2664, -1), (key2668, -1), (key2779, -1), (key2937, -1), (key2791, -1), (key2942, -1), (key2668, 2), (key2783, 2), (key2937, 2), (key2699, -1), (key2703, -1), (key2852, -1), (key2973, -1), (key2857, -1), (key2975, -1), (key2699, 2), (key2736, 2), (key2802, 2), (key2949, 2), (key2896, 2), (key2975, 2), (key2703, -1), (key2736, -1), (key2806, -1), (key2949, -1), (key2894, -1), (key2973, -1), (key2723, 2), (key2867, 2), (key2982, 2), (key2723, -1), (key2746, -1), (key2826, -1), (key2959, -1), (key2903, -1), (key2982, -1)]

def rawRow15826 : Integer.Sparse Key := [(key2668, -1), (key2664, -1), (key2937, -1), (key2779, -1), (key2942, -1), (key2791, -1), (key2668, 2), (key2937, 2), (key2783, 2), (key2703, -1), (key2699, -1), (key2973, -1), (key2852, -1), (key2975, -1), (key2857, -1), (key2736, 2), (key2699, 2), (key2949, 2), (key2802, 2), (key2975, 2), (key2896, 2), (key2736, -1), (key2703, -1), (key2949, -1), (key2806, -1), (key2973, -1), (key2894, -1), (key2723, 2), (key2982, 2), (key2867, 2), (key2746, -1), (key2723, -1), (key2959, -1), (key2826, -1), (key2982, -1), (key2903, -1)]

def rawRow15827 : Integer.Sparse Key := [(key2779, -1), (key2791, -1), (key2664, -1), (key2942, -1), (key2668, -1), (key2937, -1), (key2783, 2), (key2668, 2), (key2937, 2), (key2852, -1), (key2857, -1), (key2699, -1), (key2975, -1), (key2703, -1), (key2973, -1), (key2802, 2), (key2896, 2), (key2699, 2), (key2975, 2), (key2736, 2), (key2949, 2), (key2806, -1), (key2894, -1), (key2703, -1), (key2973, -1), (key2736, -1), (key2949, -1), (key2867, 2), (key2723, 2), (key2982, 2), (key2826, -1), (key2903, -1), (key2723, -1), (key2982, -1), (key2746, -1), (key2959, -1)]

def rawRow15828 : Integer.Sparse Key := [(key2791, -1), (key2779, -1), (key2942, -1), (key2664, -1), (key2937, -1), (key2668, -1), (key2783, 2), (key2937, 2), (key2668, 2), (key2857, -1), (key2852, -1), (key2975, -1), (key2699, -1), (key2973, -1), (key2703, -1), (key2896, 2), (key2802, 2), (key2975, 2), (key2699, 2), (key2949, 2), (key2736, 2), (key2894, -1), (key2806, -1), (key2973, -1), (key2703, -1), (key2949, -1), (key2736, -1), (key2867, 2), (key2982, 2), (key2723, 2), (key2903, -1), (key2826, -1), (key2982, -1), (key2723, -1), (key2959, -1), (key2746, -1)]

def rawRow15829 : Integer.Sparse Key := [(key2937, -1), (key2942, -1), (key2668, -1), (key2791, -1), (key2664, -1), (key2779, -1), (key2937, 2), (key2668, 2), (key2783, 2), (key2973, -1), (key2975, -1), (key2703, -1), (key2857, -1), (key2699, -1), (key2852, -1), (key2949, 2), (key2975, 2), (key2736, 2), (key2896, 2), (key2699, 2), (key2802, 2), (key2949, -1), (key2973, -1), (key2736, -1), (key2894, -1), (key2703, -1), (key2806, -1), (key2982, 2), (key2723, 2), (key2867, 2), (key2959, -1), (key2982, -1), (key2746, -1), (key2903, -1), (key2723, -1), (key2826, -1)]

def rawRow15830 : Integer.Sparse Key := [(key2942, -1), (key2937, -1), (key2791, -1), (key2668, -1), (key2779, -1), (key2664, -1), (key2937, 2), (key2783, 2), (key2668, 2), (key2975, -1), (key2973, -1), (key2857, -1), (key2703, -1), (key2852, -1), (key2699, -1), (key2975, 2), (key2949, 2), (key2896, 2), (key2736, 2), (key2802, 2), (key2699, 2), (key2973, -1), (key2949, -1), (key2894, -1), (key2736, -1), (key2806, -1), (key2703, -1), (key2982, 2), (key2867, 2), (key2723, 2), (key2982, -1), (key2959, -1), (key2903, -1), (key2746, -1), (key2826, -1), (key2723, -1)]

def rawRow15831 : Integer.Sparse Key := [(key2668, -1), (key2668, -1), (key2783, -1), (key2783, -1), (key2791, -1), (key2791, -1), (key2664, 2), (key2779, 2), (key2779, 2), (key2736, -1), (key2736, -1), (key2894, -1), (key2894, -1), (key2896, -1), (key2896, -1), (key2703, 2), (key2703, 2), (key2806, 2), (key2806, 2), (key2857, 2), (key2857, 2), (key2699, -1), (key2699, -1), (key2802, -1), (key2802, -1), (key2852, -1), (key2852, -1), (key2746, 2), (key2903, 2), (key2903, 2), (key2723, -1), (key2723, -1), (key2826, -1), (key2826, -1), (key2867, -1), (key2867, -1)]

def rawRow15832 : Integer.Sparse Key := [(key2783, -1), (key2791, -1), (key2668, -1), (key2791, -1), (key2668, -1), (key2783, -1), (key2779, 2), (key2664, 2), (key2779, 2), (key2894, -1), (key2896, -1), (key2736, -1), (key2896, -1), (key2736, -1), (key2894, -1), (key2806, 2), (key2857, 2), (key2703, 2), (key2857, 2), (key2703, 2), (key2806, 2), (key2802, -1), (key2852, -1), (key2699, -1), (key2852, -1), (key2699, -1), (key2802, -1), (key2903, 2), (key2746, 2), (key2903, 2), (key2826, -1), (key2867, -1), (key2723, -1), (key2867, -1), (key2723, -1), (key2826, -1)]

def rawRow15833 : Integer.Sparse Key := [(key2791, -1), (key2783, -1), (key2791, -1), (key2668, -1), (key2783, -1), (key2668, -1), (key2779, 2), (key2779, 2), (key2664, 2), (key2896, -1), (key2894, -1), (key2896, -1), (key2736, -1), (key2894, -1), (key2736, -1), (key2857, 2), (key2806, 2), (key2857, 2), (key2703, 2), (key2806, 2), (key2703, 2), (key2852, -1), (key2802, -1), (key2852, -1), (key2699, -1), (key2802, -1), (key2699, -1), (key2903, 2), (key2903, 2), (key2746, 2), (key2867, -1), (key2826, -1), (key2867, -1), (key2723, -1), (key2826, -1), (key2723, -1)]

def rawRow15834 : Integer.Sparse Key := [(key2699, -1), (key2703, -1), (key2852, -1), (key2973, -1), (key2857, -1), (key2975, -1), (key2723, 2), (key2867, 2), (key2982, 2), (key2664, -1), (key2668, -1), (key2779, -1), (key2937, -1), (key2791, -1), (key2942, -1), (key2699, 2), (key2736, 2), (key2802, 2), (key2949, 2), (key2896, 2), (key2975, 2), (key2723, -1), (key2746, -1), (key2826, -1), (key2959, -1), (key2903, -1), (key2982, -1), (key2668, 2), (key2783, 2), (key2937, 2), (key2703, -1), (key2736, -1), (key2806, -1), (key2949, -1), (key2894, -1), (key2973, -1)]

def rawRow15835 : Integer.Sparse Key := [(key2703, -1), (key2699, -1), (key2973, -1), (key2852, -1), (key2975, -1), (key2857, -1), (key2723, 2), (key2982, 2), (key2867, 2), (key2668, -1), (key2664, -1), (key2937, -1), (key2779, -1), (key2942, -1), (key2791, -1), (key2736, 2), (key2699, 2), (key2949, 2), (key2802, 2), (key2975, 2), (key2896, 2), (key2746, -1), (key2723, -1), (key2959, -1), (key2826, -1), (key2982, -1), (key2903, -1), (key2668, 2), (key2937, 2), (key2783, 2), (key2736, -1), (key2703, -1), (key2949, -1), (key2806, -1), (key2973, -1), (key2894, -1)]

def rawRow15836 : Integer.Sparse Key := [(key2852, -1), (key2857, -1), (key2699, -1), (key2975, -1), (key2703, -1), (key2973, -1), (key2867, 2), (key2723, 2), (key2982, 2), (key2779, -1), (key2791, -1), (key2664, -1), (key2942, -1), (key2668, -1), (key2937, -1), (key2802, 2), (key2896, 2), (key2699, 2), (key2975, 2), (key2736, 2), (key2949, 2), (key2826, -1), (key2903, -1), (key2723, -1), (key2982, -1), (key2746, -1), (key2959, -1), (key2783, 2), (key2668, 2), (key2937, 2), (key2806, -1), (key2894, -1), (key2703, -1), (key2973, -1), (key2736, -1), (key2949, -1)]

def rawRow15837 : Integer.Sparse Key := [(key2857, -1), (key2852, -1), (key2975, -1), (key2699, -1), (key2973, -1), (key2703, -1), (key2867, 2), (key2982, 2), (key2723, 2), (key2791, -1), (key2779, -1), (key2942, -1), (key2664, -1), (key2937, -1), (key2668, -1), (key2896, 2), (key2802, 2), (key2975, 2), (key2699, 2), (key2949, 2), (key2736, 2), (key2903, -1), (key2826, -1), (key2982, -1), (key2723, -1), (key2959, -1), (key2746, -1), (key2783, 2), (key2937, 2), (key2668, 2), (key2894, -1), (key2806, -1), (key2973, -1), (key2703, -1), (key2949, -1), (key2736, -1)]

def rawRow15838 : Integer.Sparse Key := [(key2973, -1), (key2975, -1), (key2703, -1), (key2857, -1), (key2699, -1), (key2852, -1), (key2982, 2), (key2723, 2), (key2867, 2), (key2937, -1), (key2942, -1), (key2668, -1), (key2791, -1), (key2664, -1), (key2779, -1), (key2949, 2), (key2975, 2), (key2736, 2), (key2896, 2), (key2699, 2), (key2802, 2), (key2959, -1), (key2982, -1), (key2746, -1), (key2903, -1), (key2723, -1), (key2826, -1), (key2937, 2), (key2668, 2), (key2783, 2), (key2949, -1), (key2973, -1), (key2736, -1), (key2894, -1), (key2703, -1), (key2806, -1)]

def rawRow15839 : Integer.Sparse Key := [(key2975, -1), (key2973, -1), (key2857, -1), (key2703, -1), (key2852, -1), (key2699, -1), (key2982, 2), (key2867, 2), (key2723, 2), (key2942, -1), (key2937, -1), (key2791, -1), (key2668, -1), (key2779, -1), (key2664, -1), (key2975, 2), (key2949, 2), (key2896, 2), (key2736, 2), (key2802, 2), (key2699, 2), (key2982, -1), (key2959, -1), (key2903, -1), (key2746, -1), (key2826, -1), (key2723, -1), (key2937, 2), (key2783, 2), (key2668, 2), (key2973, -1), (key2949, -1), (key2894, -1), (key2736, -1), (key2806, -1), (key2703, -1)]

def rawRow15840 : Integer.Sparse Key := [(key2736, -1), (key2736, -1), (key2894, -1), (key2894, -1), (key2896, -1), (key2896, -1), (key2746, 2), (key2903, 2), (key2903, 2), (key2668, -1), (key2668, -1), (key2783, -1), (key2783, -1), (key2791, -1), (key2791, -1), (key2703, 2), (key2703, 2), (key2806, 2), (key2806, 2), (key2857, 2), (key2857, 2), (key2723, -1), (key2723, -1), (key2826, -1), (key2826, -1), (key2867, -1), (key2867, -1), (key2664, 2), (key2779, 2), (key2779, 2), (key2699, -1), (key2699, -1), (key2802, -1), (key2802, -1), (key2852, -1), (key2852, -1)]

def rawRow15841 : Integer.Sparse Key := [(key2894, -1), (key2896, -1), (key2736, -1), (key2896, -1), (key2736, -1), (key2894, -1), (key2903, 2), (key2746, 2), (key2903, 2), (key2783, -1), (key2791, -1), (key2668, -1), (key2791, -1), (key2668, -1), (key2783, -1), (key2806, 2), (key2857, 2), (key2703, 2), (key2857, 2), (key2703, 2), (key2806, 2), (key2826, -1), (key2867, -1), (key2723, -1), (key2867, -1), (key2723, -1), (key2826, -1), (key2779, 2), (key2664, 2), (key2779, 2), (key2802, -1), (key2852, -1), (key2699, -1), (key2852, -1), (key2699, -1), (key2802, -1)]

def rawRow15842 : Integer.Sparse Key := [(key2896, -1), (key2894, -1), (key2896, -1), (key2736, -1), (key2894, -1), (key2736, -1), (key2903, 2), (key2903, 2), (key2746, 2), (key2791, -1), (key2783, -1), (key2791, -1), (key2668, -1), (key2783, -1), (key2668, -1), (key2857, 2), (key2806, 2), (key2857, 2), (key2703, 2), (key2806, 2), (key2703, 2), (key2867, -1), (key2826, -1), (key2867, -1), (key2723, -1), (key2826, -1), (key2723, -1), (key2779, 2), (key2779, 2), (key2664, 2), (key2852, -1), (key2802, -1), (key2852, -1), (key2699, -1), (key2802, -1), (key2699, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block148
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow15897 : Integer.Sparse Key := [(key2663, -1), (key2666, -1), (key2698, -1), (key2722, -1), (key2734, -1), (key2745, -1), (key2666, 2), (key2701, 2), (key2722, 2), (key2778, -1), (key2781, -1), (key2851, -1), (key2866, -1), (key2892, -1), (key2902, -1), (key2778, 2), (key2790, 2), (key2801, 2), (key2825, 2), (key2895, 2), (key2902, 2), (key2781, -1), (key2790, -1), (key2804, -1), (key2825, -1), (key2856, -1), (key2866, -1), (key2935, 2), (key2971, 2), (key2981, 2), (key2935, -1), (key2941, -1), (key2947, -1), (key2958, -1), (key2974, -1), (key2981, -1)]

def rawRow15898 : Integer.Sparse Key := [(key2666, -1), (key2663, -1), (key2722, -1), (key2698, -1), (key2745, -1), (key2734, -1), (key2666, 2), (key2722, 2), (key2701, 2), (key2781, -1), (key2778, -1), (key2866, -1), (key2851, -1), (key2902, -1), (key2892, -1), (key2790, 2), (key2778, 2), (key2825, 2), (key2801, 2), (key2902, 2), (key2895, 2), (key2790, -1), (key2781, -1), (key2825, -1), (key2804, -1), (key2866, -1), (key2856, -1), (key2935, 2), (key2981, 2), (key2971, 2), (key2941, -1), (key2935, -1), (key2958, -1), (key2947, -1), (key2981, -1), (key2974, -1)]

def rawRow15899 : Integer.Sparse Key := [(key2698, -1), (key2734, -1), (key2663, -1), (key2745, -1), (key2666, -1), (key2722, -1), (key2701, 2), (key2666, 2), (key2722, 2), (key2851, -1), (key2892, -1), (key2778, -1), (key2902, -1), (key2781, -1), (key2866, -1), (key2801, 2), (key2895, 2), (key2778, 2), (key2902, 2), (key2790, 2), (key2825, 2), (key2804, -1), (key2856, -1), (key2781, -1), (key2866, -1), (key2790, -1), (key2825, -1), (key2971, 2), (key2935, 2), (key2981, 2), (key2947, -1), (key2974, -1), (key2935, -1), (key2981, -1), (key2941, -1), (key2958, -1)]

def rawRow15900 : Integer.Sparse Key := [(key2734, -1), (key2698, -1), (key2745, -1), (key2663, -1), (key2722, -1), (key2666, -1), (key2701, 2), (key2722, 2), (key2666, 2), (key2892, -1), (key2851, -1), (key2902, -1), (key2778, -1), (key2866, -1), (key2781, -1), (key2895, 2), (key2801, 2), (key2902, 2), (key2778, 2), (key2825, 2), (key2790, 2), (key2856, -1), (key2804, -1), (key2866, -1), (key2781, -1), (key2825, -1), (key2790, -1), (key2971, 2), (key2981, 2), (key2935, 2), (key2974, -1), (key2947, -1), (key2981, -1), (key2935, -1), (key2958, -1), (key2941, -1)]

def rawRow15901 : Integer.Sparse Key := [(key2722, -1), (key2745, -1), (key2666, -1), (key2734, -1), (key2663, -1), (key2698, -1), (key2722, 2), (key2666, 2), (key2701, 2), (key2866, -1), (key2902, -1), (key2781, -1), (key2892, -1), (key2778, -1), (key2851, -1), (key2825, 2), (key2902, 2), (key2790, 2), (key2895, 2), (key2778, 2), (key2801, 2), (key2825, -1), (key2866, -1), (key2790, -1), (key2856, -1), (key2781, -1), (key2804, -1), (key2981, 2), (key2935, 2), (key2971, 2), (key2958, -1), (key2981, -1), (key2941, -1), (key2974, -1), (key2935, -1), (key2947, -1)]

def rawRow15902 : Integer.Sparse Key := [(key2745, -1), (key2722, -1), (key2734, -1), (key2666, -1), (key2698, -1), (key2663, -1), (key2722, 2), (key2701, 2), (key2666, 2), (key2902, -1), (key2866, -1), (key2892, -1), (key2781, -1), (key2851, -1), (key2778, -1), (key2902, 2), (key2825, 2), (key2895, 2), (key2790, 2), (key2801, 2), (key2778, 2), (key2866, -1), (key2825, -1), (key2856, -1), (key2790, -1), (key2804, -1), (key2781, -1), (key2981, 2), (key2971, 2), (key2935, 2), (key2981, -1), (key2958, -1), (key2974, -1), (key2941, -1), (key2947, -1), (key2935, -1)]

def rawRow15903 : Integer.Sparse Key := [(key2666, -1), (key2666, -1), (key2701, -1), (key2701, -1), (key2734, -1), (key2734, -1), (key2663, 2), (key2698, 2), (key2698, 2), (key2790, -1), (key2790, -1), (key2856, -1), (key2856, -1), (key2895, -1), (key2895, -1), (key2781, 2), (key2781, 2), (key2804, 2), (key2804, 2), (key2892, 2), (key2892, 2), (key2778, -1), (key2778, -1), (key2801, -1), (key2801, -1), (key2851, -1), (key2851, -1), (key2941, 2), (key2974, 2), (key2974, 2), (key2935, -1), (key2935, -1), (key2947, -1), (key2947, -1), (key2971, -1), (key2971, -1)]

def rawRow15904 : Integer.Sparse Key := [(key2701, -1), (key2734, -1), (key2666, -1), (key2734, -1), (key2666, -1), (key2701, -1), (key2698, 2), (key2663, 2), (key2698, 2), (key2856, -1), (key2895, -1), (key2790, -1), (key2895, -1), (key2790, -1), (key2856, -1), (key2804, 2), (key2892, 2), (key2781, 2), (key2892, 2), (key2781, 2), (key2804, 2), (key2801, -1), (key2851, -1), (key2778, -1), (key2851, -1), (key2778, -1), (key2801, -1), (key2974, 2), (key2941, 2), (key2974, 2), (key2947, -1), (key2971, -1), (key2935, -1), (key2971, -1), (key2935, -1), (key2947, -1)]

def rawRow15905 : Integer.Sparse Key := [(key2734, -1), (key2701, -1), (key2734, -1), (key2666, -1), (key2701, -1), (key2666, -1), (key2698, 2), (key2698, 2), (key2663, 2), (key2895, -1), (key2856, -1), (key2895, -1), (key2790, -1), (key2856, -1), (key2790, -1), (key2892, 2), (key2804, 2), (key2892, 2), (key2781, 2), (key2804, 2), (key2781, 2), (key2851, -1), (key2801, -1), (key2851, -1), (key2778, -1), (key2801, -1), (key2778, -1), (key2974, 2), (key2974, 2), (key2941, 2), (key2971, -1), (key2947, -1), (key2971, -1), (key2935, -1), (key2947, -1), (key2935, -1)]

def rawRow15906 : Integer.Sparse Key := [(key2698, -1), (key2701, -1), (key2851, -1), (key2971, -1), (key2856, -1), (key2974, -1), (key2722, 2), (key2866, 2), (key2981, 2), (key2663, -1), (key2666, -1), (key2698, -1), (key2722, -1), (key2734, -1), (key2745, -1), (key2778, 2), (key2790, 2), (key2801, 2), (key2825, 2), (key2895, 2), (key2902, 2), (key2935, -1), (key2941, -1), (key2947, -1), (key2958, -1), (key2974, -1), (key2981, -1), (key2666, 2), (key2701, 2), (key2722, 2), (key2781, -1), (key2790, -1), (key2804, -1), (key2825, -1), (key2856, -1), (key2866, -1)]

def rawRow15907 : Integer.Sparse Key := [(key2701, -1), (key2698, -1), (key2971, -1), (key2851, -1), (key2974, -1), (key2856, -1), (key2722, 2), (key2981, 2), (key2866, 2), (key2666, -1), (key2663, -1), (key2722, -1), (key2698, -1), (key2745, -1), (key2734, -1), (key2790, 2), (key2778, 2), (key2825, 2), (key2801, 2), (key2902, 2), (key2895, 2), (key2941, -1), (key2935, -1), (key2958, -1), (key2947, -1), (key2981, -1), (key2974, -1), (key2666, 2), (key2722, 2), (key2701, 2), (key2790, -1), (key2781, -1), (key2825, -1), (key2804, -1), (key2866, -1), (key2856, -1)]

def rawRow15908 : Integer.Sparse Key := [(key2851, -1), (key2856, -1), (key2698, -1), (key2974, -1), (key2701, -1), (key2971, -1), (key2866, 2), (key2722, 2), (key2981, 2), (key2698, -1), (key2734, -1), (key2663, -1), (key2745, -1), (key2666, -1), (key2722, -1), (key2801, 2), (key2895, 2), (key2778, 2), (key2902, 2), (key2790, 2), (key2825, 2), (key2947, -1), (key2974, -1), (key2935, -1), (key2981, -1), (key2941, -1), (key2958, -1), (key2701, 2), (key2666, 2), (key2722, 2), (key2804, -1), (key2856, -1), (key2781, -1), (key2866, -1), (key2790, -1), (key2825, -1)]

def rawRow15909 : Integer.Sparse Key := [(key2856, -1), (key2851, -1), (key2974, -1), (key2698, -1), (key2971, -1), (key2701, -1), (key2866, 2), (key2981, 2), (key2722, 2), (key2734, -1), (key2698, -1), (key2745, -1), (key2663, -1), (key2722, -1), (key2666, -1), (key2895, 2), (key2801, 2), (key2902, 2), (key2778, 2), (key2825, 2), (key2790, 2), (key2974, -1), (key2947, -1), (key2981, -1), (key2935, -1), (key2958, -1), (key2941, -1), (key2701, 2), (key2722, 2), (key2666, 2), (key2856, -1), (key2804, -1), (key2866, -1), (key2781, -1), (key2825, -1), (key2790, -1)]

def rawRow15910 : Integer.Sparse Key := [(key2971, -1), (key2974, -1), (key2701, -1), (key2856, -1), (key2698, -1), (key2851, -1), (key2981, 2), (key2722, 2), (key2866, 2), (key2722, -1), (key2745, -1), (key2666, -1), (key2734, -1), (key2663, -1), (key2698, -1), (key2825, 2), (key2902, 2), (key2790, 2), (key2895, 2), (key2778, 2), (key2801, 2), (key2958, -1), (key2981, -1), (key2941, -1), (key2974, -1), (key2935, -1), (key2947, -1), (key2722, 2), (key2666, 2), (key2701, 2), (key2825, -1), (key2866, -1), (key2790, -1), (key2856, -1), (key2781, -1), (key2804, -1)]

def rawRow15911 : Integer.Sparse Key := [(key2974, -1), (key2971, -1), (key2856, -1), (key2701, -1), (key2851, -1), (key2698, -1), (key2981, 2), (key2866, 2), (key2722, 2), (key2745, -1), (key2722, -1), (key2734, -1), (key2666, -1), (key2698, -1), (key2663, -1), (key2902, 2), (key2825, 2), (key2895, 2), (key2790, 2), (key2801, 2), (key2778, 2), (key2981, -1), (key2958, -1), (key2974, -1), (key2941, -1), (key2947, -1), (key2935, -1), (key2722, 2), (key2701, 2), (key2666, 2), (key2866, -1), (key2825, -1), (key2856, -1), (key2790, -1), (key2804, -1), (key2781, -1)]

def rawRow15912 : Integer.Sparse Key := [(key2734, -1), (key2734, -1), (key2892, -1), (key2892, -1), (key2895, -1), (key2895, -1), (key2745, 2), (key2902, 2), (key2902, 2), (key2666, -1), (key2666, -1), (key2781, -1), (key2781, -1), (key2790, -1), (key2790, -1), (key2701, 2), (key2701, 2), (key2804, 2), (key2804, 2), (key2856, 2), (key2856, 2), (key2722, -1), (key2722, -1), (key2825, -1), (key2825, -1), (key2866, -1), (key2866, -1), (key2663, 2), (key2698, 2), (key2698, 2), (key2778, -1), (key2778, -1), (key2801, -1), (key2801, -1), (key2851, -1), (key2851, -1)]

def rawRow15913 : Integer.Sparse Key := [(key2892, -1), (key2895, -1), (key2734, -1), (key2895, -1), (key2734, -1), (key2892, -1), (key2902, 2), (key2745, 2), (key2902, 2), (key2781, -1), (key2790, -1), (key2666, -1), (key2790, -1), (key2666, -1), (key2781, -1), (key2804, 2), (key2856, 2), (key2701, 2), (key2856, 2), (key2701, 2), (key2804, 2), (key2825, -1), (key2866, -1), (key2722, -1), (key2866, -1), (key2722, -1), (key2825, -1), (key2698, 2), (key2663, 2), (key2698, 2), (key2801, -1), (key2851, -1), (key2778, -1), (key2851, -1), (key2778, -1), (key2801, -1)]

def rawRow15914 : Integer.Sparse Key := [(key2895, -1), (key2892, -1), (key2895, -1), (key2734, -1), (key2892, -1), (key2734, -1), (key2902, 2), (key2902, 2), (key2745, 2), (key2790, -1), (key2781, -1), (key2790, -1), (key2666, -1), (key2781, -1), (key2666, -1), (key2856, 2), (key2804, 2), (key2856, 2), (key2701, 2), (key2804, 2), (key2701, 2), (key2866, -1), (key2825, -1), (key2866, -1), (key2722, -1), (key2825, -1), (key2722, -1), (key2698, 2), (key2698, 2), (key2663, 2), (key2851, -1), (key2801, -1), (key2851, -1), (key2778, -1), (key2801, -1), (key2778, -1)]

def rawRow15951 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2392, 2), (key2378, -2), (key2381, -2), (key2392, -2), (key2472, 2), (key2480, 2), (key2482, 2), (key2406, -1), (key2409, -1), (key2472, -1), (key2538, -1), (key2482, -1), (key2543, -1), (key2503, -2), (key2506, -2), (key2522, -2), (key2437, -1), (key2440, -1), (key2503, -1), (key2554, -1), (key2522, -1), (key2563, -1), (key2440, 4), (key2506, 4), (key2554, 4)]

def rawRow15952 : Integer.Sparse Key := [(key2378, 2), (key2392, 2), (key2390, 2), (key2381, -2), (key2378, -2), (key2392, -2), (key2472, 2), (key2482, 2), (key2480, 2), (key2409, -1), (key2406, -1), (key2538, -1), (key2472, -1), (key2543, -1), (key2482, -1), (key2506, -2), (key2503, -2), (key2522, -2), (key2440, -1), (key2437, -1), (key2554, -1), (key2503, -1), (key2563, -1), (key2522, -1), (key2440, 4), (key2554, 4), (key2506, 4)]

def rawRow15953 : Integer.Sparse Key := [(key2390, 2), (key2378, 2), (key2392, 2), (key2378, -2), (key2392, -2), (key2381, -2), (key2480, 2), (key2472, 2), (key2482, 2), (key2472, -1), (key2482, -1), (key2406, -1), (key2543, -1), (key2409, -1), (key2538, -1), (key2503, -2), (key2522, -2), (key2506, -2), (key2503, -1), (key2522, -1), (key2437, -1), (key2563, -1), (key2440, -1), (key2554, -1), (key2506, 4), (key2440, 4), (key2554, 4)]

def rawRow15954 : Integer.Sparse Key := [(key2390, 2), (key2392, 2), (key2378, 2), (key2392, -2), (key2378, -2), (key2381, -2), (key2480, 2), (key2482, 2), (key2472, 2), (key2482, -1), (key2472, -1), (key2543, -1), (key2406, -1), (key2538, -1), (key2409, -1), (key2522, -2), (key2503, -2), (key2506, -2), (key2522, -1), (key2503, -1), (key2563, -1), (key2437, -1), (key2554, -1), (key2440, -1), (key2506, 4), (key2554, 4), (key2440, 4)]

def rawRow15955 : Integer.Sparse Key := [(key2392, 2), (key2378, 2), (key2390, 2), (key2381, -2), (key2392, -2), (key2378, -2), (key2482, 2), (key2472, 2), (key2480, 2), (key2538, -1), (key2543, -1), (key2409, -1), (key2482, -1), (key2406, -1), (key2472, -1), (key2506, -2), (key2522, -2), (key2503, -2), (key2554, -1), (key2563, -1), (key2440, -1), (key2522, -1), (key2437, -1), (key2503, -1), (key2554, 4), (key2440, 4), (key2506, 4)]

def rawRow15956 : Integer.Sparse Key := [(key2392, 2), (key2390, 2), (key2378, 2), (key2392, -2), (key2381, -2), (key2378, -2), (key2482, 2), (key2480, 2), (key2472, 2), (key2543, -1), (key2538, -1), (key2482, -1), (key2409, -1), (key2472, -1), (key2406, -1), (key2522, -2), (key2506, -2), (key2503, -2), (key2563, -1), (key2554, -1), (key2522, -1), (key2440, -1), (key2503, -1), (key2437, -1), (key2554, 4), (key2506, 4), (key2440, 4)]

def rawRow15957 : Integer.Sparse Key := [(key2381, 2), (key2392, 2), (key2392, 2), (key2378, -2), (key2378, -2), (key2390, -2), (key2538, 2), (key2543, 2), (key2543, 2), (key2406, -1), (key2406, -1), (key2472, -1), (key2472, -1), (key2480, -1), (key2480, -1), (key2554, -2), (key2554, -2), (key2563, -2), (key2440, -1), (key2440, -1), (key2506, -1), (key2506, -1), (key2522, -1), (key2522, -1), (key2437, 4), (key2503, 4), (key2503, 4)]

def rawRow15958 : Integer.Sparse Key := [(key2392, 2), (key2381, 2), (key2392, 2), (key2378, -2), (key2390, -2), (key2378, -2), (key2543, 2), (key2538, 2), (key2543, 2), (key2472, -1), (key2480, -1), (key2406, -1), (key2480, -1), (key2406, -1), (key2472, -1), (key2554, -2), (key2563, -2), (key2554, -2), (key2506, -1), (key2522, -1), (key2440, -1), (key2522, -1), (key2440, -1), (key2506, -1), (key2503, 4), (key2437, 4), (key2503, 4)]

def rawRow15959 : Integer.Sparse Key := [(key2392, 2), (key2392, 2), (key2381, 2), (key2390, -2), (key2378, -2), (key2378, -2), (key2543, 2), (key2543, 2), (key2538, 2), (key2480, -1), (key2472, -1), (key2480, -1), (key2406, -1), (key2472, -1), (key2406, -1), (key2563, -2), (key2554, -2), (key2554, -2), (key2522, -1), (key2506, -1), (key2522, -1), (key2440, -1), (key2506, -1), (key2440, -1), (key2503, 4), (key2503, 4), (key2437, 4)]

def rawRow15960 : Integer.Sparse Key := [(key2406, 2), (key2437, 2), (key2440, 2), (key2406, -2), (key2409, -2), (key2440, -2), (key2472, 2), (key2503, 2), (key2506, 2), (key2378, -1), (key2381, -1), (key2472, -1), (key2538, -1), (key2506, -1), (key2554, -1), (key2480, -2), (key2482, -2), (key2522, -2), (key2390, -1), (key2392, -1), (key2480, -1), (key2543, -1), (key2522, -1), (key2563, -1), (key2392, 4), (key2482, 4), (key2543, 4)]

def rawRow15961 : Integer.Sparse Key := [(key2406, 2), (key2440, 2), (key2437, 2), (key2409, -2), (key2406, -2), (key2440, -2), (key2472, 2), (key2506, 2), (key2503, 2), (key2381, -1), (key2378, -1), (key2538, -1), (key2472, -1), (key2554, -1), (key2506, -1), (key2482, -2), (key2480, -2), (key2522, -2), (key2392, -1), (key2390, -1), (key2543, -1), (key2480, -1), (key2563, -1), (key2522, -1), (key2392, 4), (key2543, 4), (key2482, 4)]

def rawRow15962 : Integer.Sparse Key := [(key2437, 2), (key2406, 2), (key2440, 2), (key2406, -2), (key2440, -2), (key2409, -2), (key2503, 2), (key2472, 2), (key2506, 2), (key2472, -1), (key2506, -1), (key2378, -1), (key2554, -1), (key2381, -1), (key2538, -1), (key2480, -2), (key2522, -2), (key2482, -2), (key2480, -1), (key2522, -1), (key2390, -1), (key2563, -1), (key2392, -1), (key2543, -1), (key2482, 4), (key2392, 4), (key2543, 4)]

def rawRow15963 : Integer.Sparse Key := [(key2437, 2), (key2440, 2), (key2406, 2), (key2440, -2), (key2406, -2), (key2409, -2), (key2503, 2), (key2506, 2), (key2472, 2), (key2506, -1), (key2472, -1), (key2554, -1), (key2378, -1), (key2538, -1), (key2381, -1), (key2522, -2), (key2480, -2), (key2482, -2), (key2522, -1), (key2480, -1), (key2563, -1), (key2390, -1), (key2543, -1), (key2392, -1), (key2482, 4), (key2543, 4), (key2392, 4)]

def rawRow15964 : Integer.Sparse Key := [(key2440, 2), (key2406, 2), (key2437, 2), (key2409, -2), (key2440, -2), (key2406, -2), (key2506, 2), (key2472, 2), (key2503, 2), (key2538, -1), (key2554, -1), (key2381, -1), (key2506, -1), (key2378, -1), (key2472, -1), (key2482, -2), (key2522, -2), (key2480, -2), (key2543, -1), (key2563, -1), (key2392, -1), (key2522, -1), (key2390, -1), (key2480, -1), (key2543, 4), (key2392, 4), (key2482, 4)]

def rawRow15965 : Integer.Sparse Key := [(key2440, 2), (key2437, 2), (key2406, 2), (key2440, -2), (key2409, -2), (key2406, -2), (key2506, 2), (key2503, 2), (key2472, 2), (key2554, -1), (key2538, -1), (key2506, -1), (key2381, -1), (key2472, -1), (key2378, -1), (key2522, -2), (key2482, -2), (key2480, -2), (key2563, -1), (key2543, -1), (key2522, -1), (key2392, -1), (key2480, -1), (key2390, -1), (key2543, 4), (key2482, 4), (key2392, 4)]

def rawRow15966 : Integer.Sparse Key := [(key2409, 2), (key2440, 2), (key2440, 2), (key2406, -2), (key2406, -2), (key2437, -2), (key2538, 2), (key2554, 2), (key2554, 2), (key2378, -1), (key2378, -1), (key2472, -1), (key2472, -1), (key2503, -1), (key2503, -1), (key2543, -2), (key2543, -2), (key2563, -2), (key2392, -1), (key2392, -1), (key2482, -1), (key2482, -1), (key2522, -1), (key2522, -1), (key2390, 4), (key2480, 4), (key2480, 4)]

def rawRow15967 : Integer.Sparse Key := [(key2440, 2), (key2409, 2), (key2440, 2), (key2406, -2), (key2437, -2), (key2406, -2), (key2554, 2), (key2538, 2), (key2554, 2), (key2472, -1), (key2503, -1), (key2378, -1), (key2503, -1), (key2378, -1), (key2472, -1), (key2543, -2), (key2563, -2), (key2543, -2), (key2482, -1), (key2522, -1), (key2392, -1), (key2522, -1), (key2392, -1), (key2482, -1), (key2480, 4), (key2390, 4), (key2480, 4)]

def rawRow15968 : Integer.Sparse Key := [(key2440, 2), (key2440, 2), (key2409, 2), (key2437, -2), (key2406, -2), (key2406, -2), (key2554, 2), (key2554, 2), (key2538, 2), (key2503, -1), (key2472, -1), (key2503, -1), (key2378, -1), (key2472, -1), (key2378, -1), (key2563, -2), (key2543, -2), (key2543, -2), (key2522, -1), (key2482, -1), (key2522, -1), (key2392, -1), (key2482, -1), (key2392, -1), (key2480, 4), (key2480, 4), (key2390, 4)]

def rawRow15969 : Integer.Sparse Key := [(key2472, 2), (key2480, 2), (key2482, 2), (key2503, -2), (key2506, -2), (key2522, -2), (key2378, 2), (key2390, 2), (key2392, 2), (key2437, -1), (key2440, -1), (key2503, -1), (key2554, -1), (key2522, -1), (key2563, -1), (key2378, -2), (key2381, -2), (key2392, -2), (key2406, -1), (key2409, -1), (key2472, -1), (key2538, -1), (key2482, -1), (key2543, -1), (key2440, 4), (key2506, 4), (key2554, 4)]

def rawRow15970 : Integer.Sparse Key := [(key2472, 2), (key2482, 2), (key2480, 2), (key2506, -2), (key2503, -2), (key2522, -2), (key2378, 2), (key2392, 2), (key2390, 2), (key2440, -1), (key2437, -1), (key2554, -1), (key2503, -1), (key2563, -1), (key2522, -1), (key2381, -2), (key2378, -2), (key2392, -2), (key2409, -1), (key2406, -1), (key2538, -1), (key2472, -1), (key2543, -1), (key2482, -1), (key2440, 4), (key2554, 4), (key2506, 4)]

def rawRow15971 : Integer.Sparse Key := [(key2480, 2), (key2472, 2), (key2482, 2), (key2503, -2), (key2522, -2), (key2506, -2), (key2390, 2), (key2378, 2), (key2392, 2), (key2503, -1), (key2522, -1), (key2437, -1), (key2563, -1), (key2440, -1), (key2554, -1), (key2378, -2), (key2392, -2), (key2381, -2), (key2472, -1), (key2482, -1), (key2406, -1), (key2543, -1), (key2409, -1), (key2538, -1), (key2506, 4), (key2440, 4), (key2554, 4)]

def rawRow15972 : Integer.Sparse Key := [(key2480, 2), (key2482, 2), (key2472, 2), (key2522, -2), (key2503, -2), (key2506, -2), (key2390, 2), (key2392, 2), (key2378, 2), (key2522, -1), (key2503, -1), (key2563, -1), (key2437, -1), (key2554, -1), (key2440, -1), (key2392, -2), (key2378, -2), (key2381, -2), (key2482, -1), (key2472, -1), (key2543, -1), (key2406, -1), (key2538, -1), (key2409, -1), (key2506, 4), (key2554, 4), (key2440, 4)]

def rawRow15973 : Integer.Sparse Key := [(key2482, 2), (key2472, 2), (key2480, 2), (key2506, -2), (key2522, -2), (key2503, -2), (key2392, 2), (key2378, 2), (key2390, 2), (key2554, -1), (key2563, -1), (key2440, -1), (key2522, -1), (key2437, -1), (key2503, -1), (key2381, -2), (key2392, -2), (key2378, -2), (key2538, -1), (key2543, -1), (key2409, -1), (key2482, -1), (key2406, -1), (key2472, -1), (key2554, 4), (key2440, 4), (key2506, 4)]

def rawRow15974 : Integer.Sparse Key := [(key2482, 2), (key2480, 2), (key2472, 2), (key2522, -2), (key2506, -2), (key2503, -2), (key2392, 2), (key2390, 2), (key2378, 2), (key2563, -1), (key2554, -1), (key2522, -1), (key2440, -1), (key2503, -1), (key2437, -1), (key2392, -2), (key2381, -2), (key2378, -2), (key2543, -1), (key2538, -1), (key2482, -1), (key2409, -1), (key2472, -1), (key2406, -1), (key2554, 4), (key2506, 4), (key2440, 4)]

def rawRow15975 : Integer.Sparse Key := [(key2472, 2), (key2503, 2), (key2506, 2), (key2480, -2), (key2482, -2), (key2522, -2), (key2406, 2), (key2437, 2), (key2440, 2), (key2390, -1), (key2392, -1), (key2480, -1), (key2543, -1), (key2522, -1), (key2563, -1), (key2406, -2), (key2409, -2), (key2440, -2), (key2378, -1), (key2381, -1), (key2472, -1), (key2538, -1), (key2506, -1), (key2554, -1), (key2392, 4), (key2482, 4), (key2543, 4)]

def rawRow15976 : Integer.Sparse Key := [(key2472, 2), (key2506, 2), (key2503, 2), (key2482, -2), (key2480, -2), (key2522, -2), (key2406, 2), (key2440, 2), (key2437, 2), (key2392, -1), (key2390, -1), (key2543, -1), (key2480, -1), (key2563, -1), (key2522, -1), (key2409, -2), (key2406, -2), (key2440, -2), (key2381, -1), (key2378, -1), (key2538, -1), (key2472, -1), (key2554, -1), (key2506, -1), (key2392, 4), (key2543, 4), (key2482, 4)]

def rawRow15977 : Integer.Sparse Key := [(key2503, 2), (key2472, 2), (key2506, 2), (key2480, -2), (key2522, -2), (key2482, -2), (key2437, 2), (key2406, 2), (key2440, 2), (key2480, -1), (key2522, -1), (key2390, -1), (key2563, -1), (key2392, -1), (key2543, -1), (key2406, -2), (key2440, -2), (key2409, -2), (key2472, -1), (key2506, -1), (key2378, -1), (key2554, -1), (key2381, -1), (key2538, -1), (key2482, 4), (key2392, 4), (key2543, 4)]

def rawRow15978 : Integer.Sparse Key := [(key2503, 2), (key2506, 2), (key2472, 2), (key2522, -2), (key2480, -2), (key2482, -2), (key2437, 2), (key2440, 2), (key2406, 2), (key2522, -1), (key2480, -1), (key2563, -1), (key2390, -1), (key2543, -1), (key2392, -1), (key2440, -2), (key2406, -2), (key2409, -2), (key2506, -1), (key2472, -1), (key2554, -1), (key2378, -1), (key2538, -1), (key2381, -1), (key2482, 4), (key2543, 4), (key2392, 4)]

def rawRow15979 : Integer.Sparse Key := [(key2506, 2), (key2472, 2), (key2503, 2), (key2482, -2), (key2522, -2), (key2480, -2), (key2440, 2), (key2406, 2), (key2437, 2), (key2543, -1), (key2563, -1), (key2392, -1), (key2522, -1), (key2390, -1), (key2480, -1), (key2409, -2), (key2440, -2), (key2406, -2), (key2538, -1), (key2554, -1), (key2381, -1), (key2506, -1), (key2378, -1), (key2472, -1), (key2543, 4), (key2392, 4), (key2482, 4)]

def rawRow15980 : Integer.Sparse Key := [(key2506, 2), (key2503, 2), (key2472, 2), (key2522, -2), (key2482, -2), (key2480, -2), (key2440, 2), (key2437, 2), (key2406, 2), (key2563, -1), (key2543, -1), (key2522, -1), (key2392, -1), (key2480, -1), (key2390, -1), (key2440, -2), (key2409, -2), (key2406, -2), (key2554, -1), (key2538, -1), (key2506, -1), (key2381, -1), (key2472, -1), (key2378, -1), (key2543, 4), (key2482, 4), (key2392, 4)]

def rawRow15981 : Integer.Sparse Key := [(key2538, 2), (key2543, 2), (key2543, 2), (key2554, -2), (key2554, -2), (key2563, -2), (key2381, 2), (key2392, 2), (key2392, 2), (key2440, -1), (key2440, -1), (key2506, -1), (key2506, -1), (key2522, -1), (key2522, -1), (key2378, -2), (key2378, -2), (key2390, -2), (key2406, -1), (key2406, -1), (key2472, -1), (key2472, -1), (key2480, -1), (key2480, -1), (key2437, 4), (key2503, 4), (key2503, 4)]

def rawRow15982 : Integer.Sparse Key := [(key2543, 2), (key2538, 2), (key2543, 2), (key2554, -2), (key2563, -2), (key2554, -2), (key2392, 2), (key2381, 2), (key2392, 2), (key2506, -1), (key2522, -1), (key2440, -1), (key2522, -1), (key2440, -1), (key2506, -1), (key2378, -2), (key2390, -2), (key2378, -2), (key2472, -1), (key2480, -1), (key2406, -1), (key2480, -1), (key2406, -1), (key2472, -1), (key2503, 4), (key2437, 4), (key2503, 4)]

def rawRow15983 : Integer.Sparse Key := [(key2543, 2), (key2543, 2), (key2538, 2), (key2563, -2), (key2554, -2), (key2554, -2), (key2392, 2), (key2392, 2), (key2381, 2), (key2522, -1), (key2506, -1), (key2522, -1), (key2440, -1), (key2506, -1), (key2440, -1), (key2390, -2), (key2378, -2), (key2378, -2), (key2480, -1), (key2472, -1), (key2480, -1), (key2406, -1), (key2472, -1), (key2406, -1), (key2503, 4), (key2503, 4), (key2437, 4)]

def rawRow15984 : Integer.Sparse Key := [(key2538, 2), (key2554, 2), (key2554, 2), (key2543, -2), (key2543, -2), (key2563, -2), (key2409, 2), (key2440, 2), (key2440, 2), (key2392, -1), (key2392, -1), (key2482, -1), (key2482, -1), (key2522, -1), (key2522, -1), (key2406, -2), (key2406, -2), (key2437, -2), (key2378, -1), (key2378, -1), (key2472, -1), (key2472, -1), (key2503, -1), (key2503, -1), (key2390, 4), (key2480, 4), (key2480, 4)]

def rawRow15985 : Integer.Sparse Key := [(key2554, 2), (key2538, 2), (key2554, 2), (key2543, -2), (key2563, -2), (key2543, -2), (key2440, 2), (key2409, 2), (key2440, 2), (key2482, -1), (key2522, -1), (key2392, -1), (key2522, -1), (key2392, -1), (key2482, -1), (key2406, -2), (key2437, -2), (key2406, -2), (key2472, -1), (key2503, -1), (key2378, -1), (key2503, -1), (key2378, -1), (key2472, -1), (key2480, 4), (key2390, 4), (key2480, 4)]

def rawRow15986 : Integer.Sparse Key := [(key2554, 2), (key2554, 2), (key2538, 2), (key2563, -2), (key2543, -2), (key2543, -2), (key2440, 2), (key2440, 2), (key2409, 2), (key2522, -1), (key2482, -1), (key2522, -1), (key2392, -1), (key2482, -1), (key2392, -1), (key2437, -2), (key2406, -2), (key2406, -2), (key2503, -1), (key2472, -1), (key2503, -1), (key2378, -1), (key2472, -1), (key2378, -1), (key2480, 4), (key2480, 4), (key2390, 4)]

def rawRow15987 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2609, -1), (key2613, -1), (key2625, -1), (key2647, -1), (key2637, -1), (key2652, -1), (key2779, 2), (key2783, 2), (key2791, 2), (key2664, -1), (key2668, -1), (key2779, -1), (key2937, -1), (key2791, -1), (key2942, -1), (key2802, -1), (key2806, -1), (key2852, -1), (key2894, -1), (key2857, -1), (key2896, -1), (key2699, -1), (key2703, -1), (key2852, -1), (key2973, -1), (key2857, -1), (key2975, -1), (key2699, 2), (key2736, 2), (key2802, 2), (key2949, 2), (key2896, 2), (key2975, 2)]

def rawRow15988 : Integer.Sparse Key := [(key2629, 2), (key2625, 2), (key2637, 2), (key2613, -1), (key2609, -1), (key2647, -1), (key2625, -1), (key2652, -1), (key2637, -1), (key2783, 2), (key2779, 2), (key2791, 2), (key2668, -1), (key2664, -1), (key2937, -1), (key2779, -1), (key2942, -1), (key2791, -1), (key2806, -1), (key2802, -1), (key2894, -1), (key2852, -1), (key2896, -1), (key2857, -1), (key2703, -1), (key2699, -1), (key2973, -1), (key2852, -1), (key2975, -1), (key2857, -1), (key2736, 2), (key2699, 2), (key2949, 2), (key2802, 2), (key2975, 2), (key2896, 2)]

def rawRow15989 : Integer.Sparse Key := [(key2625, 2), (key2637, 2), (key2629, 2), (key2625, -1), (key2637, -1), (key2609, -1), (key2652, -1), (key2613, -1), (key2647, -1), (key2779, 2), (key2791, 2), (key2783, 2), (key2779, -1), (key2791, -1), (key2664, -1), (key2942, -1), (key2668, -1), (key2937, -1), (key2852, -1), (key2857, -1), (key2802, -1), (key2896, -1), (key2806, -1), (key2894, -1), (key2852, -1), (key2857, -1), (key2699, -1), (key2975, -1), (key2703, -1), (key2973, -1), (key2802, 2), (key2896, 2), (key2699, 2), (key2975, 2), (key2736, 2), (key2949, 2)]

def rawRow15990 : Integer.Sparse Key := [(key2637, 2), (key2625, 2), (key2629, 2), (key2637, -1), (key2625, -1), (key2652, -1), (key2609, -1), (key2647, -1), (key2613, -1), (key2791, 2), (key2779, 2), (key2783, 2), (key2791, -1), (key2779, -1), (key2942, -1), (key2664, -1), (key2937, -1), (key2668, -1), (key2857, -1), (key2852, -1), (key2896, -1), (key2802, -1), (key2894, -1), (key2806, -1), (key2857, -1), (key2852, -1), (key2975, -1), (key2699, -1), (key2973, -1), (key2703, -1), (key2896, 2), (key2802, 2), (key2975, 2), (key2699, 2), (key2949, 2), (key2736, 2)]

def rawRow15991 : Integer.Sparse Key := [(key2629, 2), (key2637, 2), (key2625, 2), (key2647, -1), (key2652, -1), (key2613, -1), (key2637, -1), (key2609, -1), (key2625, -1), (key2783, 2), (key2791, 2), (key2779, 2), (key2937, -1), (key2942, -1), (key2668, -1), (key2791, -1), (key2664, -1), (key2779, -1), (key2894, -1), (key2896, -1), (key2806, -1), (key2857, -1), (key2802, -1), (key2852, -1), (key2973, -1), (key2975, -1), (key2703, -1), (key2857, -1), (key2699, -1), (key2852, -1), (key2949, 2), (key2975, 2), (key2736, 2), (key2896, 2), (key2699, 2), (key2802, 2)]

def rawRow15992 : Integer.Sparse Key := [(key2637, 2), (key2629, 2), (key2625, 2), (key2652, -1), (key2647, -1), (key2637, -1), (key2613, -1), (key2625, -1), (key2609, -1), (key2791, 2), (key2783, 2), (key2779, 2), (key2942, -1), (key2937, -1), (key2791, -1), (key2668, -1), (key2779, -1), (key2664, -1), (key2896, -1), (key2894, -1), (key2857, -1), (key2806, -1), (key2852, -1), (key2802, -1), (key2975, -1), (key2973, -1), (key2857, -1), (key2703, -1), (key2852, -1), (key2699, -1), (key2975, 2), (key2949, 2), (key2896, 2), (key2736, 2), (key2802, 2), (key2699, 2)]

def rawRow15993 : Integer.Sparse Key := [(key2647, 2), (key2647, 2), (key2652, 2), (key2613, -1), (key2613, -1), (key2629, -1), (key2629, -1), (key2637, -1), (key2637, -1), (key2937, 2), (key2937, 2), (key2942, 2), (key2668, -1), (key2668, -1), (key2783, -1), (key2783, -1), (key2791, -1), (key2791, -1), (key2949, -1), (key2949, -1), (key2973, -1), (key2973, -1), (key2975, -1), (key2975, -1), (key2736, -1), (key2736, -1), (key2894, -1), (key2894, -1), (key2896, -1), (key2896, -1), (key2703, 2), (key2703, 2), (key2806, 2), (key2806, 2), (key2857, 2), (key2857, 2)]

def rawRow15994 : Integer.Sparse Key := [(key2647, 2), (key2652, 2), (key2647, 2), (key2629, -1), (key2637, -1), (key2613, -1), (key2637, -1), (key2613, -1), (key2629, -1), (key2937, 2), (key2942, 2), (key2937, 2), (key2783, -1), (key2791, -1), (key2668, -1), (key2791, -1), (key2668, -1), (key2783, -1), (key2973, -1), (key2975, -1), (key2949, -1), (key2975, -1), (key2949, -1), (key2973, -1), (key2894, -1), (key2896, -1), (key2736, -1), (key2896, -1), (key2736, -1), (key2894, -1), (key2806, 2), (key2857, 2), (key2703, 2), (key2857, 2), (key2703, 2), (key2806, 2)]

def rawRow15995 : Integer.Sparse Key := [(key2652, 2), (key2647, 2), (key2647, 2), (key2637, -1), (key2629, -1), (key2637, -1), (key2613, -1), (key2629, -1), (key2613, -1), (key2942, 2), (key2937, 2), (key2937, 2), (key2791, -1), (key2783, -1), (key2791, -1), (key2668, -1), (key2783, -1), (key2668, -1), (key2975, -1), (key2973, -1), (key2975, -1), (key2949, -1), (key2973, -1), (key2949, -1), (key2896, -1), (key2894, -1), (key2896, -1), (key2736, -1), (key2894, -1), (key2736, -1), (key2857, 2), (key2806, 2), (key2857, 2), (key2703, 2), (key2806, 2), (key2703, 2)]

def rawRow15996 : Integer.Sparse Key := [(key2699, 2), (key2703, 2), (key2723, 2), (key2664, -1), (key2668, -1), (key2699, -1), (key2736, -1), (key2723, -1), (key2746, -1), (key2802, 2), (key2806, 2), (key2826, 2), (key2609, -1), (key2613, -1), (key2802, -1), (key2949, -1), (key2826, -1), (key2959, -1), (key2779, -1), (key2783, -1), (key2852, -1), (key2894, -1), (key2867, -1), (key2903, -1), (key2625, -1), (key2629, -1), (key2852, -1), (key2973, -1), (key2867, -1), (key2982, -1), (key2625, 2), (key2647, 2), (key2779, 2), (key2937, 2), (key2903, 2), (key2982, 2)]

def rawRow15997 : Integer.Sparse Key := [(key2703, 2), (key2699, 2), (key2723, 2), (key2668, -1), (key2664, -1), (key2736, -1), (key2699, -1), (key2746, -1), (key2723, -1), (key2806, 2), (key2802, 2), (key2826, 2), (key2613, -1), (key2609, -1), (key2949, -1), (key2802, -1), (key2959, -1), (key2826, -1), (key2783, -1), (key2779, -1), (key2894, -1), (key2852, -1), (key2903, -1), (key2867, -1), (key2629, -1), (key2625, -1), (key2973, -1), (key2852, -1), (key2982, -1), (key2867, -1), (key2647, 2), (key2625, 2), (key2937, 2), (key2779, 2), (key2982, 2), (key2903, 2)]

def rawRow15998 : Integer.Sparse Key := [(key2699, 2), (key2723, 2), (key2703, 2), (key2699, -1), (key2723, -1), (key2664, -1), (key2746, -1), (key2668, -1), (key2736, -1), (key2802, 2), (key2826, 2), (key2806, 2), (key2802, -1), (key2826, -1), (key2609, -1), (key2959, -1), (key2613, -1), (key2949, -1), (key2852, -1), (key2867, -1), (key2779, -1), (key2903, -1), (key2783, -1), (key2894, -1), (key2852, -1), (key2867, -1), (key2625, -1), (key2982, -1), (key2629, -1), (key2973, -1), (key2779, 2), (key2903, 2), (key2625, 2), (key2982, 2), (key2647, 2), (key2937, 2)]

def rawRow15999 : Integer.Sparse Key := [(key2723, 2), (key2699, 2), (key2703, 2), (key2723, -1), (key2699, -1), (key2746, -1), (key2664, -1), (key2736, -1), (key2668, -1), (key2826, 2), (key2802, 2), (key2806, 2), (key2826, -1), (key2802, -1), (key2959, -1), (key2609, -1), (key2949, -1), (key2613, -1), (key2867, -1), (key2852, -1), (key2903, -1), (key2779, -1), (key2894, -1), (key2783, -1), (key2867, -1), (key2852, -1), (key2982, -1), (key2625, -1), (key2973, -1), (key2629, -1), (key2903, 2), (key2779, 2), (key2982, 2), (key2625, 2), (key2937, 2), (key2647, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block149
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow16000 : Integer.Sparse Key := [(key2703, 2), (key2723, 2), (key2699, 2), (key2736, -1), (key2746, -1), (key2668, -1), (key2723, -1), (key2664, -1), (key2699, -1), (key2806, 2), (key2826, 2), (key2802, 2), (key2949, -1), (key2959, -1), (key2613, -1), (key2826, -1), (key2609, -1), (key2802, -1), (key2894, -1), (key2903, -1), (key2783, -1), (key2867, -1), (key2779, -1), (key2852, -1), (key2973, -1), (key2982, -1), (key2629, -1), (key2867, -1), (key2625, -1), (key2852, -1), (key2937, 2), (key2982, 2), (key2647, 2), (key2903, 2), (key2625, 2), (key2779, 2)]

def rawRow16001 : Integer.Sparse Key := [(key2723, 2), (key2703, 2), (key2699, 2), (key2746, -1), (key2736, -1), (key2723, -1), (key2668, -1), (key2699, -1), (key2664, -1), (key2826, 2), (key2806, 2), (key2802, 2), (key2959, -1), (key2949, -1), (key2826, -1), (key2613, -1), (key2802, -1), (key2609, -1), (key2903, -1), (key2894, -1), (key2867, -1), (key2783, -1), (key2852, -1), (key2779, -1), (key2982, -1), (key2973, -1), (key2867, -1), (key2629, -1), (key2852, -1), (key2625, -1), (key2982, 2), (key2937, 2), (key2903, 2), (key2647, 2), (key2779, 2), (key2625, 2)]

def rawRow16002 : Integer.Sparse Key := [(key2736, 2), (key2736, 2), (key2746, 2), (key2668, -1), (key2668, -1), (key2703, -1), (key2703, -1), (key2723, -1), (key2723, -1), (key2949, 2), (key2949, 2), (key2959, 2), (key2613, -1), (key2613, -1), (key2806, -1), (key2806, -1), (key2826, -1), (key2826, -1), (key2937, -1), (key2937, -1), (key2973, -1), (key2973, -1), (key2982, -1), (key2982, -1), (key2647, -1), (key2647, -1), (key2894, -1), (key2894, -1), (key2903, -1), (key2903, -1), (key2629, 2), (key2629, 2), (key2783, 2), (key2783, 2), (key2867, 2), (key2867, 2)]

def rawRow16003 : Integer.Sparse Key := [(key2736, 2), (key2746, 2), (key2736, 2), (key2703, -1), (key2723, -1), (key2668, -1), (key2723, -1), (key2668, -1), (key2703, -1), (key2949, 2), (key2959, 2), (key2949, 2), (key2806, -1), (key2826, -1), (key2613, -1), (key2826, -1), (key2613, -1), (key2806, -1), (key2973, -1), (key2982, -1), (key2937, -1), (key2982, -1), (key2937, -1), (key2973, -1), (key2894, -1), (key2903, -1), (key2647, -1), (key2903, -1), (key2647, -1), (key2894, -1), (key2783, 2), (key2867, 2), (key2629, 2), (key2867, 2), (key2629, 2), (key2783, 2)]

def rawRow16004 : Integer.Sparse Key := [(key2746, 2), (key2736, 2), (key2736, 2), (key2723, -1), (key2703, -1), (key2723, -1), (key2668, -1), (key2703, -1), (key2668, -1), (key2959, 2), (key2949, 2), (key2949, 2), (key2826, -1), (key2806, -1), (key2826, -1), (key2613, -1), (key2806, -1), (key2613, -1), (key2982, -1), (key2973, -1), (key2982, -1), (key2937, -1), (key2973, -1), (key2937, -1), (key2903, -1), (key2894, -1), (key2903, -1), (key2647, -1), (key2894, -1), (key2647, -1), (key2867, 2), (key2783, 2), (key2867, 2), (key2629, 2), (key2783, 2), (key2629, 2)]

def rawRow16005 : Integer.Sparse Key := [(key2779, 2), (key2783, 2), (key2791, 2), (key2802, -1), (key2806, -1), (key2852, -1), (key2894, -1), (key2857, -1), (key2896, -1), (key2625, 2), (key2629, 2), (key2637, 2), (key2699, -1), (key2703, -1), (key2852, -1), (key2973, -1), (key2857, -1), (key2975, -1), (key2609, -1), (key2613, -1), (key2625, -1), (key2647, -1), (key2637, -1), (key2652, -1), (key2664, -1), (key2668, -1), (key2779, -1), (key2937, -1), (key2791, -1), (key2942, -1), (key2699, 2), (key2736, 2), (key2802, 2), (key2949, 2), (key2896, 2), (key2975, 2)]

def rawRow16006 : Integer.Sparse Key := [(key2783, 2), (key2779, 2), (key2791, 2), (key2806, -1), (key2802, -1), (key2894, -1), (key2852, -1), (key2896, -1), (key2857, -1), (key2629, 2), (key2625, 2), (key2637, 2), (key2703, -1), (key2699, -1), (key2973, -1), (key2852, -1), (key2975, -1), (key2857, -1), (key2613, -1), (key2609, -1), (key2647, -1), (key2625, -1), (key2652, -1), (key2637, -1), (key2668, -1), (key2664, -1), (key2937, -1), (key2779, -1), (key2942, -1), (key2791, -1), (key2736, 2), (key2699, 2), (key2949, 2), (key2802, 2), (key2975, 2), (key2896, 2)]

def rawRow16007 : Integer.Sparse Key := [(key2779, 2), (key2791, 2), (key2783, 2), (key2852, -1), (key2857, -1), (key2802, -1), (key2896, -1), (key2806, -1), (key2894, -1), (key2625, 2), (key2637, 2), (key2629, 2), (key2852, -1), (key2857, -1), (key2699, -1), (key2975, -1), (key2703, -1), (key2973, -1), (key2625, -1), (key2637, -1), (key2609, -1), (key2652, -1), (key2613, -1), (key2647, -1), (key2779, -1), (key2791, -1), (key2664, -1), (key2942, -1), (key2668, -1), (key2937, -1), (key2802, 2), (key2896, 2), (key2699, 2), (key2975, 2), (key2736, 2), (key2949, 2)]

def rawRow16008 : Integer.Sparse Key := [(key2791, 2), (key2779, 2), (key2783, 2), (key2857, -1), (key2852, -1), (key2896, -1), (key2802, -1), (key2894, -1), (key2806, -1), (key2637, 2), (key2625, 2), (key2629, 2), (key2857, -1), (key2852, -1), (key2975, -1), (key2699, -1), (key2973, -1), (key2703, -1), (key2637, -1), (key2625, -1), (key2652, -1), (key2609, -1), (key2647, -1), (key2613, -1), (key2791, -1), (key2779, -1), (key2942, -1), (key2664, -1), (key2937, -1), (key2668, -1), (key2896, 2), (key2802, 2), (key2975, 2), (key2699, 2), (key2949, 2), (key2736, 2)]

def rawRow16009 : Integer.Sparse Key := [(key2783, 2), (key2791, 2), (key2779, 2), (key2894, -1), (key2896, -1), (key2806, -1), (key2857, -1), (key2802, -1), (key2852, -1), (key2629, 2), (key2637, 2), (key2625, 2), (key2973, -1), (key2975, -1), (key2703, -1), (key2857, -1), (key2699, -1), (key2852, -1), (key2647, -1), (key2652, -1), (key2613, -1), (key2637, -1), (key2609, -1), (key2625, -1), (key2937, -1), (key2942, -1), (key2668, -1), (key2791, -1), (key2664, -1), (key2779, -1), (key2949, 2), (key2975, 2), (key2736, 2), (key2896, 2), (key2699, 2), (key2802, 2)]

def rawRow16010 : Integer.Sparse Key := [(key2791, 2), (key2783, 2), (key2779, 2), (key2896, -1), (key2894, -1), (key2857, -1), (key2806, -1), (key2852, -1), (key2802, -1), (key2637, 2), (key2629, 2), (key2625, 2), (key2975, -1), (key2973, -1), (key2857, -1), (key2703, -1), (key2852, -1), (key2699, -1), (key2652, -1), (key2647, -1), (key2637, -1), (key2613, -1), (key2625, -1), (key2609, -1), (key2942, -1), (key2937, -1), (key2791, -1), (key2668, -1), (key2779, -1), (key2664, -1), (key2975, 2), (key2949, 2), (key2896, 2), (key2736, 2), (key2802, 2), (key2699, 2)]

def rawRow16011 : Integer.Sparse Key := [(key2802, 2), (key2806, 2), (key2826, 2), (key2779, -1), (key2783, -1), (key2852, -1), (key2894, -1), (key2867, -1), (key2903, -1), (key2699, 2), (key2703, 2), (key2723, 2), (key2625, -1), (key2629, -1), (key2852, -1), (key2973, -1), (key2867, -1), (key2982, -1), (key2664, -1), (key2668, -1), (key2699, -1), (key2736, -1), (key2723, -1), (key2746, -1), (key2609, -1), (key2613, -1), (key2802, -1), (key2949, -1), (key2826, -1), (key2959, -1), (key2625, 2), (key2647, 2), (key2779, 2), (key2937, 2), (key2903, 2), (key2982, 2)]

def rawRow16012 : Integer.Sparse Key := [(key2806, 2), (key2802, 2), (key2826, 2), (key2783, -1), (key2779, -1), (key2894, -1), (key2852, -1), (key2903, -1), (key2867, -1), (key2703, 2), (key2699, 2), (key2723, 2), (key2629, -1), (key2625, -1), (key2973, -1), (key2852, -1), (key2982, -1), (key2867, -1), (key2668, -1), (key2664, -1), (key2736, -1), (key2699, -1), (key2746, -1), (key2723, -1), (key2613, -1), (key2609, -1), (key2949, -1), (key2802, -1), (key2959, -1), (key2826, -1), (key2647, 2), (key2625, 2), (key2937, 2), (key2779, 2), (key2982, 2), (key2903, 2)]

def rawRow16013 : Integer.Sparse Key := [(key2802, 2), (key2826, 2), (key2806, 2), (key2852, -1), (key2867, -1), (key2779, -1), (key2903, -1), (key2783, -1), (key2894, -1), (key2699, 2), (key2723, 2), (key2703, 2), (key2852, -1), (key2867, -1), (key2625, -1), (key2982, -1), (key2629, -1), (key2973, -1), (key2699, -1), (key2723, -1), (key2664, -1), (key2746, -1), (key2668, -1), (key2736, -1), (key2802, -1), (key2826, -1), (key2609, -1), (key2959, -1), (key2613, -1), (key2949, -1), (key2779, 2), (key2903, 2), (key2625, 2), (key2982, 2), (key2647, 2), (key2937, 2)]

def rawRow16014 : Integer.Sparse Key := [(key2826, 2), (key2802, 2), (key2806, 2), (key2867, -1), (key2852, -1), (key2903, -1), (key2779, -1), (key2894, -1), (key2783, -1), (key2723, 2), (key2699, 2), (key2703, 2), (key2867, -1), (key2852, -1), (key2982, -1), (key2625, -1), (key2973, -1), (key2629, -1), (key2723, -1), (key2699, -1), (key2746, -1), (key2664, -1), (key2736, -1), (key2668, -1), (key2826, -1), (key2802, -1), (key2959, -1), (key2609, -1), (key2949, -1), (key2613, -1), (key2903, 2), (key2779, 2), (key2982, 2), (key2625, 2), (key2937, 2), (key2647, 2)]

def rawRow16015 : Integer.Sparse Key := [(key2806, 2), (key2826, 2), (key2802, 2), (key2894, -1), (key2903, -1), (key2783, -1), (key2867, -1), (key2779, -1), (key2852, -1), (key2703, 2), (key2723, 2), (key2699, 2), (key2973, -1), (key2982, -1), (key2629, -1), (key2867, -1), (key2625, -1), (key2852, -1), (key2736, -1), (key2746, -1), (key2668, -1), (key2723, -1), (key2664, -1), (key2699, -1), (key2949, -1), (key2959, -1), (key2613, -1), (key2826, -1), (key2609, -1), (key2802, -1), (key2937, 2), (key2982, 2), (key2647, 2), (key2903, 2), (key2625, 2), (key2779, 2)]

def rawRow16016 : Integer.Sparse Key := [(key2826, 2), (key2806, 2), (key2802, 2), (key2903, -1), (key2894, -1), (key2867, -1), (key2783, -1), (key2852, -1), (key2779, -1), (key2723, 2), (key2703, 2), (key2699, 2), (key2982, -1), (key2973, -1), (key2867, -1), (key2629, -1), (key2852, -1), (key2625, -1), (key2746, -1), (key2736, -1), (key2723, -1), (key2668, -1), (key2699, -1), (key2664, -1), (key2959, -1), (key2949, -1), (key2826, -1), (key2613, -1), (key2802, -1), (key2609, -1), (key2982, 2), (key2937, 2), (key2903, 2), (key2647, 2), (key2779, 2), (key2625, 2)]

def rawRow16017 : Integer.Sparse Key := [(key2937, 2), (key2937, 2), (key2942, 2), (key2949, -1), (key2949, -1), (key2973, -1), (key2973, -1), (key2975, -1), (key2975, -1), (key2647, 2), (key2647, 2), (key2652, 2), (key2736, -1), (key2736, -1), (key2894, -1), (key2894, -1), (key2896, -1), (key2896, -1), (key2613, -1), (key2613, -1), (key2629, -1), (key2629, -1), (key2637, -1), (key2637, -1), (key2668, -1), (key2668, -1), (key2783, -1), (key2783, -1), (key2791, -1), (key2791, -1), (key2703, 2), (key2703, 2), (key2806, 2), (key2806, 2), (key2857, 2), (key2857, 2)]

def rawRow16018 : Integer.Sparse Key := [(key2937, 2), (key2942, 2), (key2937, 2), (key2973, -1), (key2975, -1), (key2949, -1), (key2975, -1), (key2949, -1), (key2973, -1), (key2647, 2), (key2652, 2), (key2647, 2), (key2894, -1), (key2896, -1), (key2736, -1), (key2896, -1), (key2736, -1), (key2894, -1), (key2629, -1), (key2637, -1), (key2613, -1), (key2637, -1), (key2613, -1), (key2629, -1), (key2783, -1), (key2791, -1), (key2668, -1), (key2791, -1), (key2668, -1), (key2783, -1), (key2806, 2), (key2857, 2), (key2703, 2), (key2857, 2), (key2703, 2), (key2806, 2)]

def rawRow16019 : Integer.Sparse Key := [(key2942, 2), (key2937, 2), (key2937, 2), (key2975, -1), (key2973, -1), (key2975, -1), (key2949, -1), (key2973, -1), (key2949, -1), (key2652, 2), (key2647, 2), (key2647, 2), (key2896, -1), (key2894, -1), (key2896, -1), (key2736, -1), (key2894, -1), (key2736, -1), (key2637, -1), (key2629, -1), (key2637, -1), (key2613, -1), (key2629, -1), (key2613, -1), (key2791, -1), (key2783, -1), (key2791, -1), (key2668, -1), (key2783, -1), (key2668, -1), (key2857, 2), (key2806, 2), (key2857, 2), (key2703, 2), (key2806, 2), (key2703, 2)]

def rawRow16020 : Integer.Sparse Key := [(key2949, 2), (key2949, 2), (key2959, 2), (key2937, -1), (key2937, -1), (key2973, -1), (key2973, -1), (key2982, -1), (key2982, -1), (key2736, 2), (key2736, 2), (key2746, 2), (key2647, -1), (key2647, -1), (key2894, -1), (key2894, -1), (key2903, -1), (key2903, -1), (key2668, -1), (key2668, -1), (key2703, -1), (key2703, -1), (key2723, -1), (key2723, -1), (key2613, -1), (key2613, -1), (key2806, -1), (key2806, -1), (key2826, -1), (key2826, -1), (key2629, 2), (key2629, 2), (key2783, 2), (key2783, 2), (key2867, 2), (key2867, 2)]

def rawRow16021 : Integer.Sparse Key := [(key2949, 2), (key2959, 2), (key2949, 2), (key2973, -1), (key2982, -1), (key2937, -1), (key2982, -1), (key2937, -1), (key2973, -1), (key2736, 2), (key2746, 2), (key2736, 2), (key2894, -1), (key2903, -1), (key2647, -1), (key2903, -1), (key2647, -1), (key2894, -1), (key2703, -1), (key2723, -1), (key2668, -1), (key2723, -1), (key2668, -1), (key2703, -1), (key2806, -1), (key2826, -1), (key2613, -1), (key2826, -1), (key2613, -1), (key2806, -1), (key2783, 2), (key2867, 2), (key2629, 2), (key2867, 2), (key2629, 2), (key2783, 2)]

def rawRow16022 : Integer.Sparse Key := [(key2959, 2), (key2949, 2), (key2949, 2), (key2982, -1), (key2973, -1), (key2982, -1), (key2937, -1), (key2973, -1), (key2937, -1), (key2746, 2), (key2736, 2), (key2736, 2), (key2903, -1), (key2894, -1), (key2903, -1), (key2647, -1), (key2894, -1), (key2647, -1), (key2723, -1), (key2703, -1), (key2723, -1), (key2668, -1), (key2703, -1), (key2668, -1), (key2826, -1), (key2806, -1), (key2826, -1), (key2613, -1), (key2806, -1), (key2613, -1), (key2867, 2), (key2783, 2), (key2867, 2), (key2629, 2), (key2783, 2), (key2629, 2)]

def rawRow16023 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, -1), (key2647, -1), (key2637, -1), (key2652, -1), (key2613, 2), (key2629, 2), (key2647, 2), (key2664, 1), (key2668, 1), (key2779, 1), (key2937, 1), (key2791, 1), (key2942, 1), (key2668, -2), (key2783, -2), (key2937, -2), (key2802, -1), (key2806, -1), (key2852, -1), (key2894, -1), (key2857, -1), (key2896, -1), (key2699, 1), (key2703, 1), (key2852, 1), (key2973, 1), (key2857, 1), (key2975, 1), (key2826, 2), (key2867, 2), (key2903, 2), (key2723, -2), (key2867, -2), (key2982, -2)]

def rawRow16024 : Integer.Sparse Key := [(key2613, -1), (key2609, -1), (key2647, -1), (key2625, -1), (key2652, -1), (key2637, -1), (key2613, 2), (key2647, 2), (key2629, 2), (key2668, 1), (key2664, 1), (key2937, 1), (key2779, 1), (key2942, 1), (key2791, 1), (key2668, -2), (key2937, -2), (key2783, -2), (key2806, -1), (key2802, -1), (key2894, -1), (key2852, -1), (key2896, -1), (key2857, -1), (key2703, 1), (key2699, 1), (key2973, 1), (key2852, 1), (key2975, 1), (key2857, 1), (key2826, 2), (key2903, 2), (key2867, 2), (key2723, -2), (key2982, -2), (key2867, -2)]

def rawRow16025 : Integer.Sparse Key := [(key2625, -1), (key2637, -1), (key2609, -1), (key2652, -1), (key2613, -1), (key2647, -1), (key2629, 2), (key2613, 2), (key2647, 2), (key2779, 1), (key2791, 1), (key2664, 1), (key2942, 1), (key2668, 1), (key2937, 1), (key2783, -2), (key2668, -2), (key2937, -2), (key2852, -1), (key2857, -1), (key2802, -1), (key2896, -1), (key2806, -1), (key2894, -1), (key2852, 1), (key2857, 1), (key2699, 1), (key2975, 1), (key2703, 1), (key2973, 1), (key2867, 2), (key2826, 2), (key2903, 2), (key2867, -2), (key2723, -2), (key2982, -2)]

def rawRow16026 : Integer.Sparse Key := [(key2637, -1), (key2625, -1), (key2652, -1), (key2609, -1), (key2647, -1), (key2613, -1), (key2629, 2), (key2647, 2), (key2613, 2), (key2791, 1), (key2779, 1), (key2942, 1), (key2664, 1), (key2937, 1), (key2668, 1), (key2783, -2), (key2937, -2), (key2668, -2), (key2857, -1), (key2852, -1), (key2896, -1), (key2802, -1), (key2894, -1), (key2806, -1), (key2857, 1), (key2852, 1), (key2975, 1), (key2699, 1), (key2973, 1), (key2703, 1), (key2867, 2), (key2903, 2), (key2826, 2), (key2867, -2), (key2982, -2), (key2723, -2)]

def rawRow16027 : Integer.Sparse Key := [(key2647, -1), (key2652, -1), (key2613, -1), (key2637, -1), (key2609, -1), (key2625, -1), (key2647, 2), (key2613, 2), (key2629, 2), (key2937, 1), (key2942, 1), (key2668, 1), (key2791, 1), (key2664, 1), (key2779, 1), (key2937, -2), (key2668, -2), (key2783, -2), (key2894, -1), (key2896, -1), (key2806, -1), (key2857, -1), (key2802, -1), (key2852, -1), (key2973, 1), (key2975, 1), (key2703, 1), (key2857, 1), (key2699, 1), (key2852, 1), (key2903, 2), (key2826, 2), (key2867, 2), (key2982, -2), (key2723, -2), (key2867, -2)]

def rawRow16028 : Integer.Sparse Key := [(key2652, -1), (key2647, -1), (key2637, -1), (key2613, -1), (key2625, -1), (key2609, -1), (key2647, 2), (key2629, 2), (key2613, 2), (key2942, 1), (key2937, 1), (key2791, 1), (key2668, 1), (key2779, 1), (key2664, 1), (key2937, -2), (key2783, -2), (key2668, -2), (key2896, -1), (key2894, -1), (key2857, -1), (key2806, -1), (key2852, -1), (key2802, -1), (key2975, 1), (key2973, 1), (key2857, 1), (key2703, 1), (key2852, 1), (key2699, 1), (key2903, 2), (key2867, 2), (key2826, 2), (key2982, -2), (key2867, -2), (key2723, -2)]

def rawRow16029 : Integer.Sparse Key := [(key2613, -1), (key2613, -1), (key2629, -1), (key2629, -1), (key2637, -1), (key2637, -1), (key2609, 2), (key2625, 2), (key2625, 2), (key2668, 1), (key2668, 1), (key2783, 1), (key2783, 1), (key2791, 1), (key2791, 1), (key2664, -2), (key2779, -2), (key2779, -2), (key2949, -1), (key2949, -1), (key2973, -1), (key2973, -1), (key2975, -1), (key2975, -1), (key2736, 1), (key2736, 1), (key2894, 1), (key2894, 1), (key2896, 1), (key2896, 1), (key2959, 2), (key2982, 2), (key2982, 2), (key2746, -2), (key2903, -2), (key2903, -2)]

def rawRow16030 : Integer.Sparse Key := [(key2629, -1), (key2637, -1), (key2613, -1), (key2637, -1), (key2613, -1), (key2629, -1), (key2625, 2), (key2609, 2), (key2625, 2), (key2783, 1), (key2791, 1), (key2668, 1), (key2791, 1), (key2668, 1), (key2783, 1), (key2779, -2), (key2664, -2), (key2779, -2), (key2973, -1), (key2975, -1), (key2949, -1), (key2975, -1), (key2949, -1), (key2973, -1), (key2894, 1), (key2896, 1), (key2736, 1), (key2896, 1), (key2736, 1), (key2894, 1), (key2982, 2), (key2959, 2), (key2982, 2), (key2903, -2), (key2746, -2), (key2903, -2)]

def rawRow16031 : Integer.Sparse Key := [(key2637, -1), (key2629, -1), (key2637, -1), (key2613, -1), (key2629, -1), (key2613, -1), (key2625, 2), (key2625, 2), (key2609, 2), (key2791, 1), (key2783, 1), (key2791, 1), (key2668, 1), (key2783, 1), (key2668, 1), (key2779, -2), (key2779, -2), (key2664, -2), (key2975, -1), (key2973, -1), (key2975, -1), (key2949, -1), (key2973, -1), (key2949, -1), (key2896, 1), (key2894, 1), (key2896, 1), (key2736, 1), (key2894, 1), (key2736, 1), (key2982, 2), (key2982, 2), (key2959, 2), (key2903, -2), (key2903, -2), (key2746, -2)]

def rawRow16032 : Integer.Sparse Key := [(key2664, -1), (key2668, -1), (key2699, -1), (key2736, -1), (key2723, -1), (key2746, -1), (key2668, 2), (key2703, 2), (key2736, 2), (key2609, 1), (key2613, 1), (key2802, 1), (key2949, 1), (key2826, 1), (key2959, 1), (key2613, -2), (key2806, -2), (key2949, -2), (key2779, -1), (key2783, -1), (key2852, -1), (key2894, -1), (key2867, -1), (key2903, -1), (key2625, 1), (key2629, 1), (key2852, 1), (key2973, 1), (key2867, 1), (key2982, 1), (key2791, 2), (key2857, 2), (key2896, 2), (key2637, -2), (key2857, -2), (key2975, -2)]

def rawRow16033 : Integer.Sparse Key := [(key2668, -1), (key2664, -1), (key2736, -1), (key2699, -1), (key2746, -1), (key2723, -1), (key2668, 2), (key2736, 2), (key2703, 2), (key2613, 1), (key2609, 1), (key2949, 1), (key2802, 1), (key2959, 1), (key2826, 1), (key2613, -2), (key2949, -2), (key2806, -2), (key2783, -1), (key2779, -1), (key2894, -1), (key2852, -1), (key2903, -1), (key2867, -1), (key2629, 1), (key2625, 1), (key2973, 1), (key2852, 1), (key2982, 1), (key2867, 1), (key2791, 2), (key2896, 2), (key2857, 2), (key2637, -2), (key2975, -2), (key2857, -2)]

def rawRow16034 : Integer.Sparse Key := [(key2699, -1), (key2723, -1), (key2664, -1), (key2746, -1), (key2668, -1), (key2736, -1), (key2703, 2), (key2668, 2), (key2736, 2), (key2802, 1), (key2826, 1), (key2609, 1), (key2959, 1), (key2613, 1), (key2949, 1), (key2806, -2), (key2613, -2), (key2949, -2), (key2852, -1), (key2867, -1), (key2779, -1), (key2903, -1), (key2783, -1), (key2894, -1), (key2852, 1), (key2867, 1), (key2625, 1), (key2982, 1), (key2629, 1), (key2973, 1), (key2857, 2), (key2791, 2), (key2896, 2), (key2857, -2), (key2637, -2), (key2975, -2)]

def rawRow16035 : Integer.Sparse Key := [(key2723, -1), (key2699, -1), (key2746, -1), (key2664, -1), (key2736, -1), (key2668, -1), (key2703, 2), (key2736, 2), (key2668, 2), (key2826, 1), (key2802, 1), (key2959, 1), (key2609, 1), (key2949, 1), (key2613, 1), (key2806, -2), (key2949, -2), (key2613, -2), (key2867, -1), (key2852, -1), (key2903, -1), (key2779, -1), (key2894, -1), (key2783, -1), (key2867, 1), (key2852, 1), (key2982, 1), (key2625, 1), (key2973, 1), (key2629, 1), (key2857, 2), (key2896, 2), (key2791, 2), (key2857, -2), (key2975, -2), (key2637, -2)]

def rawRow16036 : Integer.Sparse Key := [(key2736, -1), (key2746, -1), (key2668, -1), (key2723, -1), (key2664, -1), (key2699, -1), (key2736, 2), (key2668, 2), (key2703, 2), (key2949, 1), (key2959, 1), (key2613, 1), (key2826, 1), (key2609, 1), (key2802, 1), (key2949, -2), (key2613, -2), (key2806, -2), (key2894, -1), (key2903, -1), (key2783, -1), (key2867, -1), (key2779, -1), (key2852, -1), (key2973, 1), (key2982, 1), (key2629, 1), (key2867, 1), (key2625, 1), (key2852, 1), (key2896, 2), (key2791, 2), (key2857, 2), (key2975, -2), (key2637, -2), (key2857, -2)]

def rawRow16037 : Integer.Sparse Key := [(key2746, -1), (key2736, -1), (key2723, -1), (key2668, -1), (key2699, -1), (key2664, -1), (key2736, 2), (key2703, 2), (key2668, 2), (key2959, 1), (key2949, 1), (key2826, 1), (key2613, 1), (key2802, 1), (key2609, 1), (key2949, -2), (key2806, -2), (key2613, -2), (key2903, -1), (key2894, -1), (key2867, -1), (key2783, -1), (key2852, -1), (key2779, -1), (key2982, 1), (key2973, 1), (key2867, 1), (key2629, 1), (key2852, 1), (key2625, 1), (key2896, 2), (key2857, 2), (key2791, 2), (key2975, -2), (key2857, -2), (key2637, -2)]

def rawRow16038 : Integer.Sparse Key := [(key2668, -1), (key2668, -1), (key2703, -1), (key2703, -1), (key2723, -1), (key2723, -1), (key2664, 2), (key2699, 2), (key2699, 2), (key2613, 1), (key2613, 1), (key2806, 1), (key2806, 1), (key2826, 1), (key2826, 1), (key2609, -2), (key2802, -2), (key2802, -2), (key2937, -1), (key2937, -1), (key2973, -1), (key2973, -1), (key2982, -1), (key2982, -1), (key2647, 1), (key2647, 1), (key2894, 1), (key2894, 1), (key2903, 1), (key2903, 1), (key2942, 2), (key2975, 2), (key2975, 2), (key2652, -2), (key2896, -2), (key2896, -2)]

def rawRow16039 : Integer.Sparse Key := [(key2703, -1), (key2723, -1), (key2668, -1), (key2723, -1), (key2668, -1), (key2703, -1), (key2699, 2), (key2664, 2), (key2699, 2), (key2806, 1), (key2826, 1), (key2613, 1), (key2826, 1), (key2613, 1), (key2806, 1), (key2802, -2), (key2609, -2), (key2802, -2), (key2973, -1), (key2982, -1), (key2937, -1), (key2982, -1), (key2937, -1), (key2973, -1), (key2894, 1), (key2903, 1), (key2647, 1), (key2903, 1), (key2647, 1), (key2894, 1), (key2975, 2), (key2942, 2), (key2975, 2), (key2896, -2), (key2652, -2), (key2896, -2)]

def rawRow16040 : Integer.Sparse Key := [(key2723, -1), (key2703, -1), (key2723, -1), (key2668, -1), (key2703, -1), (key2668, -1), (key2699, 2), (key2699, 2), (key2664, 2), (key2826, 1), (key2806, 1), (key2826, 1), (key2613, 1), (key2806, 1), (key2613, 1), (key2802, -2), (key2802, -2), (key2609, -2), (key2982, -1), (key2973, -1), (key2982, -1), (key2937, -1), (key2973, -1), (key2937, -1), (key2903, 1), (key2894, 1), (key2903, 1), (key2647, 1), (key2894, 1), (key2647, 1), (key2975, 2), (key2975, 2), (key2942, 2), (key2896, -2), (key2896, -2), (key2652, -2)]

def rawRow16041 : Integer.Sparse Key := [(key2802, -1), (key2806, -1), (key2852, -1), (key2894, -1), (key2857, -1), (key2896, -1), (key2826, 2), (key2867, 2), (key2903, 2), (key2699, 1), (key2703, 1), (key2852, 1), (key2973, 1), (key2857, 1), (key2975, 1), (key2723, -2), (key2867, -2), (key2982, -2), (key2609, -1), (key2613, -1), (key2625, -1), (key2647, -1), (key2637, -1), (key2652, -1), (key2664, 1), (key2668, 1), (key2779, 1), (key2937, 1), (key2791, 1), (key2942, 1), (key2613, 2), (key2629, 2), (key2647, 2), (key2668, -2), (key2783, -2), (key2937, -2)]

def rawRow16042 : Integer.Sparse Key := [(key2806, -1), (key2802, -1), (key2894, -1), (key2852, -1), (key2896, -1), (key2857, -1), (key2826, 2), (key2903, 2), (key2867, 2), (key2703, 1), (key2699, 1), (key2973, 1), (key2852, 1), (key2975, 1), (key2857, 1), (key2723, -2), (key2982, -2), (key2867, -2), (key2613, -1), (key2609, -1), (key2647, -1), (key2625, -1), (key2652, -1), (key2637, -1), (key2668, 1), (key2664, 1), (key2937, 1), (key2779, 1), (key2942, 1), (key2791, 1), (key2613, 2), (key2647, 2), (key2629, 2), (key2668, -2), (key2937, -2), (key2783, -2)]

def rawRow16043 : Integer.Sparse Key := [(key2852, -1), (key2857, -1), (key2802, -1), (key2896, -1), (key2806, -1), (key2894, -1), (key2867, 2), (key2826, 2), (key2903, 2), (key2852, 1), (key2857, 1), (key2699, 1), (key2975, 1), (key2703, 1), (key2973, 1), (key2867, -2), (key2723, -2), (key2982, -2), (key2625, -1), (key2637, -1), (key2609, -1), (key2652, -1), (key2613, -1), (key2647, -1), (key2779, 1), (key2791, 1), (key2664, 1), (key2942, 1), (key2668, 1), (key2937, 1), (key2629, 2), (key2613, 2), (key2647, 2), (key2783, -2), (key2668, -2), (key2937, -2)]

def rawRow16044 : Integer.Sparse Key := [(key2857, -1), (key2852, -1), (key2896, -1), (key2802, -1), (key2894, -1), (key2806, -1), (key2867, 2), (key2903, 2), (key2826, 2), (key2857, 1), (key2852, 1), (key2975, 1), (key2699, 1), (key2973, 1), (key2703, 1), (key2867, -2), (key2982, -2), (key2723, -2), (key2637, -1), (key2625, -1), (key2652, -1), (key2609, -1), (key2647, -1), (key2613, -1), (key2791, 1), (key2779, 1), (key2942, 1), (key2664, 1), (key2937, 1), (key2668, 1), (key2629, 2), (key2647, 2), (key2613, 2), (key2783, -2), (key2937, -2), (key2668, -2)]

def rawRow16045 : Integer.Sparse Key := [(key2894, -1), (key2896, -1), (key2806, -1), (key2857, -1), (key2802, -1), (key2852, -1), (key2903, 2), (key2826, 2), (key2867, 2), (key2973, 1), (key2975, 1), (key2703, 1), (key2857, 1), (key2699, 1), (key2852, 1), (key2982, -2), (key2723, -2), (key2867, -2), (key2647, -1), (key2652, -1), (key2613, -1), (key2637, -1), (key2609, -1), (key2625, -1), (key2937, 1), (key2942, 1), (key2668, 1), (key2791, 1), (key2664, 1), (key2779, 1), (key2647, 2), (key2613, 2), (key2629, 2), (key2937, -2), (key2668, -2), (key2783, -2)]

def rawRow16046 : Integer.Sparse Key := [(key2896, -1), (key2894, -1), (key2857, -1), (key2806, -1), (key2852, -1), (key2802, -1), (key2903, 2), (key2867, 2), (key2826, 2), (key2975, 1), (key2973, 1), (key2857, 1), (key2703, 1), (key2852, 1), (key2699, 1), (key2982, -2), (key2867, -2), (key2723, -2), (key2652, -1), (key2647, -1), (key2637, -1), (key2613, -1), (key2625, -1), (key2609, -1), (key2942, 1), (key2937, 1), (key2791, 1), (key2668, 1), (key2779, 1), (key2664, 1), (key2647, 2), (key2629, 2), (key2613, 2), (key2937, -2), (key2783, -2), (key2668, -2)]

def rawRow16047 : Integer.Sparse Key := [(key2779, -1), (key2783, -1), (key2852, -1), (key2894, -1), (key2867, -1), (key2903, -1), (key2791, 2), (key2857, 2), (key2896, 2), (key2625, 1), (key2629, 1), (key2852, 1), (key2973, 1), (key2867, 1), (key2982, 1), (key2637, -2), (key2857, -2), (key2975, -2), (key2664, -1), (key2668, -1), (key2699, -1), (key2736, -1), (key2723, -1), (key2746, -1), (key2609, 1), (key2613, 1), (key2802, 1), (key2949, 1), (key2826, 1), (key2959, 1), (key2668, 2), (key2703, 2), (key2736, 2), (key2613, -2), (key2806, -2), (key2949, -2)]

def rawRow16048 : Integer.Sparse Key := [(key2783, -1), (key2779, -1), (key2894, -1), (key2852, -1), (key2903, -1), (key2867, -1), (key2791, 2), (key2896, 2), (key2857, 2), (key2629, 1), (key2625, 1), (key2973, 1), (key2852, 1), (key2982, 1), (key2867, 1), (key2637, -2), (key2975, -2), (key2857, -2), (key2668, -1), (key2664, -1), (key2736, -1), (key2699, -1), (key2746, -1), (key2723, -1), (key2613, 1), (key2609, 1), (key2949, 1), (key2802, 1), (key2959, 1), (key2826, 1), (key2668, 2), (key2736, 2), (key2703, 2), (key2613, -2), (key2949, -2), (key2806, -2)]

def rawRow16049 : Integer.Sparse Key := [(key2852, -1), (key2867, -1), (key2779, -1), (key2903, -1), (key2783, -1), (key2894, -1), (key2857, 2), (key2791, 2), (key2896, 2), (key2852, 1), (key2867, 1), (key2625, 1), (key2982, 1), (key2629, 1), (key2973, 1), (key2857, -2), (key2637, -2), (key2975, -2), (key2699, -1), (key2723, -1), (key2664, -1), (key2746, -1), (key2668, -1), (key2736, -1), (key2802, 1), (key2826, 1), (key2609, 1), (key2959, 1), (key2613, 1), (key2949, 1), (key2703, 2), (key2668, 2), (key2736, 2), (key2806, -2), (key2613, -2), (key2949, -2)]

def rawRow16050 : Integer.Sparse Key := [(key2867, -1), (key2852, -1), (key2903, -1), (key2779, -1), (key2894, -1), (key2783, -1), (key2857, 2), (key2896, 2), (key2791, 2), (key2867, 1), (key2852, 1), (key2982, 1), (key2625, 1), (key2973, 1), (key2629, 1), (key2857, -2), (key2975, -2), (key2637, -2), (key2723, -1), (key2699, -1), (key2746, -1), (key2664, -1), (key2736, -1), (key2668, -1), (key2826, 1), (key2802, 1), (key2959, 1), (key2609, 1), (key2949, 1), (key2613, 1), (key2703, 2), (key2736, 2), (key2668, 2), (key2806, -2), (key2949, -2), (key2613, -2)]

def rawRow16051 : Integer.Sparse Key := [(key2894, -1), (key2903, -1), (key2783, -1), (key2867, -1), (key2779, -1), (key2852, -1), (key2896, 2), (key2791, 2), (key2857, 2), (key2973, 1), (key2982, 1), (key2629, 1), (key2867, 1), (key2625, 1), (key2852, 1), (key2975, -2), (key2637, -2), (key2857, -2), (key2736, -1), (key2746, -1), (key2668, -1), (key2723, -1), (key2664, -1), (key2699, -1), (key2949, 1), (key2959, 1), (key2613, 1), (key2826, 1), (key2609, 1), (key2802, 1), (key2736, 2), (key2668, 2), (key2703, 2), (key2949, -2), (key2613, -2), (key2806, -2)]

def rawRow16052 : Integer.Sparse Key := [(key2903, -1), (key2894, -1), (key2867, -1), (key2783, -1), (key2852, -1), (key2779, -1), (key2896, 2), (key2857, 2), (key2791, 2), (key2982, 1), (key2973, 1), (key2867, 1), (key2629, 1), (key2852, 1), (key2625, 1), (key2975, -2), (key2857, -2), (key2637, -2), (key2746, -1), (key2736, -1), (key2723, -1), (key2668, -1), (key2699, -1), (key2664, -1), (key2959, 1), (key2949, 1), (key2826, 1), (key2613, 1), (key2802, 1), (key2609, 1), (key2736, 2), (key2703, 2), (key2668, 2), (key2949, -2), (key2806, -2), (key2613, -2)]

def rawRow16053 : Integer.Sparse Key := [(key2949, -1), (key2949, -1), (key2973, -1), (key2973, -1), (key2975, -1), (key2975, -1), (key2959, 2), (key2982, 2), (key2982, 2), (key2736, 1), (key2736, 1), (key2894, 1), (key2894, 1), (key2896, 1), (key2896, 1), (key2746, -2), (key2903, -2), (key2903, -2), (key2613, -1), (key2613, -1), (key2629, -1), (key2629, -1), (key2637, -1), (key2637, -1), (key2668, 1), (key2668, 1), (key2783, 1), (key2783, 1), (key2791, 1), (key2791, 1), (key2609, 2), (key2625, 2), (key2625, 2), (key2664, -2), (key2779, -2), (key2779, -2)]

def rawRow16054 : Integer.Sparse Key := [(key2973, -1), (key2975, -1), (key2949, -1), (key2975, -1), (key2949, -1), (key2973, -1), (key2982, 2), (key2959, 2), (key2982, 2), (key2894, 1), (key2896, 1), (key2736, 1), (key2896, 1), (key2736, 1), (key2894, 1), (key2903, -2), (key2746, -2), (key2903, -2), (key2629, -1), (key2637, -1), (key2613, -1), (key2637, -1), (key2613, -1), (key2629, -1), (key2783, 1), (key2791, 1), (key2668, 1), (key2791, 1), (key2668, 1), (key2783, 1), (key2625, 2), (key2609, 2), (key2625, 2), (key2779, -2), (key2664, -2), (key2779, -2)]

def rawRow16055 : Integer.Sparse Key := [(key2975, -1), (key2973, -1), (key2975, -1), (key2949, -1), (key2973, -1), (key2949, -1), (key2982, 2), (key2982, 2), (key2959, 2), (key2896, 1), (key2894, 1), (key2896, 1), (key2736, 1), (key2894, 1), (key2736, 1), (key2903, -2), (key2903, -2), (key2746, -2), (key2637, -1), (key2629, -1), (key2637, -1), (key2613, -1), (key2629, -1), (key2613, -1), (key2791, 1), (key2783, 1), (key2791, 1), (key2668, 1), (key2783, 1), (key2668, 1), (key2625, 2), (key2625, 2), (key2609, 2), (key2779, -2), (key2779, -2), (key2664, -2)]

def rawRow16056 : Integer.Sparse Key := [(key2937, -1), (key2937, -1), (key2973, -1), (key2973, -1), (key2982, -1), (key2982, -1), (key2942, 2), (key2975, 2), (key2975, 2), (key2647, 1), (key2647, 1), (key2894, 1), (key2894, 1), (key2903, 1), (key2903, 1), (key2652, -2), (key2896, -2), (key2896, -2), (key2668, -1), (key2668, -1), (key2703, -1), (key2703, -1), (key2723, -1), (key2723, -1), (key2613, 1), (key2613, 1), (key2806, 1), (key2806, 1), (key2826, 1), (key2826, 1), (key2664, 2), (key2699, 2), (key2699, 2), (key2609, -2), (key2802, -2), (key2802, -2)]

def rawRow16057 : Integer.Sparse Key := [(key2973, -1), (key2982, -1), (key2937, -1), (key2982, -1), (key2937, -1), (key2973, -1), (key2975, 2), (key2942, 2), (key2975, 2), (key2894, 1), (key2903, 1), (key2647, 1), (key2903, 1), (key2647, 1), (key2894, 1), (key2896, -2), (key2652, -2), (key2896, -2), (key2703, -1), (key2723, -1), (key2668, -1), (key2723, -1), (key2668, -1), (key2703, -1), (key2806, 1), (key2826, 1), (key2613, 1), (key2826, 1), (key2613, 1), (key2806, 1), (key2699, 2), (key2664, 2), (key2699, 2), (key2802, -2), (key2609, -2), (key2802, -2)]

def rawRow16058 : Integer.Sparse Key := [(key2982, -1), (key2973, -1), (key2982, -1), (key2937, -1), (key2973, -1), (key2937, -1), (key2975, 2), (key2975, 2), (key2942, 2), (key2903, 1), (key2894, 1), (key2903, 1), (key2647, 1), (key2894, 1), (key2647, 1), (key2896, -2), (key2896, -2), (key2652, -2), (key2723, -1), (key2703, -1), (key2723, -1), (key2668, -1), (key2703, -1), (key2668, -1), (key2826, 1), (key2806, 1), (key2826, 1), (key2613, 1), (key2806, 1), (key2613, 1), (key2699, 2), (key2699, 2), (key2664, 2), (key2802, -2), (key2802, -2), (key2609, -2)]

def rawRow16059 : Integer.Sparse Key := [(key2608, -1), (key2611, -1), (key2624, -1), (key2636, -1), (key2645, -1), (key2651, -1), (key2611, 2), (key2627, 2), (key2636, 2), (key2663, 1), (key2666, 1), (key2698, 1), (key2722, 1), (key2734, 1), (key2745, 1), (key2666, -2), (key2701, -2), (key2722, -2), (key2801, -1), (key2804, -1), (key2851, -1), (key2856, -1), (key2892, -1), (key2895, -1), (key2778, 1), (key2781, 1), (key2851, 1), (key2866, 1), (key2892, 1), (key2902, 1), (key2947, 2), (key2971, 2), (key2974, 2), (key2935, -2), (key2971, -2), (key2981, -2)]

def rawRow16060 : Integer.Sparse Key := [(key2611, -1), (key2608, -1), (key2636, -1), (key2624, -1), (key2651, -1), (key2645, -1), (key2611, 2), (key2636, 2), (key2627, 2), (key2666, 1), (key2663, 1), (key2722, 1), (key2698, 1), (key2745, 1), (key2734, 1), (key2666, -2), (key2722, -2), (key2701, -2), (key2804, -1), (key2801, -1), (key2856, -1), (key2851, -1), (key2895, -1), (key2892, -1), (key2781, 1), (key2778, 1), (key2866, 1), (key2851, 1), (key2902, 1), (key2892, 1), (key2947, 2), (key2974, 2), (key2971, 2), (key2935, -2), (key2981, -2), (key2971, -2)]

def rawRow16061 : Integer.Sparse Key := [(key2624, -1), (key2636, -1), (key2608, -1), (key2651, -1), (key2611, -1), (key2636, -1), (key2627, 2), (key2611, 2), (key2636, 2), (key2698, 1), (key2734, 1), (key2663, 1), (key2745, 1), (key2666, 1), (key2722, 1), (key2701, -2), (key2666, -2), (key2722, -2), (key2851, -1), (key2892, -1), (key2801, -1), (key2895, -1), (key2804, -1), (key2856, -1), (key2851, 1), (key2892, 1), (key2778, 1), (key2902, 1), (key2781, 1), (key2866, 1), (key2971, 2), (key2947, 2), (key2974, 2), (key2971, -2), (key2935, -2), (key2981, -2)]

def rawRow16062 : Integer.Sparse Key := [(key2636, -1), (key2624, -1), (key2651, -1), (key2608, -1), (key2636, -1), (key2611, -1), (key2627, 2), (key2636, 2), (key2611, 2), (key2734, 1), (key2698, 1), (key2745, 1), (key2663, 1), (key2722, 1), (key2666, 1), (key2701, -2), (key2722, -2), (key2666, -2), (key2892, -1), (key2851, -1), (key2895, -1), (key2801, -1), (key2856, -1), (key2804, -1), (key2892, 1), (key2851, 1), (key2902, 1), (key2778, 1), (key2866, 1), (key2781, 1), (key2971, 2), (key2974, 2), (key2947, 2), (key2971, -2), (key2981, -2), (key2935, -2)]

def rawRow16063 : Integer.Sparse Key := [(key2645, -1), (key2651, -1), (key2611, -1), (key2636, -1), (key2608, -1), (key2624, -1), (key2636, 2), (key2611, 2), (key2627, 2), (key2722, 1), (key2745, 1), (key2666, 1), (key2734, 1), (key2663, 1), (key2698, 1), (key2722, -2), (key2666, -2), (key2701, -2), (key2856, -1), (key2895, -1), (key2804, -1), (key2892, -1), (key2801, -1), (key2851, -1), (key2866, 1), (key2902, 1), (key2781, 1), (key2892, 1), (key2778, 1), (key2851, 1), (key2974, 2), (key2947, 2), (key2971, 2), (key2981, -2), (key2935, -2), (key2971, -2)]

def rawRow16064 : Integer.Sparse Key := [(key2651, -1), (key2645, -1), (key2636, -1), (key2611, -1), (key2624, -1), (key2608, -1), (key2636, 2), (key2627, 2), (key2611, 2), (key2745, 1), (key2722, 1), (key2734, 1), (key2666, 1), (key2698, 1), (key2663, 1), (key2722, -2), (key2701, -2), (key2666, -2), (key2895, -1), (key2856, -1), (key2892, -1), (key2804, -1), (key2851, -1), (key2801, -1), (key2902, 1), (key2866, 1), (key2892, 1), (key2781, 1), (key2851, 1), (key2778, 1), (key2974, 2), (key2971, 2), (key2947, 2), (key2981, -2), (key2971, -2), (key2935, -2)]

def rawRow16065 : Integer.Sparse Key := [(key2611, -1), (key2611, -1), (key2627, -1), (key2627, -1), (key2636, -1), (key2636, -1), (key2608, 2), (key2624, 2), (key2624, 2), (key2666, 1), (key2666, 1), (key2701, 1), (key2701, 1), (key2734, 1), (key2734, 1), (key2663, -2), (key2698, -2), (key2698, -2), (key2825, -1), (key2825, -1), (key2866, -1), (key2866, -1), (key2902, -1), (key2902, -1), (key2790, 1), (key2790, 1), (key2856, 1), (key2856, 1), (key2895, 1), (key2895, 1), (key2958, 2), (key2981, 2), (key2981, 2), (key2941, -2), (key2974, -2), (key2974, -2)]

def rawRow16066 : Integer.Sparse Key := [(key2627, -1), (key2636, -1), (key2611, -1), (key2636, -1), (key2611, -1), (key2627, -1), (key2624, 2), (key2608, 2), (key2624, 2), (key2701, 1), (key2734, 1), (key2666, 1), (key2734, 1), (key2666, 1), (key2701, 1), (key2698, -2), (key2663, -2), (key2698, -2), (key2866, -1), (key2902, -1), (key2825, -1), (key2902, -1), (key2825, -1), (key2866, -1), (key2856, 1), (key2895, 1), (key2790, 1), (key2895, 1), (key2790, 1), (key2856, 1), (key2981, 2), (key2958, 2), (key2981, 2), (key2974, -2), (key2941, -2), (key2974, -2)]

def rawRow16067 : Integer.Sparse Key := [(key2636, -1), (key2627, -1), (key2636, -1), (key2611, -1), (key2627, -1), (key2611, -1), (key2624, 2), (key2624, 2), (key2608, 2), (key2734, 1), (key2701, 1), (key2734, 1), (key2666, 1), (key2701, 1), (key2666, 1), (key2698, -2), (key2698, -2), (key2663, -2), (key2902, -1), (key2866, -1), (key2902, -1), (key2825, -1), (key2866, -1), (key2825, -1), (key2895, 1), (key2856, 1), (key2895, 1), (key2790, 1), (key2856, 1), (key2790, 1), (key2981, 2), (key2981, 2), (key2958, 2), (key2974, -2), (key2974, -2), (key2941, -2)]

def rawRow16068 : Integer.Sparse Key := [(key2663, -1), (key2666, -1), (key2698, -1), (key2734, -1), (key2722, -1), (key2745, -1), (key2666, 2), (key2701, 2), (key2734, 2), (key2608, 1), (key2611, 1), (key2801, 1), (key2825, 1), (key2947, 1), (key2958, 1), (key2611, -2), (key2804, -2), (key2825, -2), (key2698, -1), (key2701, -1), (key2851, -1), (key2856, -1), (key2971, -1), (key2974, -1), (key2624, 1), (key2627, 1), (key2851, 1), (key2866, 1), (key2971, 1), (key2981, 1), (key2734, 2), (key2892, 2), (key2895, 2), (key2645, -2), (key2892, -2), (key2902, -2)]

def rawRow16069 : Integer.Sparse Key := [(key2666, -1), (key2663, -1), (key2734, -1), (key2698, -1), (key2745, -1), (key2722, -1), (key2666, 2), (key2734, 2), (key2701, 2), (key2611, 1), (key2608, 1), (key2825, 1), (key2801, 1), (key2958, 1), (key2947, 1), (key2611, -2), (key2825, -2), (key2804, -2), (key2701, -1), (key2698, -1), (key2856, -1), (key2851, -1), (key2974, -1), (key2971, -1), (key2627, 1), (key2624, 1), (key2866, 1), (key2851, 1), (key2981, 1), (key2971, 1), (key2734, 2), (key2895, 2), (key2892, 2), (key2645, -2), (key2902, -2), (key2892, -2)]

def rawRow16070 : Integer.Sparse Key := [(key2698, -1), (key2722, -1), (key2663, -1), (key2745, -1), (key2666, -1), (key2734, -1), (key2701, 2), (key2666, 2), (key2734, 2), (key2801, 1), (key2825, 1), (key2608, 1), (key2958, 1), (key2611, 1), (key2825, 1), (key2804, -2), (key2611, -2), (key2825, -2), (key2851, -1), (key2971, -1), (key2698, -1), (key2974, -1), (key2701, -1), (key2856, -1), (key2851, 1), (key2971, 1), (key2624, 1), (key2981, 1), (key2627, 1), (key2866, 1), (key2892, 2), (key2734, 2), (key2895, 2), (key2892, -2), (key2645, -2), (key2902, -2)]

def rawRow16071 : Integer.Sparse Key := [(key2722, -1), (key2698, -1), (key2745, -1), (key2663, -1), (key2734, -1), (key2666, -1), (key2701, 2), (key2734, 2), (key2666, 2), (key2825, 1), (key2801, 1), (key2958, 1), (key2608, 1), (key2825, 1), (key2611, 1), (key2804, -2), (key2825, -2), (key2611, -2), (key2971, -1), (key2851, -1), (key2974, -1), (key2698, -1), (key2856, -1), (key2701, -1), (key2971, 1), (key2851, 1), (key2981, 1), (key2624, 1), (key2866, 1), (key2627, 1), (key2892, 2), (key2895, 2), (key2734, 2), (key2892, -2), (key2902, -2), (key2645, -2)]

def rawRow16072 : Integer.Sparse Key := [(key2734, -1), (key2745, -1), (key2666, -1), (key2722, -1), (key2663, -1), (key2698, -1), (key2734, 2), (key2666, 2), (key2701, 2), (key2947, 1), (key2958, 1), (key2611, 1), (key2825, 1), (key2608, 1), (key2801, 1), (key2825, -2), (key2611, -2), (key2804, -2), (key2856, -1), (key2974, -1), (key2701, -1), (key2971, -1), (key2698, -1), (key2851, -1), (key2866, 1), (key2981, 1), (key2627, 1), (key2971, 1), (key2624, 1), (key2851, 1), (key2895, 2), (key2734, 2), (key2892, 2), (key2902, -2), (key2645, -2), (key2892, -2)]

def rawRow16073 : Integer.Sparse Key := [(key2745, -1), (key2734, -1), (key2722, -1), (key2666, -1), (key2698, -1), (key2663, -1), (key2734, 2), (key2701, 2), (key2666, 2), (key2958, 1), (key2947, 1), (key2825, 1), (key2611, 1), (key2801, 1), (key2608, 1), (key2825, -2), (key2804, -2), (key2611, -2), (key2974, -1), (key2856, -1), (key2971, -1), (key2701, -1), (key2851, -1), (key2698, -1), (key2981, 1), (key2866, 1), (key2971, 1), (key2627, 1), (key2851, 1), (key2624, 1), (key2895, 2), (key2892, 2), (key2734, 2), (key2902, -2), (key2892, -2), (key2645, -2)]

def rawRow16074 : Integer.Sparse Key := [(key2666, -1), (key2666, -1), (key2701, -1), (key2701, -1), (key2722, -1), (key2722, -1), (key2663, 2), (key2698, 2), (key2698, 2), (key2611, 1), (key2611, 1), (key2804, 1), (key2804, 1), (key2825, 1), (key2825, 1), (key2608, -2), (key2801, -2), (key2801, -2), (key2722, -1), (key2722, -1), (key2866, -1), (key2866, -1), (key2981, -1), (key2981, -1), (key2636, 1), (key2636, 1), (key2856, 1), (key2856, 1), (key2974, 1), (key2974, 1), (key2745, 2), (key2902, 2), (key2902, 2), (key2651, -2), (key2895, -2), (key2895, -2)]

def rawRow16075 : Integer.Sparse Key := [(key2701, -1), (key2722, -1), (key2666, -1), (key2722, -1), (key2666, -1), (key2701, -1), (key2698, 2), (key2663, 2), (key2698, 2), (key2804, 1), (key2825, 1), (key2611, 1), (key2825, 1), (key2611, 1), (key2804, 1), (key2801, -2), (key2608, -2), (key2801, -2), (key2866, -1), (key2981, -1), (key2722, -1), (key2981, -1), (key2722, -1), (key2866, -1), (key2856, 1), (key2974, 1), (key2636, 1), (key2974, 1), (key2636, 1), (key2856, 1), (key2902, 2), (key2745, 2), (key2902, 2), (key2895, -2), (key2651, -2), (key2895, -2)]

def rawRow16076 : Integer.Sparse Key := [(key2722, -1), (key2701, -1), (key2722, -1), (key2666, -1), (key2701, -1), (key2666, -1), (key2698, 2), (key2698, 2), (key2663, 2), (key2825, 1), (key2804, 1), (key2825, 1), (key2611, 1), (key2804, 1), (key2611, 1), (key2801, -2), (key2801, -2), (key2608, -2), (key2981, -1), (key2866, -1), (key2981, -1), (key2722, -1), (key2866, -1), (key2722, -1), (key2974, 1), (key2856, 1), (key2974, 1), (key2636, 1), (key2856, 1), (key2636, 1), (key2902, 2), (key2902, 2), (key2745, 2), (key2895, -2), (key2895, -2), (key2651, -2)]

def rawRow16077 : Integer.Sparse Key := [(key2801, -1), (key2804, -1), (key2851, -1), (key2892, -1), (key2856, -1), (key2895, -1), (key2825, 2), (key2866, 2), (key2902, 2), (key2698, 1), (key2701, 1), (key2851, 1), (key2971, 1), (key2856, 1), (key2974, 1), (key2722, -2), (key2866, -2), (key2981, -2), (key2608, -1), (key2611, -1), (key2624, -1), (key2636, -1), (key2645, -1), (key2651, -1), (key2663, 1), (key2666, 1), (key2698, 1), (key2722, 1), (key2734, 1), (key2745, 1), (key2611, 2), (key2627, 2), (key2636, 2), (key2666, -2), (key2701, -2), (key2722, -2)]

def rawRow16078 : Integer.Sparse Key := [(key2804, -1), (key2801, -1), (key2892, -1), (key2851, -1), (key2895, -1), (key2856, -1), (key2825, 2), (key2902, 2), (key2866, 2), (key2701, 1), (key2698, 1), (key2971, 1), (key2851, 1), (key2974, 1), (key2856, 1), (key2722, -2), (key2981, -2), (key2866, -2), (key2611, -1), (key2608, -1), (key2636, -1), (key2624, -1), (key2651, -1), (key2645, -1), (key2666, 1), (key2663, 1), (key2722, 1), (key2698, 1), (key2745, 1), (key2734, 1), (key2611, 2), (key2636, 2), (key2627, 2), (key2666, -2), (key2722, -2), (key2701, -2)]

def rawRow16079 : Integer.Sparse Key := [(key2851, -1), (key2856, -1), (key2801, -1), (key2895, -1), (key2804, -1), (key2892, -1), (key2866, 2), (key2825, 2), (key2902, 2), (key2851, 1), (key2856, 1), (key2698, 1), (key2974, 1), (key2701, 1), (key2971, 1), (key2866, -2), (key2722, -2), (key2981, -2), (key2624, -1), (key2636, -1), (key2608, -1), (key2651, -1), (key2611, -1), (key2636, -1), (key2698, 1), (key2734, 1), (key2663, 1), (key2745, 1), (key2666, 1), (key2722, 1), (key2627, 2), (key2611, 2), (key2636, 2), (key2701, -2), (key2666, -2), (key2722, -2)]

def rawRow16080 : Integer.Sparse Key := [(key2856, -1), (key2851, -1), (key2895, -1), (key2801, -1), (key2892, -1), (key2804, -1), (key2866, 2), (key2902, 2), (key2825, 2), (key2856, 1), (key2851, 1), (key2974, 1), (key2698, 1), (key2971, 1), (key2701, 1), (key2866, -2), (key2981, -2), (key2722, -2), (key2636, -1), (key2624, -1), (key2651, -1), (key2608, -1), (key2636, -1), (key2611, -1), (key2734, 1), (key2698, 1), (key2745, 1), (key2663, 1), (key2722, 1), (key2666, 1), (key2627, 2), (key2636, 2), (key2611, 2), (key2701, -2), (key2722, -2), (key2666, -2)]

def rawRow16081 : Integer.Sparse Key := [(key2892, -1), (key2895, -1), (key2804, -1), (key2856, -1), (key2801, -1), (key2851, -1), (key2902, 2), (key2825, 2), (key2866, 2), (key2971, 1), (key2974, 1), (key2701, 1), (key2856, 1), (key2698, 1), (key2851, 1), (key2981, -2), (key2722, -2), (key2866, -2), (key2645, -1), (key2651, -1), (key2611, -1), (key2636, -1), (key2608, -1), (key2624, -1), (key2722, 1), (key2745, 1), (key2666, 1), (key2734, 1), (key2663, 1), (key2698, 1), (key2636, 2), (key2611, 2), (key2627, 2), (key2722, -2), (key2666, -2), (key2701, -2)]

def rawRow16082 : Integer.Sparse Key := [(key2895, -1), (key2892, -1), (key2856, -1), (key2804, -1), (key2851, -1), (key2801, -1), (key2902, 2), (key2866, 2), (key2825, 2), (key2974, 1), (key2971, 1), (key2856, 1), (key2701, 1), (key2851, 1), (key2698, 1), (key2981, -2), (key2866, -2), (key2722, -2), (key2651, -1), (key2645, -1), (key2636, -1), (key2611, -1), (key2624, -1), (key2608, -1), (key2745, 1), (key2722, 1), (key2734, 1), (key2666, 1), (key2698, 1), (key2663, 1), (key2636, 2), (key2627, 2), (key2611, 2), (key2722, -2), (key2701, -2), (key2666, -2)]

def rawRow16083 : Integer.Sparse Key := [(key2778, -1), (key2781, -1), (key2851, -1), (key2892, -1), (key2866, -1), (key2902, -1), (key2790, 2), (key2856, 2), (key2895, 2), (key2624, 1), (key2627, 1), (key2851, 1), (key2971, 1), (key2866, 1), (key2981, 1), (key2636, -2), (key2856, -2), (key2974, -2), (key2663, -1), (key2666, -1), (key2698, -1), (key2734, -1), (key2722, -1), (key2745, -1), (key2608, 1), (key2611, 1), (key2801, 1), (key2825, 1), (key2947, 1), (key2958, 1), (key2666, 2), (key2781, 2), (key2790, 2), (key2611, -2), (key2804, -2), (key2825, -2)]

def rawRow16084 : Integer.Sparse Key := [(key2781, -1), (key2778, -1), (key2892, -1), (key2851, -1), (key2902, -1), (key2866, -1), (key2790, 2), (key2895, 2), (key2856, 2), (key2627, 1), (key2624, 1), (key2971, 1), (key2851, 1), (key2981, 1), (key2866, 1), (key2636, -2), (key2974, -2), (key2856, -2), (key2666, -1), (key2663, -1), (key2734, -1), (key2698, -1), (key2745, -1), (key2722, -1), (key2611, 1), (key2608, 1), (key2825, 1), (key2801, 1), (key2958, 1), (key2947, 1), (key2666, 2), (key2790, 2), (key2781, 2), (key2611, -2), (key2825, -2), (key2804, -2)]

def rawRow16085 : Integer.Sparse Key := [(key2851, -1), (key2866, -1), (key2778, -1), (key2902, -1), (key2781, -1), (key2892, -1), (key2856, 2), (key2790, 2), (key2895, 2), (key2851, 1), (key2866, 1), (key2624, 1), (key2981, 1), (key2627, 1), (key2971, 1), (key2856, -2), (key2636, -2), (key2974, -2), (key2698, -1), (key2722, -1), (key2663, -1), (key2745, -1), (key2666, -1), (key2734, -1), (key2801, 1), (key2825, 1), (key2608, 1), (key2958, 1), (key2611, 1), (key2825, 1), (key2781, 2), (key2666, 2), (key2790, 2), (key2804, -2), (key2611, -2), (key2825, -2)]

def rawRow16086 : Integer.Sparse Key := [(key2866, -1), (key2851, -1), (key2902, -1), (key2778, -1), (key2892, -1), (key2781, -1), (key2856, 2), (key2895, 2), (key2790, 2), (key2866, 1), (key2851, 1), (key2981, 1), (key2624, 1), (key2971, 1), (key2627, 1), (key2856, -2), (key2974, -2), (key2636, -2), (key2722, -1), (key2698, -1), (key2745, -1), (key2663, -1), (key2734, -1), (key2666, -1), (key2825, 1), (key2801, 1), (key2958, 1), (key2608, 1), (key2825, 1), (key2611, 1), (key2781, 2), (key2790, 2), (key2666, 2), (key2804, -2), (key2825, -2), (key2611, -2)]

def rawRow16087 : Integer.Sparse Key := [(key2892, -1), (key2902, -1), (key2781, -1), (key2866, -1), (key2778, -1), (key2851, -1), (key2895, 2), (key2790, 2), (key2856, 2), (key2971, 1), (key2981, 1), (key2627, 1), (key2866, 1), (key2624, 1), (key2851, 1), (key2974, -2), (key2636, -2), (key2856, -2), (key2734, -1), (key2745, -1), (key2666, -1), (key2722, -1), (key2663, -1), (key2698, -1), (key2947, 1), (key2958, 1), (key2611, 1), (key2825, 1), (key2608, 1), (key2801, 1), (key2790, 2), (key2666, 2), (key2781, 2), (key2825, -2), (key2611, -2), (key2804, -2)]

def rawRow16088 : Integer.Sparse Key := [(key2902, -1), (key2892, -1), (key2866, -1), (key2781, -1), (key2851, -1), (key2778, -1), (key2895, 2), (key2856, 2), (key2790, 2), (key2981, 1), (key2971, 1), (key2866, 1), (key2627, 1), (key2851, 1), (key2624, 1), (key2974, -2), (key2856, -2), (key2636, -2), (key2745, -1), (key2734, -1), (key2722, -1), (key2666, -1), (key2698, -1), (key2663, -1), (key2958, 1), (key2947, 1), (key2825, 1), (key2611, 1), (key2801, 1), (key2608, 1), (key2790, 2), (key2781, 2), (key2666, 2), (key2825, -2), (key2804, -2), (key2611, -2)]

def rawRow16089 : Integer.Sparse Key := [(key2947, -1), (key2947, -1), (key2971, -1), (key2971, -1), (key2974, -1), (key2974, -1), (key2958, 2), (key2981, 2), (key2981, 2), (key2734, 1), (key2734, 1), (key2892, 1), (key2892, 1), (key2895, 1), (key2895, 1), (key2745, -2), (key2902, -2), (key2902, -2), (key2611, -1), (key2611, -1), (key2627, -1), (key2627, -1), (key2636, -1), (key2636, -1), (key2666, 1), (key2666, 1), (key2781, 1), (key2781, 1), (key2790, 1), (key2790, 1), (key2608, 2), (key2624, 2), (key2624, 2), (key2663, -2), (key2698, -2), (key2698, -2)]

def rawRow16090 : Integer.Sparse Key := [(key2971, -1), (key2974, -1), (key2947, -1), (key2974, -1), (key2947, -1), (key2971, -1), (key2981, 2), (key2958, 2), (key2981, 2), (key2892, 1), (key2895, 1), (key2734, 1), (key2895, 1), (key2734, 1), (key2892, 1), (key2902, -2), (key2745, -2), (key2902, -2), (key2627, -1), (key2636, -1), (key2611, -1), (key2636, -1), (key2611, -1), (key2627, -1), (key2781, 1), (key2790, 1), (key2666, 1), (key2790, 1), (key2666, 1), (key2781, 1), (key2624, 2), (key2608, 2), (key2624, 2), (key2698, -2), (key2663, -2), (key2698, -2)]

def rawRow16091 : Integer.Sparse Key := [(key2974, -1), (key2971, -1), (key2974, -1), (key2947, -1), (key2971, -1), (key2947, -1), (key2981, 2), (key2981, 2), (key2958, 2), (key2895, 1), (key2892, 1), (key2895, 1), (key2734, 1), (key2892, 1), (key2734, 1), (key2902, -2), (key2902, -2), (key2745, -2), (key2636, -1), (key2627, -1), (key2636, -1), (key2611, -1), (key2627, -1), (key2611, -1), (key2790, 1), (key2781, 1), (key2790, 1), (key2666, 1), (key2781, 1), (key2666, 1), (key2624, 2), (key2624, 2), (key2608, 2), (key2698, -2), (key2698, -2), (key2663, -2)]

def rawRow16092 : Integer.Sparse Key := [(key2935, -1), (key2935, -1), (key2971, -1), (key2971, -1), (key2981, -1), (key2981, -1), (key2941, 2), (key2974, 2), (key2974, 2), (key2645, 1), (key2645, 1), (key2892, 1), (key2892, 1), (key2902, 1), (key2902, 1), (key2651, -2), (key2895, -2), (key2895, -2), (key2666, -1), (key2666, -1), (key2701, -1), (key2701, -1), (key2722, -1), (key2722, -1), (key2611, 1), (key2611, 1), (key2804, 1), (key2804, 1), (key2825, 1), (key2825, 1), (key2663, 2), (key2698, 2), (key2698, 2), (key2608, -2), (key2801, -2), (key2801, -2)]

def rawRow16093 : Integer.Sparse Key := [(key2971, -1), (key2981, -1), (key2935, -1), (key2981, -1), (key2935, -1), (key2971, -1), (key2974, 2), (key2941, 2), (key2974, 2), (key2892, 1), (key2902, 1), (key2645, 1), (key2902, 1), (key2645, 1), (key2892, 1), (key2895, -2), (key2651, -2), (key2895, -2), (key2701, -1), (key2722, -1), (key2666, -1), (key2722, -1), (key2666, -1), (key2701, -1), (key2804, 1), (key2825, 1), (key2611, 1), (key2825, 1), (key2611, 1), (key2804, 1), (key2698, 2), (key2663, 2), (key2698, 2), (key2801, -2), (key2608, -2), (key2801, -2)]

def rawRow16094 : Integer.Sparse Key := [(key2981, -1), (key2971, -1), (key2981, -1), (key2935, -1), (key2971, -1), (key2935, -1), (key2974, 2), (key2974, 2), (key2941, 2), (key2902, 1), (key2892, 1), (key2902, 1), (key2645, 1), (key2892, 1), (key2645, 1), (key2895, -2), (key2895, -2), (key2651, -2), (key2722, -1), (key2701, -1), (key2722, -1), (key2666, -1), (key2701, -1), (key2666, -1), (key2825, 1), (key2804, 1), (key2825, 1), (key2611, 1), (key2804, 1), (key2611, 1), (key2698, 2), (key2698, 2), (key2663, 2), (key2801, -2), (key2801, -2), (key2608, -2)]

def rawRow16095 : Integer.Sparse Key := [(key2592, 4), (key2991, 4), (key2991, 4), (key2595, -2), (key2595, -2), (key2882, -2), (key2882, -2), (key2993, -2), (key2993, -2), (key2602, -2), (key2602, -2), (key2912, -2), (key2912, -2), (key3003, -2), (key3003, -2), (key2603, 4), (key2914, 4), (key2914, 4)]

def rawRow16096 : Integer.Sparse Key := [(key2991, 4), (key2592, 4), (key2991, 4), (key2882, -2), (key2993, -2), (key2595, -2), (key2993, -2), (key2595, -2), (key2882, -2), (key2912, -2), (key3003, -2), (key2602, -2), (key3003, -2), (key2602, -2), (key2912, -2), (key2914, 4), (key2603, 4), (key2914, 4)]

def rawRow16097 : Integer.Sparse Key := [(key2991, 4), (key2991, 4), (key2592, 4), (key2993, -2), (key2882, -2), (key2993, -2), (key2595, -2), (key2882, -2), (key2595, -2), (key3003, -2), (key2912, -2), (key3003, -2), (key2602, -2), (key2912, -2), (key2602, -2), (key2914, 4), (key2914, 4), (key2603, 4)]

def rawRow16098 : Integer.Sparse Key := [(key2595, 4), (key2970, 4), (key2993, 4), (key2592, -2), (key2595, -2), (key2848, -2), (key2882, -2), (key2970, -2), (key2991, -2), (key2602, -2), (key2603, -2), (key2891, -2), (key2914, -2), (key2996, -2), (key3003, -2), (key2602, 4), (key2891, 4), (key2912, 4)]

def rawRow16099 : Integer.Sparse Key := [(key2595, 4), (key2993, 4), (key2970, 4), (key2595, -2), (key2592, -2), (key2882, -2), (key2848, -2), (key2991, -2), (key2970, -2), (key2603, -2), (key2602, -2), (key2914, -2), (key2891, -2), (key3003, -2), (key2996, -2), (key2602, 4), (key2912, 4), (key2891, 4)]

def rawRow16100 : Integer.Sparse Key := [(key2970, 4), (key2595, 4), (key2993, 4), (key2848, -2), (key2970, -2), (key2592, -2), (key2991, -2), (key2595, -2), (key2882, -2), (key2891, -2), (key2996, -2), (key2602, -2), (key3003, -2), (key2603, -2), (key2914, -2), (key2891, 4), (key2602, 4), (key2912, 4)]

def rawRow16101 : Integer.Sparse Key := [(key2970, 4), (key2993, 4), (key2595, 4), (key2970, -2), (key2848, -2), (key2991, -2), (key2592, -2), (key2882, -2), (key2595, -2), (key2996, -2), (key2891, -2), (key3003, -2), (key2602, -2), (key2914, -2), (key2603, -2), (key2891, 4), (key2912, 4), (key2602, 4)]

def rawRow16102 : Integer.Sparse Key := [(key2993, 4), (key2595, 4), (key2970, 4), (key2882, -2), (key2991, -2), (key2595, -2), (key2970, -2), (key2592, -2), (key2848, -2), (key2914, -2), (key3003, -2), (key2603, -2), (key2996, -2), (key2602, -2), (key2891, -2), (key2912, 4), (key2602, 4), (key2891, 4)]

def rawRow16103 : Integer.Sparse Key := [(key2993, 4), (key2970, 4), (key2595, 4), (key2991, -2), (key2882, -2), (key2970, -2), (key2595, -2), (key2848, -2), (key2592, -2), (key3003, -2), (key2914, -2), (key2996, -2), (key2603, -2), (key2891, -2), (key2602, -2), (key2912, 4), (key2891, 4), (key2602, 4)]

def rawRow16104 : Integer.Sparse Key := [(key2592, 4), (key2991, 4), (key2991, 4), (key2602, -2), (key2602, -2), (key2912, -2), (key2912, -2), (key3003, -2), (key3003, -2), (key2595, -2), (key2595, -2), (key2882, -2), (key2882, -2), (key2993, -2), (key2993, -2), (key2603, 4), (key2914, 4), (key2914, 4)]

def rawRow16105 : Integer.Sparse Key := [(key2991, 4), (key2592, 4), (key2991, 4), (key2912, -2), (key3003, -2), (key2602, -2), (key3003, -2), (key2602, -2), (key2912, -2), (key2882, -2), (key2993, -2), (key2595, -2), (key2993, -2), (key2595, -2), (key2882, -2), (key2914, 4), (key2603, 4), (key2914, 4)]

def rawRow16106 : Integer.Sparse Key := [(key2991, 4), (key2991, 4), (key2592, 4), (key3003, -2), (key2912, -2), (key3003, -2), (key2602, -2), (key2912, -2), (key2602, -2), (key2993, -2), (key2882, -2), (key2993, -2), (key2595, -2), (key2882, -2), (key2595, -2), (key2914, 4), (key2914, 4), (key2603, 4)]

def rawRow16107 : Integer.Sparse Key := [(key2393, 4), (key2441, 4), (key2565, 4), (key2379, -2), (key2393, -2), (key2771, -2), (key2912, -2), (key2933, -2), (key2991, -2), (key2595, -2), (key2603, -2), (key2774, -2), (key2914, -2), (key2934, -2), (key2993, -2), (key2595, 4), (key2774, 4), (key2882, 4)]

def rawRow16108 : Integer.Sparse Key := [(key2393, 4), (key2565, 4), (key2441, 4), (key2393, -2), (key2379, -2), (key2912, -2), (key2771, -2), (key2991, -2), (key2933, -2), (key2603, -2), (key2595, -2), (key2914, -2), (key2774, -2), (key2993, -2), (key2934, -2), (key2595, 4), (key2882, 4), (key2774, 4)]

def rawRow16109 : Integer.Sparse Key := [(key2441, 4), (key2393, 4), (key2565, 4), (key2407, -2), (key2441, -2), (key2592, -2), (key2991, -2), (key2602, -2), (key2912, -2), (key2774, -2), (key2934, -2), (key2595, -2), (key2993, -2), (key2603, -2), (key2914, -2), (key2774, 4), (key2595, 4), (key2882, 4)]

def rawRow16110 : Integer.Sparse Key := [(key2441, 4), (key2565, 4), (key2393, 4), (key2441, -2), (key2407, -2), (key2991, -2), (key2592, -2), (key2912, -2), (key2602, -2), (key2934, -2), (key2774, -2), (key2993, -2), (key2595, -2), (key2914, -2), (key2603, -2), (key2774, 4), (key2882, 4), (key2595, 4)]

def rawRow16111 : Integer.Sparse Key := [(key2565, 4), (key2393, 4), (key2441, 4), (key2544, -2), (key2555, -2), (key2393, -2), (key2441, -2), (key2379, -2), (key2771, -2), (key2914, -2), (key2993, -2), (key2603, -2), (key2934, -2), (key2595, -2), (key2774, -2), (key2882, 4), (key2595, 4), (key2774, 4)]

def rawRow16112 : Integer.Sparse Key := [(key2565, 4), (key2441, 4), (key2393, 4), (key2555, -2), (key2544, -2), (key2441, -2), (key2393, -2), (key2407, -2), (key2592, -2), (key2993, -2), (key2914, -2), (key2934, -2), (key2603, -2), (key2774, -2), (key2595, -2), (key2882, 4), (key2774, 4), (key2595, 4)]

def rawRow16113 : Integer.Sparse Key := [(key2382, 4), (key2507, 4), (key2557, 4), (key2393, -2), (key2395, -2), (key2483, -2), (key2545, -2), (key2526, -2), (key2565, -2), (key2592, -2), (key2595, -2), (key2848, -2), (key2882, -2), (key2970, -2), (key2991, -2), (key2602, 4), (key2891, 4), (key2912, 4)]

def rawRow16114 : Integer.Sparse Key := [(key2382, 4), (key2557, 4), (key2507, 4), (key2395, -2), (key2393, -2), (key2545, -2), (key2483, -2), (key2565, -2), (key2526, -2), (key2595, -2), (key2592, -2), (key2882, -2), (key2848, -2), (key2991, -2), (key2970, -2), (key2602, 4), (key2912, 4), (key2891, 4)]

def rawRow16115 : Integer.Sparse Key := [(key2507, 4), (key2382, 4), (key2557, 4), (key2483, -2), (key2526, -2), (key2393, -2), (key2565, -2), (key2395, -2), (key2545, -2), (key2848, -2), (key2970, -2), (key2592, -2), (key2991, -2), (key2595, -2), (key2882, -2), (key2891, 4), (key2602, 4), (key2912, 4)]

def rawRow16116 : Integer.Sparse Key := [(key2507, 4), (key2557, 4), (key2382, 4), (key2526, -2), (key2483, -2), (key2565, -2), (key2393, -2), (key2545, -2), (key2395, -2), (key2970, -2), (key2848, -2), (key2991, -2), (key2592, -2), (key2882, -2), (key2595, -2), (key2891, 4), (key2912, 4), (key2602, 4)]

def rawRow16117 : Integer.Sparse Key := [(key2557, 4), (key2382, 4), (key2507, 4), (key2545, -2), (key2565, -2), (key2395, -2), (key2526, -2), (key2393, -2), (key2483, -2), (key2882, -2), (key2991, -2), (key2595, -2), (key2970, -2), (key2592, -2), (key2848, -2), (key2912, 4), (key2602, 4), (key2891, 4)]

def rawRow16118 : Integer.Sparse Key := [(key2557, 4), (key2507, 4), (key2382, 4), (key2565, -2), (key2545, -2), (key2526, -2), (key2395, -2), (key2483, -2), (key2393, -2), (key2991, -2), (key2882, -2), (key2970, -2), (key2595, -2), (key2848, -2), (key2592, -2), (key2912, 4), (key2891, 4), (key2602, 4)]

def rawRow16119 : Integer.Sparse Key := [(key2393, 4), (key2441, 4), (key2565, 4), (key2382, -2), (key2395, -2), (key2410, -2), (key2545, -2), (key2445, -2), (key2557, -2), (key2379, -2), (key2393, -2), (key2771, -2), (key2912, -2), (key2933, -2), (key2991, -2), (key2595, 4), (key2774, 4), (key2882, 4)]

def rawRow16120 : Integer.Sparse Key := [(key2393, 4), (key2565, 4), (key2441, 4), (key2395, -2), (key2382, -2), (key2545, -2), (key2410, -2), (key2557, -2), (key2445, -2), (key2393, -2), (key2379, -2), (key2912, -2), (key2771, -2), (key2991, -2), (key2933, -2), (key2595, 4), (key2882, 4), (key2774, 4)]

def rawRow16121 : Integer.Sparse Key := [(key2441, 4), (key2393, 4), (key2565, 4), (key2410, -2), (key2445, -2), (key2382, -2), (key2557, -2), (key2395, -2), (key2545, -2), (key2407, -2), (key2441, -2), (key2592, -2), (key2991, -2), (key2602, -2), (key2912, -2), (key2774, 4), (key2595, 4), (key2882, 4)]

def rawRow16122 : Integer.Sparse Key := [(key2441, 4), (key2565, 4), (key2393, 4), (key2445, -2), (key2410, -2), (key2557, -2), (key2382, -2), (key2545, -2), (key2395, -2), (key2441, -2), (key2407, -2), (key2991, -2), (key2592, -2), (key2912, -2), (key2602, -2), (key2774, 4), (key2882, 4), (key2595, 4)]

def rawRow16123 : Integer.Sparse Key := [(key2565, 4), (key2393, 4), (key2441, 4), (key2545, -2), (key2557, -2), (key2395, -2), (key2445, -2), (key2382, -2), (key2410, -2), (key2544, -2), (key2555, -2), (key2393, -2), (key2441, -2), (key2379, -2), (key2771, -2), (key2882, 4), (key2595, 4), (key2774, 4)]

def rawRow16124 : Integer.Sparse Key := [(key2565, 4), (key2441, 4), (key2393, 4), (key2557, -2), (key2545, -2), (key2445, -2), (key2395, -2), (key2410, -2), (key2382, -2), (key2555, -2), (key2544, -2), (key2441, -2), (key2393, -2), (key2407, -2), (key2592, -2), (key2882, 4), (key2774, 4), (key2595, 4)]

def rawRow16125 : Integer.Sparse Key := [(key2395, 4), (key2445, 4), (key2526, 4), (key2382, -2), (key2393, -2), (key2410, -2), (key2483, -2), (key2441, -2), (key2507, -2), (key2382, -2), (key2393, -2), (key2410, -2), (key2483, -2), (key2441, -2), (key2507, -2), (key2379, 4), (key2771, 4), (key2848, 4)]

def rawRow16126 : Integer.Sparse Key := [(key2395, 4), (key2526, 4), (key2445, 4), (key2393, -2), (key2382, -2), (key2483, -2), (key2410, -2), (key2507, -2), (key2441, -2), (key2393, -2), (key2382, -2), (key2483, -2), (key2410, -2), (key2507, -2), (key2441, -2), (key2379, 4), (key2848, 4), (key2771, 4)]

def rawRow16127 : Integer.Sparse Key := [(key2445, 4), (key2395, 4), (key2526, 4), (key2410, -2), (key2441, -2), (key2382, -2), (key2507, -2), (key2393, -2), (key2483, -2), (key2410, -2), (key2441, -2), (key2382, -2), (key2507, -2), (key2393, -2), (key2483, -2), (key2407, 4), (key2592, 4), (key2848, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block150
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow16128 : Integer.Sparse Key := [(key2445, 4), (key2526, 4), (key2395, 4), (key2441, -2), (key2410, -2), (key2507, -2), (key2382, -2), (key2483, -2), (key2393, -2), (key2441, -2), (key2410, -2), (key2507, -2), (key2382, -2), (key2483, -2), (key2393, -2), (key2407, 4), (key2848, 4), (key2592, 4)]

def rawRow16129 : Integer.Sparse Key := [(key2526, 4), (key2395, 4), (key2445, 4), (key2483, -2), (key2507, -2), (key2393, -2), (key2441, -2), (key2382, -2), (key2410, -2), (key2483, -2), (key2507, -2), (key2393, -2), (key2441, -2), (key2382, -2), (key2410, -2), (key2473, 4), (key2379, 4), (key2771, 4)]

def rawRow16130 : Integer.Sparse Key := [(key2526, 4), (key2445, 4), (key2395, 4), (key2507, -2), (key2483, -2), (key2441, -2), (key2393, -2), (key2410, -2), (key2382, -2), (key2507, -2), (key2483, -2), (key2441, -2), (key2393, -2), (key2410, -2), (key2382, -2), (key2473, 4), (key2407, 4), (key2592, 4)]

def rawRow16167 : Integer.Sparse Key := [(key2402, -2), (key2402, -2), (key2439, -2), (key2408, 6), (key2847, -2), (key2847, -2), (key3020, -2), (key2591, 2), (key2591, 2), (key2878, 2), (key2878, 2), (key3029, 2), (key3029, 2), (key2596, -2), (key2884, -2), (key2884, -2), (key2917, 6), (key2605, -2), (key2926, -2), (key2926, -2)]

def rawRow16168 : Integer.Sparse Key := [(key2402, -2), (key2439, -2), (key2402, -2), (key2408, 6), (key2847, -2), (key3020, -2), (key2847, -2), (key2878, 2), (key3029, 2), (key2591, 2), (key3029, 2), (key2591, 2), (key2878, 2), (key2884, -2), (key2596, -2), (key2884, -2), (key2917, 6), (key2926, -2), (key2605, -2), (key2926, -2)]

def rawRow16169 : Integer.Sparse Key := [(key2439, -2), (key2402, -2), (key2402, -2), (key2408, 6), (key3020, -2), (key2847, -2), (key2847, -2), (key3029, 2), (key2878, 2), (key3029, 2), (key2591, 2), (key2878, 2), (key2591, 2), (key2884, -2), (key2884, -2), (key2596, -2), (key2917, 6), (key2926, -2), (key2926, -2), (key2605, -2)]

def rawRow16170 : Integer.Sparse Key := [(key2402, -2), (key2408, -2), (key2439, -2), (key2402, 6), (key2878, -2), (key2884, -2), (key3029, -2), (key2591, 2), (key2596, 2), (key2847, 2), (key2884, 2), (key3020, 2), (key3029, 2), (key2591, -2), (key2847, -2), (key2878, -2), (key2926, 6), (key2605, -2), (key2917, -2), (key2926, -2)]

def rawRow16171 : Integer.Sparse Key := [(key2408, -2), (key2402, -2), (key2439, -2), (key2402, 6), (key2884, -2), (key2878, -2), (key3029, -2), (key2596, 2), (key2591, 2), (key2884, 2), (key2847, 2), (key3029, 2), (key3020, 2), (key2591, -2), (key2878, -2), (key2847, -2), (key2926, 6), (key2605, -2), (key2926, -2), (key2917, -2)]

def rawRow16172 : Integer.Sparse Key := [(key2402, -2), (key2439, -2), (key2408, -2), (key2402, 6), (key2878, -2), (key3029, -2), (key2884, -2), (key2847, 2), (key3020, 2), (key2591, 2), (key3029, 2), (key2596, 2), (key2884, 2), (key2847, -2), (key2591, -2), (key2878, -2), (key2926, 6), (key2917, -2), (key2605, -2), (key2926, -2)]

def rawRow16173 : Integer.Sparse Key := [(key2439, -2), (key2402, -2), (key2408, -2), (key2402, 6), (key3029, -2), (key2878, -2), (key2884, -2), (key3020, 2), (key2847, 2), (key3029, 2), (key2591, 2), (key2884, 2), (key2596, 2), (key2847, -2), (key2878, -2), (key2591, -2), (key2926, 6), (key2917, -2), (key2926, -2), (key2605, -2)]

def rawRow16174 : Integer.Sparse Key := [(key2408, -2), (key2439, -2), (key2402, -2), (key2402, 6), (key2884, -2), (key3029, -2), (key2878, -2), (key2884, 2), (key3029, 2), (key2596, 2), (key3020, 2), (key2591, 2), (key2847, 2), (key2878, -2), (key2591, -2), (key2847, -2), (key2926, 6), (key2926, -2), (key2605, -2), (key2917, -2)]

def rawRow16175 : Integer.Sparse Key := [(key2439, -2), (key2408, -2), (key2402, -2), (key2402, 6), (key3029, -2), (key2884, -2), (key2878, -2), (key3029, 2), (key2884, 2), (key3020, 2), (key2596, 2), (key2847, 2), (key2591, 2), (key2878, -2), (key2847, -2), (key2591, -2), (key2926, 6), (key2926, -2), (key2917, -2), (key2605, -2)]

def rawRow16176 : Integer.Sparse Key := [(key2468, -2), (key2468, -2), (key2505, -2), (key2481, 6), (key2402, -2), (key2402, -2), (key2439, -2), (key2591, 2), (key2591, 2), (key2878, 2), (key2878, 2), (key3029, 2), (key3029, 2), (key2605, -2), (key2926, -2), (key2926, -2), (key2775, 6), (key2596, -2), (key2884, -2), (key2884, -2)]

def rawRow16177 : Integer.Sparse Key := [(key2468, -2), (key2505, -2), (key2468, -2), (key2481, 6), (key2402, -2), (key2439, -2), (key2402, -2), (key2878, 2), (key3029, 2), (key2591, 2), (key3029, 2), (key2591, 2), (key2878, 2), (key2926, -2), (key2605, -2), (key2926, -2), (key2775, 6), (key2884, -2), (key2596, -2), (key2884, -2)]

def rawRow16178 : Integer.Sparse Key := [(key2505, -2), (key2468, -2), (key2468, -2), (key2481, 6), (key2439, -2), (key2402, -2), (key2402, -2), (key3029, 2), (key2878, 2), (key3029, 2), (key2591, 2), (key2878, 2), (key2591, 2), (key2926, -2), (key2926, -2), (key2605, -2), (key2775, 6), (key2884, -2), (key2884, -2), (key2596, -2)]

def rawRow16179 : Integer.Sparse Key := [(key2468, -2), (key2481, -2), (key2505, -2), (key2468, 6), (key2535, -2), (key2542, -2), (key2553, -2), (key2374, 2), (key2391, 2), (key2402, 2), (key2542, 2), (key2439, 2), (key2553, 2), (key2591, -2), (key2770, -2), (key2878, -2), (key2884, 6), (key2596, -2), (key2775, -2), (key2884, -2)]

def rawRow16180 : Integer.Sparse Key := [(key2481, -2), (key2468, -2), (key2505, -2), (key2468, 6), (key2542, -2), (key2535, -2), (key2553, -2), (key2391, 2), (key2374, 2), (key2542, 2), (key2402, 2), (key2553, 2), (key2439, 2), (key2591, -2), (key2878, -2), (key2770, -2), (key2884, 6), (key2596, -2), (key2884, -2), (key2775, -2)]

def rawRow16181 : Integer.Sparse Key := [(key2468, -2), (key2505, -2), (key2481, -2), (key2468, 6), (key2535, -2), (key2553, -2), (key2542, -2), (key2402, 2), (key2439, 2), (key2374, 2), (key2553, 2), (key2391, 2), (key2542, 2), (key2770, -2), (key2591, -2), (key2878, -2), (key2884, 6), (key2775, -2), (key2596, -2), (key2884, -2)]

def rawRow16182 : Integer.Sparse Key := [(key2505, -2), (key2468, -2), (key2481, -2), (key2468, 6), (key2553, -2), (key2535, -2), (key2542, -2), (key2439, 2), (key2402, 2), (key2553, 2), (key2374, 2), (key2542, 2), (key2391, 2), (key2770, -2), (key2878, -2), (key2591, -2), (key2884, 6), (key2775, -2), (key2884, -2), (key2596, -2)]

def rawRow16183 : Integer.Sparse Key := [(key2481, -2), (key2505, -2), (key2468, -2), (key2468, 6), (key2542, -2), (key2553, -2), (key2535, -2), (key2542, 2), (key2553, 2), (key2391, 2), (key2439, 2), (key2374, 2), (key2402, 2), (key2878, -2), (key2591, -2), (key2770, -2), (key2884, 6), (key2884, -2), (key2596, -2), (key2775, -2)]

def rawRow16184 : Integer.Sparse Key := [(key2505, -2), (key2481, -2), (key2468, -2), (key2468, 6), (key2553, -2), (key2542, -2), (key2535, -2), (key2553, 2), (key2542, 2), (key2439, 2), (key2391, 2), (key2402, 2), (key2374, 2), (key2878, -2), (key2770, -2), (key2591, -2), (key2884, 6), (key2884, -2), (key2775, -2), (key2596, -2)]

def rawRow16185 : Integer.Sparse Key := [(key2535, -2), (key2537, -2), (key2553, -2), (key2542, 6), (key2402, -2), (key2408, -2), (key2439, -2), (key2374, 2), (key2380, 2), (key2468, 2), (key2537, 2), (key2505, 2), (key2553, 2), (key2391, -2), (key2481, -2), (key2542, -2), (key2770, 6), (key2591, -2), (key2847, -2), (key2878, -2)]

def rawRow16186 : Integer.Sparse Key := [(key2537, -2), (key2535, -2), (key2553, -2), (key2542, 6), (key2408, -2), (key2402, -2), (key2439, -2), (key2380, 2), (key2374, 2), (key2537, 2), (key2468, 2), (key2553, 2), (key2505, 2), (key2391, -2), (key2542, -2), (key2481, -2), (key2770, 6), (key2591, -2), (key2878, -2), (key2847, -2)]

def rawRow16187 : Integer.Sparse Key := [(key2535, -2), (key2553, -2), (key2537, -2), (key2542, 6), (key2402, -2), (key2439, -2), (key2408, -2), (key2468, 2), (key2505, 2), (key2374, 2), (key2553, 2), (key2380, 2), (key2537, 2), (key2481, -2), (key2391, -2), (key2542, -2), (key2770, 6), (key2847, -2), (key2591, -2), (key2878, -2)]

def rawRow16188 : Integer.Sparse Key := [(key2553, -2), (key2535, -2), (key2537, -2), (key2542, 6), (key2439, -2), (key2402, -2), (key2408, -2), (key2505, 2), (key2468, 2), (key2553, 2), (key2374, 2), (key2537, 2), (key2380, 2), (key2481, -2), (key2542, -2), (key2391, -2), (key2770, 6), (key2847, -2), (key2878, -2), (key2591, -2)]

def rawRow16189 : Integer.Sparse Key := [(key2537, -2), (key2553, -2), (key2535, -2), (key2542, 6), (key2408, -2), (key2439, -2), (key2402, -2), (key2537, 2), (key2553, 2), (key2380, 2), (key2505, 2), (key2374, 2), (key2468, 2), (key2542, -2), (key2391, -2), (key2481, -2), (key2770, 6), (key2878, -2), (key2591, -2), (key2847, -2)]

def rawRow16190 : Integer.Sparse Key := [(key2553, -2), (key2537, -2), (key2535, -2), (key2542, 6), (key2439, -2), (key2408, -2), (key2402, -2), (key2553, 2), (key2537, 2), (key2505, 2), (key2380, 2), (key2468, 2), (key2374, 2), (key2542, -2), (key2481, -2), (key2391, -2), (key2770, 6), (key2878, -2), (key2847, -2), (key2591, -2)]

def rawRow16191 : Integer.Sparse Key := [(key2535, -2), (key2542, -2), (key2553, -2), (key2537, 6), (key2468, -2), (key2481, -2), (key2505, -2), (key2374, 2), (key2391, 2), (key2402, 2), (key2542, 2), (key2439, 2), (key2553, 2), (key2380, -2), (key2408, -2), (key2537, -2), (key2847, 6), (key2591, -2), (key2770, -2), (key2878, -2)]

def rawRow16192 : Integer.Sparse Key := [(key2542, -2), (key2535, -2), (key2553, -2), (key2537, 6), (key2481, -2), (key2468, -2), (key2505, -2), (key2391, 2), (key2374, 2), (key2542, 2), (key2402, 2), (key2553, 2), (key2439, 2), (key2380, -2), (key2537, -2), (key2408, -2), (key2847, 6), (key2591, -2), (key2878, -2), (key2770, -2)]

def rawRow16193 : Integer.Sparse Key := [(key2535, -2), (key2553, -2), (key2542, -2), (key2537, 6), (key2468, -2), (key2505, -2), (key2481, -2), (key2402, 2), (key2439, 2), (key2374, 2), (key2553, 2), (key2391, 2), (key2542, 2), (key2408, -2), (key2380, -2), (key2537, -2), (key2847, 6), (key2770, -2), (key2591, -2), (key2878, -2)]

def rawRow16194 : Integer.Sparse Key := [(key2553, -2), (key2535, -2), (key2542, -2), (key2537, 6), (key2505, -2), (key2468, -2), (key2481, -2), (key2439, 2), (key2402, 2), (key2553, 2), (key2374, 2), (key2542, 2), (key2391, 2), (key2408, -2), (key2537, -2), (key2380, -2), (key2847, 6), (key2770, -2), (key2878, -2), (key2591, -2)]

def rawRow16195 : Integer.Sparse Key := [(key2542, -2), (key2553, -2), (key2535, -2), (key2537, 6), (key2481, -2), (key2505, -2), (key2468, -2), (key2542, 2), (key2553, 2), (key2391, 2), (key2439, 2), (key2374, 2), (key2402, 2), (key2537, -2), (key2380, -2), (key2408, -2), (key2847, 6), (key2878, -2), (key2591, -2), (key2770, -2)]

def rawRow16196 : Integer.Sparse Key := [(key2553, -2), (key2542, -2), (key2535, -2), (key2537, 6), (key2505, -2), (key2481, -2), (key2468, -2), (key2553, 2), (key2542, 2), (key2439, 2), (key2391, 2), (key2402, 2), (key2374, 2), (key2537, -2), (key2408, -2), (key2380, -2), (key2847, 6), (key2878, -2), (key2770, -2), (key2591, -2)]

def rawRow16197 : Integer.Sparse Key := [(key2537, -2), (key2542, -2), (key2553, -2), (key2535, 6), (key2537, -2), (key2542, -2), (key2553, -2), (key2380, 2), (key2391, 2), (key2408, 2), (key2481, 2), (key2439, 2), (key2505, 2), (key2374, -2), (key2402, -2), (key2468, -2), (key2878, 6), (key2591, -2), (key2770, -2), (key2847, -2)]

def rawRow16198 : Integer.Sparse Key := [(key2542, -2), (key2537, -2), (key2553, -2), (key2535, 6), (key2542, -2), (key2537, -2), (key2553, -2), (key2391, 2), (key2380, 2), (key2481, 2), (key2408, 2), (key2505, 2), (key2439, 2), (key2374, -2), (key2468, -2), (key2402, -2), (key2878, 6), (key2591, -2), (key2847, -2), (key2770, -2)]

def rawRow16199 : Integer.Sparse Key := [(key2537, -2), (key2553, -2), (key2542, -2), (key2535, 6), (key2537, -2), (key2553, -2), (key2542, -2), (key2408, 2), (key2439, 2), (key2380, 2), (key2505, 2), (key2391, 2), (key2481, 2), (key2402, -2), (key2374, -2), (key2468, -2), (key2878, 6), (key2770, -2), (key2591, -2), (key2847, -2)]

def rawRow16200 : Integer.Sparse Key := [(key2553, -2), (key2537, -2), (key2542, -2), (key2535, 6), (key2553, -2), (key2537, -2), (key2542, -2), (key2439, 2), (key2408, 2), (key2505, 2), (key2380, 2), (key2481, 2), (key2391, 2), (key2402, -2), (key2468, -2), (key2374, -2), (key2878, 6), (key2770, -2), (key2847, -2), (key2591, -2)]

def rawRow16201 : Integer.Sparse Key := [(key2542, -2), (key2553, -2), (key2537, -2), (key2535, 6), (key2542, -2), (key2553, -2), (key2537, -2), (key2481, 2), (key2505, 2), (key2391, 2), (key2439, 2), (key2380, 2), (key2408, 2), (key2468, -2), (key2374, -2), (key2402, -2), (key2878, 6), (key2847, -2), (key2591, -2), (key2770, -2)]

def rawRow16202 : Integer.Sparse Key := [(key2553, -2), (key2542, -2), (key2537, -2), (key2535, 6), (key2553, -2), (key2542, -2), (key2537, -2), (key2505, 2), (key2481, 2), (key2439, 2), (key2391, 2), (key2408, 2), (key2380, 2), (key2468, -2), (key2402, -2), (key2374, -2), (key2878, 6), (key2847, -2), (key2770, -2), (key2591, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block151
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow16311 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2829, -1), (key2829, -1), (key3017, -1), (key3017, -1), (key2621, 2), (key2835, 2), (key2835, 2), (key2632, -1), (key2632, -1), (key2870, -1), (key2870, -1), (key3026, -1), (key3026, -1), (key2640, 2), (key2640, 2), (key2726, 2), (key2726, 2), (key3030, 2), (key3030, 2), (key2644, -1), (key2644, -1), (key2732, -1), (key2732, -1), (key2885, -1), (key2885, -1), (key2658, 2), (key2923, 2), (key2923, 2), (key2660, -1), (key2660, -1), (key2758, -1), (key2758, -1), (key2927, -1), (key2927, -1)]

def rawRow16312 : Integer.Sparse Key := [(key2948, -1), (key2960, -1), (key2612, -1), (key2960, -1), (key2616, -1), (key2829, -1), (key2835, 2), (key2621, 2), (key2835, 2), (key2870, -1), (key3026, -1), (key2632, -1), (key3026, -1), (key2632, -1), (key2870, -1), (key2726, 2), (key3030, 2), (key2640, 2), (key3030, 2), (key2640, 2), (key2726, 2), (key2732, -1), (key2885, -1), (key2644, -1), (key2885, -1), (key2644, -1), (key2732, -1), (key2923, 2), (key2658, 2), (key2923, 2), (key2758, -1), (key2927, -1), (key2660, -1), (key2927, -1), (key2660, -1), (key2758, -1)]

def rawRow16313 : Integer.Sparse Key := [(key2960, -1), (key2948, -1), (key2960, -1), (key2612, -1), (key2829, -1), (key2616, -1), (key2835, 2), (key2835, 2), (key2621, 2), (key3026, -1), (key2870, -1), (key3026, -1), (key2632, -1), (key2870, -1), (key2632, -1), (key3030, 2), (key2726, 2), (key3030, 2), (key2640, 2), (key2726, 2), (key2640, 2), (key2885, -1), (key2732, -1), (key2885, -1), (key2644, -1), (key2732, -1), (key2644, -1), (key2923, 2), (key2923, 2), (key2658, 2), (key2927, -1), (key2758, -1), (key2927, -1), (key2660, -1), (key2758, -1), (key2660, -1)]

def rawRow16314 : Integer.Sparse Key := [(key2612, -1), (key2618, -1), (key2805, -1), (key2950, -1), (key2831, -1), (key2960, -1), (key2616, 2), (key2809, 2), (key2829, 2), (key2640, -1), (key2644, -1), (key2860, -1), (key2885, -1), (key3023, -1), (key3030, -1), (key2632, 2), (key2644, 2), (key2706, 2), (key2732, 2), (key3023, 2), (key3026, 2), (key2632, -1), (key2640, -1), (key2706, -1), (key2726, -1), (key2860, -1), (key2870, -1), (key2660, 2), (key2920, 2), (key2927, 2), (key2658, -1), (key2660, -1), (key2753, -1), (key2758, -1), (key2920, -1), (key2923, -1)]

def rawRow16315 : Integer.Sparse Key := [(key2618, -1), (key2612, -1), (key2950, -1), (key2805, -1), (key2960, -1), (key2831, -1), (key2616, 2), (key2829, 2), (key2809, 2), (key2644, -1), (key2640, -1), (key2885, -1), (key2860, -1), (key3030, -1), (key3023, -1), (key2644, 2), (key2632, 2), (key2732, 2), (key2706, 2), (key3026, 2), (key3023, 2), (key2640, -1), (key2632, -1), (key2726, -1), (key2706, -1), (key2870, -1), (key2860, -1), (key2660, 2), (key2927, 2), (key2920, 2), (key2660, -1), (key2658, -1), (key2758, -1), (key2753, -1), (key2923, -1), (key2920, -1)]

def rawRow16316 : Integer.Sparse Key := [(key2805, -1), (key2831, -1), (key2612, -1), (key2960, -1), (key2618, -1), (key2950, -1), (key2809, 2), (key2616, 2), (key2829, 2), (key2860, -1), (key3023, -1), (key2640, -1), (key3030, -1), (key2644, -1), (key2885, -1), (key2706, 2), (key3023, 2), (key2632, 2), (key3026, 2), (key2644, 2), (key2732, 2), (key2706, -1), (key2860, -1), (key2632, -1), (key2870, -1), (key2640, -1), (key2726, -1), (key2920, 2), (key2660, 2), (key2927, 2), (key2753, -1), (key2920, -1), (key2658, -1), (key2923, -1), (key2660, -1), (key2758, -1)]

def rawRow16317 : Integer.Sparse Key := [(key2831, -1), (key2805, -1), (key2960, -1), (key2612, -1), (key2950, -1), (key2618, -1), (key2809, 2), (key2829, 2), (key2616, 2), (key3023, -1), (key2860, -1), (key3030, -1), (key2640, -1), (key2885, -1), (key2644, -1), (key3023, 2), (key2706, 2), (key3026, 2), (key2632, 2), (key2732, 2), (key2644, 2), (key2860, -1), (key2706, -1), (key2870, -1), (key2632, -1), (key2726, -1), (key2640, -1), (key2920, 2), (key2927, 2), (key2660, 2), (key2920, -1), (key2753, -1), (key2923, -1), (key2658, -1), (key2758, -1), (key2660, -1)]

def rawRow16318 : Integer.Sparse Key := [(key2950, -1), (key2960, -1), (key2618, -1), (key2831, -1), (key2612, -1), (key2805, -1), (key2829, 2), (key2616, 2), (key2809, 2), (key2885, -1), (key3030, -1), (key2644, -1), (key3023, -1), (key2640, -1), (key2860, -1), (key2732, 2), (key3026, 2), (key2644, 2), (key3023, 2), (key2632, 2), (key2706, 2), (key2726, -1), (key2870, -1), (key2640, -1), (key2860, -1), (key2632, -1), (key2706, -1), (key2927, 2), (key2660, 2), (key2920, 2), (key2758, -1), (key2923, -1), (key2660, -1), (key2920, -1), (key2658, -1), (key2753, -1)]

def rawRow16319 : Integer.Sparse Key := [(key2960, -1), (key2950, -1), (key2831, -1), (key2618, -1), (key2805, -1), (key2612, -1), (key2829, 2), (key2809, 2), (key2616, 2), (key3030, -1), (key2885, -1), (key3023, -1), (key2644, -1), (key2860, -1), (key2640, -1), (key3026, 2), (key2732, 2), (key3023, 2), (key2644, 2), (key2706, 2), (key2632, 2), (key2870, -1), (key2726, -1), (key2860, -1), (key2640, -1), (key2706, -1), (key2632, -1), (key2927, 2), (key2920, 2), (key2660, 2), (key2923, -1), (key2758, -1), (key2920, -1), (key2660, -1), (key2753, -1), (key2658, -1)]

def rawRow16320 : Integer.Sparse Key := [(key2628, -1), (key2628, -1), (key2972, -1), (key2972, -1), (key2983, -1), (key2983, -1), (key2641, 2), (key2976, 2), (key2976, 2), (key2612, -1), (key2616, -1), (key2829, -1), (key2829, -1), (key3017, -1), (key3017, -1), (key2640, 2), (key2640, 2), (key2726, 2), (key2726, 2), (key3030, 2), (key3030, 2), (key2660, -1), (key2660, -1), (key2758, -1), (key2758, -1), (key2927, -1), (key2927, -1), (key2621, 2), (key2835, 2), (key2835, 2), (key2644, -1), (key2644, -1), (key2732, -1), (key2732, -1), (key2885, -1), (key2885, -1)]

def rawRow16321 : Integer.Sparse Key := [(key2972, -1), (key2983, -1), (key2628, -1), (key2983, -1), (key2628, -1), (key2972, -1), (key2976, 2), (key2641, 2), (key2976, 2), (key2948, -1), (key2960, -1), (key2612, -1), (key2960, -1), (key2616, -1), (key2829, -1), (key2726, 2), (key3030, 2), (key2640, 2), (key3030, 2), (key2640, 2), (key2726, 2), (key2758, -1), (key2927, -1), (key2660, -1), (key2927, -1), (key2660, -1), (key2758, -1), (key2835, 2), (key2621, 2), (key2835, 2), (key2732, -1), (key2885, -1), (key2644, -1), (key2885, -1), (key2644, -1), (key2732, -1)]

def rawRow16322 : Integer.Sparse Key := [(key2983, -1), (key2972, -1), (key2983, -1), (key2628, -1), (key2972, -1), (key2628, -1), (key2976, 2), (key2976, 2), (key2641, 2), (key2960, -1), (key2948, -1), (key2960, -1), (key2612, -1), (key2829, -1), (key2616, -1), (key3030, 2), (key2726, 2), (key3030, 2), (key2640, 2), (key2726, 2), (key2640, 2), (key2927, -1), (key2758, -1), (key2927, -1), (key2660, -1), (key2758, -1), (key2660, -1), (key2835, 2), (key2835, 2), (key2621, 2), (key2885, -1), (key2732, -1), (key2885, -1), (key2644, -1), (key2732, -1), (key2644, -1)]

def rawRow16323 : Integer.Sparse Key := [(key2628, -1), (key2641, -1), (key2702, -1), (key2976, -1), (key2728, -1), (key2983, -1), (key2628, 2), (key2702, 2), (key2972, 2), (key2646, -1), (key2653, -1), (key2735, -1), (key2998, -1), (key2747, -1), (key3000, -1), (key2612, 2), (key2653, 2), (key2667, 2), (key2943, 2), (key2747, 2), (key2960, 2), (key2616, -1), (key2640, -1), (key2671, -1), (key2726, -1), (key2794, -1), (key2829, -1), (key2644, 2), (key2798, 2), (key2885, 2), (key2621, -1), (key2644, -1), (key2676, -1), (key2732, -1), (key2798, -1), (key2835, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow161 : Integer.Sparse Key := [(key1903, -1), (key1903, -1), (key1911, 2), (key1896, 1), (key1896, 1), (key1926, -1), (key1926, -1), (key1899, -2), (key1920, 1), (key1920, 1), (key1472, 1), (key1472, 1), (key1480, -2), (key1351, -1), (key1351, -1), (key1689, 1), (key1689, 1), (key1354, 2), (key1683, -1), (key1683, -1), (key1393, -1), (key1393, -1), (key1444, 1), (key1444, 1), (key1298, 1), (key1298, 1), (key1593, -1), (key1593, -1), (key1326, -1), (key1326, -1), (key1556, 1), (key1556, 1), (key1387, 2), (key1420, -1), (key1420, -1), (key1292, -2), (key1569, 1), (key1569, 1), (key1312, 1), (key1312, 1), (key1542, -1), (key1542, -1)]

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

def rawRow8834 : Integer.Sparse Key := [(key2359, 6), (key2353, 6), (key2359, 6), (key2359, 6), (key2566, -6), (key2566, -6), (key2578, -6), (key2566, -6)]

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

def nodeValue1185 : Sparse Master := [(Sum.inr 1185, (1 / 1))]

def nodeValue1186 : Sparse Master := [(Sum.inr 1186, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue1662 : Sparse Master := []

end MUB6.Certificate.MixedSemantics

end OAI
end


