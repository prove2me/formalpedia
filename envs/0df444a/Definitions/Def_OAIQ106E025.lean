-- Prove2me | Definitions.Def_OAIQ106E025
-- name    : OAIQ106E025
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T18:52:53.692959+00:00
-- url     : https://prove2.me/theorems/2e3ff8e1-2db9-49d8-9dc5-e0b09db674f7
-- title:
--   Definitions bundle OAIQ106E025 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2743 declarations of OpenAI's Lean: 2743 definitions. The definitions and types are `OAI.MUB6.Certificate.GramEntries.Block3.entry0_0`, `OAI.MUB6.Certificate.GramEntries.Block3.entry10_0`, `OAI.MUB6.Certificate.GramEntries.Block3.entry10_1`, `OAI.MUB6.Certificate.GramEntries.Block3.entry10_10`, `OAI.MUB6.Certificate.GramEntries.Block3.entry10_2`, `OAI.MUB6.Certificate.GramEntries.Block3.entry10_3`, `OAI.MUB6.Certificate.GramEntries.Block3.entry10_4`, `OAI.MUB6.Certificate.GramEntries.Block3.entry10_5`, `OAI.MUB6.Certificate.GramEntries.Block3.entry10_6`, `OAI.MUB6.Certificate.GramEntries.Block3.entry10_7`, `OAI.MUB6.Certificate.GramEntries.Block3.entry10_8`, `OAI.MUB6.Certificate.GramEntries.Block3.entry10_9`, `OAI.MUB6.Certificate.GramEntries.Block3.entry11_0`, `OAI.MUB6.Certificate.GramEntries.Block3.entry11_1`, `OAI.MUB6.Certificate.GramEntries.Block3.entry11_10`, `OAI.MUB6.Certificate.GramEntries.Block3.entry11_11`, `OAI.MUB6.Certificate.GramEntries.Block3.entry11_2`, `OAI.MUB6.Certificate.GramEntries.Block3.entry11_3`, `OAI.MUB6.Certificate.GramEntries.Block3.entry11_4`, `OAI.MUB6.Certificate.GramEntries.Block3.entry11_5`, `OAI.MUB6.Certificate.GramEntries.Block3.entry11_6`, `OAI.MUB6.Certificate.GramEntries.Block3.entry11_7`, `OAI.MUB6.Certificate.GramEntries.Block3.entry11_8`, `OAI.MUB6.Certificate.GramEntries.Block3.entry11_9`, `OAI.MUB6.Certificate.GramEntries.Block3.entry12_0`, `OAI.MUB6.Certificate.GramEntries.Block3.entry12_1`, `OAI.MUB6.Certificate.GramEntries.Block3.entry12_10`, `OAI.MUB6.Certificate.GramEntries.Block3.entry12_11`, `OAI.MUB6.Certificate.GramEntries.Block3.entry12_12`, `OAI.MUB6.Certificate.GramEntries.Block3.entry12_2`, `OAI.MUB6.Certificate.GramEntries.Block3.entry12_3`, `OAI.MUB6.Certificate.GramEntries.Block3.entry12_4`, `OAI.MUB6.Certificate.GramEntries.Block3.entry12_5`, `OAI.MUB6.Certificate.GramEntries.Block3.entry12_6`, `OAI.MUB6.Certificate.GramEntries.Block3.entry12_7`, `OAI.MUB6.Certificate.GramEntries.Block3.entry12_8`, `OAI.MUB6.Certificate.GramEntries.Block3.entry12_9`, `OAI.MUB6.Certificate.GramEntries.Block3.entry13_0`, `OAI.MUB6.Certificate.GramEntries.Block3.entry13_1`, `OAI.MUB6.Certificate.GramEntries.Block3.entry13_10` and 2703 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_GramEntries_Block3Data`, `MutuallyUnbiased_GramRows_Block100`, `MutuallyUnbiased_GramRows_Block101`, `MutuallyUnbiased_GramRows_Block72`, `MutuallyUnbiased_GramRows_Block73`, `MutuallyUnbiased_GramRows_Block74`, `MutuallyUnbiased_GramRows_Block75`, `MutuallyUnbiased_GramRows_Block76`, `MutuallyUnbiased_GramRows_Block77`, `MutuallyUnbiased_GramRows_Block78`, `MutuallyUnbiased_GramRows_Block81`, `MutuallyUnbiased_GramRows_Block82`, `MutuallyUnbiased_GramRows_Block83`, `MutuallyUnbiased_GramRows_Block90`, `MutuallyUnbiased_GramRows_Block91`, `MutuallyUnbiased_GramRows_Block92`, `MutuallyUnbiased_GramRows_Block93`, `MutuallyUnbiased_GramRows_Block94`, `MutuallyUnbiased_GramRows_Block95`, `MutuallyUnbiased_GramRows_Block96`, `MutuallyUnbiased_GramRows_Block97`, `MutuallyUnbiased_GramRows_Block98`, `MutuallyUnbiased_GramRows_Block99`.
--
--   **Imports.** It imports the bundles `OAIQ106E000` and `OAIQ106E002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ106E026`, `OAIQ106E027`, `OAIQ106E028` and `OAIQ106E030`; the statements `OAI.MUB6.Certificate.GramEntries.Block3.entryEval10_5_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval13_9_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval15_5_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval15_8_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval15_9_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval17_10_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval17_13_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval17_15_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval17_4_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval17_5_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval17_7_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval17_8_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval17_9_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_10_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_11_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_13_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_18_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_3_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_5_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_7_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_8_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_9_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_0_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_10_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_11_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_13_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_15_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_17_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_18_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_21_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_2_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_4_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_5_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_6_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_7_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_8_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_9_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_0_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_10_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_11_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_13_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_15_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_17_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_18_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_1_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_21_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_22_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_2_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_3_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_4_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_5_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_7_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_8_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_9_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval23_0_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval23_21_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval23_22_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval23_5_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval23_7_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval23_8_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval23_9_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_0_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_10_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_17_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_18_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_21_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_22_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_23_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_26_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_5_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_7_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_8_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_9_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval5_0_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval5_2_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval5_3_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval5_4_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval7_5_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval8_0_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval8_2_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval8_3_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval8_4_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval8_7_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval9_0_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval9_1_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval9_2_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval9_3_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval9_4_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval9_6_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval9_7_e` and `OAI.MUB6.Certificate.GramEntries.Block3.entryEval9_8_e`; the proofs of `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_10_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_11_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_13_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_18_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_3_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_5_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_7_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_8_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_9_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_0_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_10_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_11_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_13_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_15_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_17_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_18_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_21_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_2_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_4_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_5_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_6_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_7_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_8_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_9_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_0_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_10_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_11_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_13_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_15_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_17_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_18_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_1_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_21_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_22_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_2_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_3_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_4_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_5_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_7_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_8_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_9_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval23_21_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval23_22_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval23_5_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval23_7_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval23_8_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval23_9_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_0_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_10_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_17_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_18_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_21_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_22_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_23_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_26_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_5_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_7_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_8_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_9_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval5_0_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval5_2_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval5_3_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval5_4_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval7_5_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval8_0_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval8_2_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval8_3_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval8_4_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval8_7_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval9_0_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval9_1_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval9_2_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval9_3_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval9_4_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval9_6_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval9_7_e` and `OAI.MUB6.Certificate.GramEntries.Block3.entryEval9_8_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E000
import Definitions.Def_OAIQ106E002

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization

def entry0_0 : Integer.Sparse Key := [(key2362, 96), (key2367, -96), (key2457, 144), (key2460, -96), (key2521, 64), (key2525, -192), (key2532, 128), (key2533, -96), (key2562, 144), (key2564, -96)]

def entry1_0 : Integer.Sparse Key := [(key1088, -720), (key1178, 720)]

def entry1_1 : Integer.Sparse Key := [(key0, 720), (key83, -720)]

def entry2_0 : Integer.Sparse Key := [(key976, 48), (key984, -48), (key1090, -288), (key1098, -240), (key1169, -192), (key1180, 240), (key1183, 288), (key1220, 192)]

def entry2_1 : Integer.Sparse Key := [(key3, 720), (key86, -720)]

def entry2_2 : Integer.Sparse Key := [(key1, 192), (key7, 528), (key84, -192), (key90, -480), (key151, -160), (key193, 64), (key202, 48)]

def entry3_0 : Integer.Sparse Key := [(key2377, -192), (key2389, 192), (key2405, -48), (key2436, 48), (key2471, -240), (key2479, 288), (key2502, -288), (key2518, 240)]

def entry3_1 : Integer.Sparse Key := [(key1024, 720), (key1102, -720)]

def entry3_2 : Integer.Sparse Key := [(key995, -48), (key1011, 48), (key1030, 528), (key1067, 192), (key1108, -480), (key1119, -48), (key1146, -192)]

def entry3_3 : Integer.Sparse Key := [(key2606, 192), (key2622, -192), (key2661, 48), (key2696, -160), (key2776, 64), (key2799, 528), (key2849, -480)]

def entry4_0 : Integer.Sparse Key := [(key2361, 48), (key2363, -64), (key2366, 16), (key2452, -336), (key2456, 48), (key2458, -240), (key2517, 64), (key2519, -204), (key2523, 48), (key2528, 176), (key2530, 240), (key2560, 160), (key2567, 12), (key2579, 32)]

def entry4_1 : Integer.Sparse Key := [(key970, 720), (key1084, -720)]

def entry4_2 : Integer.Sparse Key := [(key971, 192), (key979, 528), (key1085, -192), (key1093, -480), (key1164, -48), (key1228, -48), (key1245, 48)]

def entry4_3 : Integer.Sparse Key := [(key2372, -48), (key2385, 48), (key2400, 528), (key2432, 192), (key2466, -480), (key2475, -48), (key2498, -192)]

def entry4_4 : Integer.Sparse Key := [(key2353, 192), (key2359, 528), (key2448, -192), (key2454, -480), (key2515, -160), (key2566, 64), (key2578, 48)]

def entry5_0 : Integer.Sparse Key := [(key2378, 24), (key2390, 32), (key2394, 24), (key2406, 24), (key2437, 32), (key2443, 24), (key2480, 24), (key2503, 24), (key2524, 24), (key2571, 12), (key2576, 12), (key2580, 16), (key2587, -120), (key2593, -96), (key2598, 64), (key2600, 72), (key2766, -24), (key2772, -48), (key2843, -144), (key2880, -96), (key2887, 120), (key2889, 48), (key2910, 84), (key2929, 16), (key2931, -24), (key2966, -72), (key2968, -144), (key2989, -108), (key2995, 120), (key3002, 80)]

def entry5_1 : Integer.Sparse Key := [(key1026, 720), (key1104, -720)]

def entry5_2 : Integer.Sparse Key := [(key1001, -48), (key1015, 48), (key1028, 192), (key1036, 336), (key1071, 192), (key1106, -192), (key1114, -240), (key1123, -96), (key1150, -192), (key1232, -48), (key1235, 48)]

def entry5_3 : Integer.Sparse Key := [(key2610, 192), (key2626, -192), (key2665, 48), (key2700, -48), (key2780, -96), (key2789, 48), (key2803, 336), (key2824, 192), (key2853, -240), (key2855, -48), (key2865, -192)]

def entry5_4 : Integer.Sparse Key := [(key2370, 24), (key2376, 24), (key2388, 32), (key2398, 168), (key2404, 312), (key2435, 176), (key2464, -128), (key2470, -144), (key2478, -120), (key2501, -120), (key2568, 12), (key2570, 16), (key2575, 16), (key2583, -24), (key2589, -72), (key2604, 16), (key2762, 24), (key2768, 24), (key2839, -64), (key2845, -96), (key2876, -60), (key2916, 24), (key2925, 32), (key3005, 16), (key3019, -72), (key3028, -16)]

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

def entry7_2 : Integer.Sparse Key := [(key993, 192), (key1001, 384), (key1015, 144), (key1028, -192), (key1036, -384), (key1071, -144), (key1123, -96), (key1150, 96), (key1235, -48), (key1242, 48)]

def entry7_3 : Integer.Sparse Key := [(key2610, -144), (key2626, 96), (key2635, 48), (key2665, 144), (key2700, 384), (key2721, 192), (key2780, -96), (key2789, -48), (key2803, -384), (key2824, -192)]

def entry7_4 : Integer.Sparse Key := [(key2370, 144), (key2376, 288), (key2388, 144), (key2398, -144), (key2404, -288), (key2435, -144), (key2583, 48), (key2589, 96), (key2762, -48), (key2768, -96), (key2916, -96), (key2925, -48), (key3019, 96), (key3028, 48)]

def entry7_5 : Integer.Sparse Key := [(key2608, -48), (key2614, -96), (key2624, 48), (key2630, 48), (key2638, 48), (key2663, 48), (key2669, 96), (key2698, 144), (key2704, 144), (key2724, 144), (key2752, 96), (key2757, 48), (key2778, -48), (key2784, -48), (key2792, -48), (key2801, -144), (key2807, -144), (key2827, -176), (key2918, -48), (key2919, -48), (key2922, -48), (key3011, -64), (key3016, -48), (key3021, 48), (key3022, 48), (key3025, 48)]

def entry7_6 : Integer.Sparse Key := [(key2585, 720), (key2764, -720)]

def entry7_7 : Integer.Sparse Key := [(key2608, 96), (key2614, 192), (key2624, 96), (key2630, 96), (key2638, 128), (key2657, 64), (key2659, 48), (key2663, -96), (key2669, -192), (key2698, -192), (key2704, -192), (key2724, -192), (key2752, -192), (key2757, -96), (key2801, 96), (key2807, 96), (key2827, 128), (key3011, 64), (key3016, 48)]

def entry8_0 : Integer.Sparse Key := [(key1256, -96), (key1261, -96), (key1265, 96), (key1268, 96), (key1536, -48), (key1609, -144), (key1642, -96), (key1648, 144), (key1651, 48), (key1674, 96), (key1765, 48), (key1806, -48), (key1809, -144), (key1832, -96), (key1837, 144), (key1848, 96)]

def entry8_1 : Integer.Sparse Key := [(key377, 720), (key428, -720)]

def entry8_2 : Integer.Sparse Key := [(key18, 24), (key23, 24), (key35, 32), (key43, 168), (key48, 312), (key74, 176), (key100, -128), (key105, -144), (key115, -120), (key137, -120), (key195, 12), (key196, 16), (key200, 16), (key206, -24), (key212, -72), (key218, 16), (key375, 24), (key381, 24), (key426, -64), (key432, -96), (key460, -60), (key486, 24), (key490, 32), (key654, 16), (key659, -72), (key663, -16)]

def entry8_3 : Integer.Sparse Key := [(key1293, 192), (key1313, -192), (key1388, 48), (key1421, -48), (key1543, -96), (key1553, 48), (key1570, 336), (key1590, 192), (key1619, -240), (key1621, -48), (key1630, -192)]

def entry8_4 : Integer.Sparse Key := [(key1259, -48), (key1271, 48), (key1526, 192), (key1534, 336), (key1604, -192), (key1612, -240), (key1640, -48), (key1679, -96), (key1693, 48), (key1894, 192), (key1916, -192)]

def entry8_5 : Integer.Sparse Key := [(key1291, 72), (key1299, 120), (key1311, -72), (key1319, -96), (key1327, -24), (key1352, -24), (key1355, 24), (key1386, 24), (key1394, 24), (key1419, -24), (key1427, -48), (key1445, -24), (key1473, 24), (key1481, 24), (key1541, -24), (key1549, -48), (key1557, 24), (key1568, 120), (key1576, 96), (key1594, 120), (key1617, -96), (key1625, -48), (key1634, -96), (key1682, -48), (key1684, 24), (key1690, -24), (key1897, -24), (key1900, 24), (key1904, 120), (key1912, 72), (key1919, -96), (key1921, -24), (key1927, -72)]

def entry8_6 : Integer.Sparse Key := [(key1528, 720), (key1606, -720)]

def entry8_7 : Integer.Sparse Key := [(key1291, -48), (key1299, -96), (key1311, 48), (key1319, 48), (key1352, 48), (key1386, 48), (key1394, 96), (key1419, -48), (key1427, -48), (key1473, -48), (key1541, 144), (key1549, 144), (key1557, 96), (key1568, -144), (key1576, -144), (key1594, -96), (key1625, -48), (key1634, 48), (key1684, -48), (key1690, 48), (key1897, 144), (key1900, 48), (key1904, -144), (key1912, -48), (key1921, -48), (key1927, 48)]

def entry8_8 : Integer.Sparse Key := [(key236, 72), (key241, 120), (key248, -72), (key253, -96), (key263, -64), (key277, 16), (key278, 24), (key302, 24), (key307, 24), (key316, -64), (key321, -96), (key331, -60), (key346, 24), (key347, 32), (key385, 16), (key400, 24), (key406, 120), (key411, 96), (key421, 160), (key435, -96), (key445, -96), (key453, -96), (key488, 24), (key489, 24), (key655, 12), (key656, 16), (key657, 80), (key658, 72), (key660, -96), (key661, -72), (key662, -72)]

def entry9_0 : Integer.Sparse Key := [(key2378, 120), (key2383, -48), (key2390, 80), (key2394, -72), (key2406, 120), (key2411, -48), (key2437, 80), (key2443, -72), (key2472, 96), (key2480, 120), (key2484, -96), (key2503, 120), (key2509, -96), (key2524, -72), (key2571, 12), (key2576, 12), (key2580, 16), (key2587, -24), (key2593, -48), (key2598, 16), (key2600, -24), (key2766, -24), (key2772, -48), (key2843, -48), (key2880, -48), (key2887, 24), (key2889, -48), (key2910, -12), (key2929, 16), (key2931, -24), (key2966, 24), (key2968, -48), (key2989, -12), (key2995, 24), (key3002, 32)]

def entry9_1 : Integer.Sparse Key := [(key1104, -720), (key1230, 720)]

def entry9_2 : Integer.Sparse Key := [(key993, 48), (key1001, -48), (key1028, 48), (key1036, -48), (key1106, -96), (key1114, -240), (key1123, -192), (key1150, -192), (key1232, 336), (key1235, 192), (key1242, 192)]

def entry9_3 : Integer.Sparse Key := [(key2626, -192), (key2635, 192), (key2700, -48), (key2721, 48), (key2780, -192), (key2789, 192), (key2803, -48), (key2824, 48), (key2853, -240), (key2855, 336), (key2865, -96)]

def entry9_4 : Integer.Sparse Key := [(key2370, 24), (key2376, -72), (key2388, -16), (key2398, 24), (key2404, -72), (key2435, -16), (key2464, -128), (key2470, -240), (key2478, -216), (key2501, -216), (key2568, 300), (key2570, 160), (key2575, 160), (key2583, 24), (key2589, 24), (key2604, 16), (key2762, 24), (key2768, 24), (key2839, 32), (key2876, 36), (key2916, 24), (key2925, 32), (key3005, 16), (key3019, 24), (key3028, 32)]

def entry9_5 : Integer.Sparse Key := [(key2608, 24), (key2614, -24), (key2624, -24), (key2630, -96), (key2638, -64), (key2657, 112), (key2659, 72), (key2663, 24), (key2669, -24), (key2698, -16), (key2704, -96), (key2724, -60), (key2752, 120), (key2757, 80), (key2778, 16), (key2784, -48), (key2792, -24), (key2801, 24), (key2807, -48), (key2827, -16), (key2851, -48), (key2858, -96), (key2868, -96), (key2918, 96), (key2919, 120), (key2922, 120), (key3007, 12), (key3009, 16), (key3011, 16), (key3016, 24), (key3021, -48), (key3022, -24), (key3025, -24)]

def entry9_6 : Integer.Sparse Key := [(key2841, -720), (key2873, 720)]

def entry9_7 : Integer.Sparse Key := [(key2624, 48), (key2630, 48), (key2638, 48), (key2657, -96), (key2659, -48), (key2698, 48), (key2704, 48), (key2724, 48), (key2752, -96), (key2757, -48), (key2778, -48), (key2784, -48), (key2792, -48), (key2801, -48), (key2807, -48), (key2827, -48), (key2918, -144), (key2919, -144), (key2922, -144), (key3007, 96), (key3009, 48), (key3011, 96), (key3016, 48), (key3021, 144), (key3022, 144), (key3025, 144)]

def entry9_8 : Integer.Sparse Key := [(key1291, 24), (key1299, -24), (key1311, -24), (key1319, -96), (key1327, -72), (key1352, 120), (key1355, 72), (key1386, 24), (key1394, -24), (key1419, -24), (key1427, -96), (key1445, -72), (key1473, 120), (key1481, 72), (key1541, 24), (key1549, -48), (key1557, -24), (key1568, 24), (key1576, -48), (key1594, -24), (key1617, -48), (key1625, -96), (key1634, -96), (key1682, 96), (key1684, 120), (key1690, 120), (key1897, 24), (key1900, 24), (key1904, 24), (key1912, 24), (key1919, -48), (key1921, -24), (key1927, -24)]

def entry9_9 : Integer.Sparse Key := [(key2608, 72), (key2614, -72), (key2624, 120), (key2630, -96), (key2638, -64), (key2657, 16), (key2659, 24), (key2663, 72), (key2669, -72), (key2698, 160), (key2704, -96), (key2724, -60), (key2752, 24), (key2757, 32), (key2778, 80), (key2784, -96), (key2792, -72), (key2801, 120), (key2807, -96), (key2827, -64), (key2851, 96), (key2858, -96), (key2868, -96), (key2919, 24), (key2922, 24), (key3007, 12), (key3009, 16), (key3011, 16), (key3016, 24), (key3022, 24), (key3025, 24)]

def entry10_0 : Integer.Sparse Key := [(key1254, -192), (key1263, 192), (key1529, -48), (key1607, -240), (key1646, 288), (key1763, 48), (key1804, -288), (key1835, 240)]

def entry10_1 : Integer.Sparse Key := [(key16, 72), (key41, 648), (key98, -480), (key205, -72), (key374, 72), (key425, -240)]

def entry10_2 : Integer.Sparse Key := [(key20, -48), (key31, 48), (key45, 528), (key70, 192), (key102, -480), (key111, -48), (key133, -192)]

def entry10_3 : Integer.Sparse Key := [(key1287, 192), (key1307, -192), (key1382, 48), (key1415, -48), (key1537, -48), (key1564, 528), (key1613, -480)]

def entry10_4 : Integer.Sparse Key := [(key1250, -48), (key1269, 48), (key1525, 528), (key1603, -480), (key1677, -48), (key1892, 192), (key1914, -192)]

def entry10_5 : Integer.Sparse Key := [(key1289, 192), (key1309, -192), (key1384, 48), (key1417, -96), (key1471, 48), (key1539, -48), (key1566, 336), (key1615, -240), (key1680, -48), (key1902, 192), (key1917, -192)]

def entry10_6 : Integer.Sparse Key := [(key1523, 720), (key1601, -720)]

def entry10_7 : Integer.Sparse Key := [(key1289, -144), (key1309, 96), (key1350, 48), (key1384, 144), (key1417, -96), (key1471, -48), (key1539, 384), (key1566, -384), (key1895, 192), (key1902, -192)]

def entry10_8 : Integer.Sparse Key := [(key238, 192), (key250, -192), (key304, 48), (key318, -48), (key387, -96), (key396, 48), (key408, 336), (key417, 192), (key437, -240), (key441, -48), (key449, -192)]

def entry10_9 : Integer.Sparse Key := [(key1309, -192), (key1350, 192), (key1417, -192), (key1471, 192), (key1539, -48), (key1566, -48), (key1615, -240), (key1680, 336), (key1895, 48), (key1902, 48), (key1917, -96)]

def entry10_10 : Integer.Sparse Key := [(key234, 192), (key246, -192), (key300, 48), (key314, -160), (key383, 64), (key404, 528), (key433, -480)]

def entry11_0 : Integer.Sparse Key := [(key2361, 144), (key2364, -144), (key2456, 576), (key2520, -576), (key2531, 144), (key2561, -144)]

def entry11_1 : Integer.Sparse Key := [(key969, -720), (key1177, 720)]

def entry11_2 : Integer.Sparse Key := [(key972, -144), (key977, -576), (key1086, 144), (key1162, -144), (key1181, 576), (key1218, 144)]

def entry11_3 : Integer.Sparse Key := [(key2369, -144), (key2384, 144), (key2397, -576), (key2431, -144), (key2474, 576), (key2497, 144)]

def entry11_4 : Integer.Sparse Key := [(key2354, -144), (key2358, -576), (key2449, 144), (key2514, -144), (key2529, 576), (key2559, 144)]

def entry11_5 : Integer.Sparse Key := [(key2588, -144), (key2599, 144), (key2763, -144), (key2767, -432), (key2840, 144), (key2875, -144), (key2888, 432), (key2909, 144), (key2930, -144), (key2967, 144)]

def entry11_6 : Integer.Sparse Key := [(key2352, -720), (key2511, 720)]

def entry11_7 : Integer.Sparse Key := [(key2584, -144), (key2588, -288), (key2599, -288), (key2763, 144), (key2767, 288), (key2888, -288), (key2909, -144), (key2930, 288), (key2967, 288), (key2988, 144)]

def entry11_8 : Integer.Sparse Key := [(key1257, -144), (key1266, 144), (key1527, -144), (key1532, -432), (key1605, 144), (key1638, -144), (key1649, 432), (key1672, 144), (key1766, -144), (key1807, 144)]

def entry11_9 : Integer.Sparse Key := [(key2584, 144), (key2588, -144), (key2763, 144), (key2767, -144), (key2840, 432), (key2875, -432), (key2888, 144), (key2909, -144), (key2967, 144), (key2988, -144)]

def entry11_10 : Integer.Sparse Key := [(key1249, -144), (key1262, 144), (key1524, -576), (key1645, 576), (key1762, -144), (key1803, 144)]

def entry11_11 : Integer.Sparse Key := [(key2353, 288), (key2356, 432), (key2448, 432), (key2527, -864), (key2558, -288)]

def entry12_0 : Integer.Sparse Key := [(key2361, 144), (key2366, -144), (key2452, 288), (key2456, 288), (key2458, 144), (key2461, -144), (key2517, 144), (key2519, 144), (key2523, -288), (key2528, -144), (key2530, -288), (key2560, -144)]

def entry12_1 : Integer.Sparse Key := [(key970, -720), (key1226, 720)]

def entry12_2 : Integer.Sparse Key := [(key971, -144), (key979, -576), (key1085, 144), (key1164, -144), (key1228, 576), (key1245, 144)]

def entry12_3 : Integer.Sparse Key := [(key2372, -144), (key2385, 144), (key2400, -576), (key2432, -144), (key2475, 576), (key2498, 144)]

def entry12_4 : Integer.Sparse Key := [(key2353, -144), (key2359, -576), (key2448, 144), (key2566, 432), (key2578, 144)]

def entry12_5 : Integer.Sparse Key := [(key2398, -144), (key2404, -288), (key2435, -144), (key2464, 144), (key2470, 144), (key2478, 144), (key2501, 144), (key2589, -144), (key2604, 144), (key2768, -144), (key2845, -144), (key2876, -144), (key2916, 288), (key2925, 144)]

def entry12_6 : Integer.Sparse Key := [(key2355, -720), (key2512, 720)]

def entry12_7 : Integer.Sparse Key := [(key2370, -144), (key2376, -288), (key2388, -144), (key2398, 144), (key2404, 288), (key2435, 144), (key2604, -144), (key2916, -288), (key2925, -144), (key3005, 144), (key3019, 288), (key3028, 144)]

def entry12_8 : Integer.Sparse Key := [(key1259, -144), (key1271, 144), (key1526, -144), (key1534, -432), (key1604, 144), (key1640, -144), (key1679, 432), (key1693, 144), (key1894, -144), (key1916, 144)]

def entry12_9 : Integer.Sparse Key := [(key2370, 72), (key2398, 72), (key2464, 240), (key2470, 144), (key2478, 144), (key2501, 144), (key2568, -288), (key2570, -144), (key2575, -144), (key2583, 72), (key2589, -144), (key2762, 72), (key2768, -144), (key2839, 192), (key2845, -144), (key2876, -144)]

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

def entry13_7 : Integer.Sparse Key := [(key2077, 192), (key2079, 384), (key2085, 144), (key2174, -192), (key2176, -384), (key2187, -144), (key2279, -96), (key2287, 96), (key2343, -48), (key2347, 48)]

def entry13_8 : Integer.Sparse Key := [(key738, -48), (key743, 48), (key817, 192), (key818, 336), (key825, 192), (key897, -192), (key898, -240), (key902, -96), (key908, -192), (key960, -48), (key962, 48)]

def entry13_9 : Integer.Sparse Key := [(key2077, 48), (key2079, -48), (key2174, 48), (key2176, -48), (key2274, -96), (key2276, -240), (key2279, -192), (key2287, -192), (key2341, 336), (key2343, 192), (key2347, 192)]

def entry13_10 : Integer.Sparse Key := [(key754, -48), (key755, 48), (key843, 528), (key844, 192), (key943, -480), (key944, -48), (key945, -192)]

def entry13_11 : Integer.Sparse Key := [(key2006, -144), (key2007, -576), (key2299, 144), (key2313, -144), (key2340, 576), (key2349, 144)]

def entry13_12 : Integer.Sparse Key := [(key1998, -144), (key2000, -576), (key2267, 144), (key2292, -144), (key2340, 576), (key2349, 144)]

def entry13_13 : Integer.Sparse Key := [(key776, 192), (key778, 528), (key801, -192), (key803, -480), (key811, -160), (key836, 64), (key839, 48)]

def entry14_0 : Integer.Sparse Key := [(key976, 144), (key984, -144), (key1090, 576), (key1169, 144), (key1183, -576), (key1220, -144)]

def entry14_2 : Integer.Sparse Key := [(key1, -144), (key7, -576), (key84, 144), (key193, 432), (key202, 144)]

def entry14_3 : Integer.Sparse Key := [(key995, -144), (key1011, 144), (key1030, -576), (key1067, -144), (key1119, 576), (key1146, 144)]

def entry14_4 : Integer.Sparse Key := [(key971, -144), (key979, -576), (key1085, 144), (key1164, 576), (key1228, -144), (key1245, 144)]

def entry14_5 : Integer.Sparse Key := [(key1001, -144), (key1015, 144), (key1028, -144), (key1036, -432), (key1071, -144), (key1106, 144), (key1123, 432), (key1150, 144), (key1232, -144), (key1235, 144)]

def entry14_6 : Integer.Sparse Key := [(key973, -720), (key1160, 720)]

def entry14_7 : Integer.Sparse Key := [(key993, -144), (key1001, -288), (key1015, -288), (key1028, 144), (key1036, 288), (key1071, 288), (key1123, -288), (key1150, 288), (key1235, -144), (key1242, 144)]

def entry14_8 : Integer.Sparse Key := [(key43, -144), (key48, -288), (key74, -144), (key100, 144), (key105, 144), (key115, 144), (key137, 144), (key212, -144), (key218, 144), (key381, -144), (key432, -144), (key460, -144), (key486, 288), (key490, 144)]

def entry14_9 : Integer.Sparse Key := [(key993, 144), (key1001, -144), (key1028, 144), (key1036, -144), (key1106, 432), (key1123, 144), (key1150, 144), (key1232, -432), (key1235, -144), (key1242, -144)]

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

def entry15_7 : Integer.Sparse Key := [(key2584, 192), (key2588, 384), (key2599, 144), (key2763, -192), (key2767, -384), (key2888, -96), (key2909, -48), (key2930, -144), (key2967, 96), (key2988, 48)]

def entry15_8 : Integer.Sparse Key := [(key1257, -48), (key1266, 48), (key1527, 192), (key1532, 336), (key1605, -192), (key1610, -240), (key1638, -48), (key1649, -96), (key1672, 48), (key1766, 192), (key1807, -192)]

def entry15_9 : Integer.Sparse Key := [(key2584, 48), (key2588, -48), (key2763, 48), (key2767, -48), (key2840, -96), (key2844, -240), (key2875, 336), (key2888, -192), (key2909, 192), (key2967, -192), (key2988, 192)]

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

def entry16_7 : Integer.Sparse Key := [(key2610, 288), (key2626, 288), (key2635, 144), (key2665, -288), (key2700, -288), (key2721, -144), (key2780, -288), (key2789, -144), (key2803, 288), (key2824, 144)]

def entry16_8 : Integer.Sparse Key := [(key1293, -144), (key1313, 144), (key1388, 144), (key1421, -144), (key1543, 432), (key1553, 144), (key1570, -432), (key1590, -144), (key1621, -144), (key1630, 144)]

def entry16_9 : Integer.Sparse Key := [(key2626, 144), (key2635, -144), (key2700, -144), (key2721, 144), (key2780, 144), (key2789, -144), (key2803, -144), (key2824, 144), (key2855, -432), (key2865, 432)]

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

def entry17_8 : Integer.Sparse Key := [(key1296, 144), (key1303, 48), (key1316, -144), (key1330, -48), (key1340, -48), (key1346, 48), (key1391, 48), (key1424, -96), (key1448, -48), (key1455, 48), (key1467, 48), (key1546, -48), (key1573, 96), (key1597, 48), (key1655, -48), (key1668, -48), (key1775, -48), (key1781, 48), (key1788, 144), (key1791, 96), (key1799, 144), (key1813, -144), (key1818, -96), (key1826, -144), (key1840, -48), (key1842, 48)]

def entry17_9 : Integer.Sparse Key := [(key2612, 24), (key2616, 24), (key2621, -48), (key2632, -48), (key2640, -16), (key2644, -144), (key2646, 16), (key2653, 32), (key2658, 48), (key2660, 112), (key2667, 24), (key2671, 24), (key2676, -48), (key2706, -48), (key2726, -12), (key2732, -144), (key2735, 24), (key2747, 36), (key2753, 48), (key2758, 120), (key2794, 24), (key2798, -96), (key2829, 32), (key2835, -96), (key2860, -48), (key2870, -48), (key2885, -144), (key2920, 96), (key2923, 96), (key2927, 120), (key2936, 12), (key2943, 24), (key2948, 16), (key2960, 32), (key2998, 24), (key3000, 24), (key3010, 12), (key3017, 16), (key3023, -48), (key3026, -48), (key3030, -24)]

def entry17_10 : Integer.Sparse Key := [(key1294, 192), (key1314, -192), (key1389, 48), (key1422, -144), (key1453, 96), (key1544, -48), (key1571, 144), (key1653, -96), (key1786, 384), (key1811, -384)]

def entry17_11 : Integer.Sparse Key := [(key2594, -144), (key2601, 144), (key2770, -288), (key2773, -288), (key2847, 288), (key2881, -288), (key2890, 288), (key2911, 288), (key2932, -144), (key2969, 144)]

def entry17_12 : Integer.Sparse Key := [(key2402, -288), (key2408, -144), (key2439, -144), (key2468, 288), (key2481, 144), (key2505, 144), (key2596, -144), (key2605, 144), (key2775, -144), (key2884, -288), (key2917, 144), (key2926, 288)]

def entry17_13 : Integer.Sparse Key := [(key2082, -48), (key2087, 48), (key2175, 384), (key2179, 144), (key2189, 192), (key2275, -384), (key2281, -144), (key2289, -192), (key2328, -96), (key2330, 96)]

def entry17_14 : Integer.Sparse Key := [(key1006, -144), (key1019, 144), (key1033, -288), (key1041, -288), (key1076, -144), (key1111, 288), (key1127, 288), (key1155, 144), (key1193, -288), (key1199, 288)]

def entry17_15 : Integer.Sparse Key := [(key2594, -48), (key2601, 48), (key2770, 384), (key2773, 144), (key2847, -384), (key2881, -96), (key2890, -144), (key2911, 96), (key2932, 192), (key2969, -192)]

def entry17_16 : Integer.Sparse Key := [(key2615, -144), (key2631, 144), (key2670, 144), (key2705, -144), (key2785, 288), (key2793, 288), (key2808, -288), (key2828, -288), (key2859, -288), (key2869, 288)]

def entry17_17 : Integer.Sparse Key := [(key2617, 96), (key2620, 96), (key2633, -96), (key2643, -192), (key2655, 96), (key2672, 48), (key2707, -96), (key2730, -192), (key2749, 128), (key2810, 48), (key2833, 128), (key2945, 64), (key2952, 64), (key2962, 192), (key2964, 96), (key2978, -192), (key2985, -192), (key2994, -192), (key3004, 96)]

def entry18_0 : Integer.Sparse Key := [(key982, 96), (key988, -96), (key1096, 144), (key1100, -96), (key1171, 96), (key1175, -144), (key1185, 96), (key1186, -144), (key1222, 144), (key1224, -96)]

def entry18_1 : Integer.Sparse Key := [(key91, -720), (key152, 720)]

def entry18_2 : Integer.Sparse Key := [(key9, 48), (key11, -64), (key14, 16), (key88, -336), (key92, 48), (key94, -240), (key153, 64), (key156, -204), (key161, 48), (key165, 176), (key167, 240), (key187, 160), (key194, 12), (key203, 32)]

def entry18_3 : Integer.Sparse Key := [(key1002, -192), (key1016, 192), (key1037, -48), (key1072, 48), (key1115, -240), (key1124, 288), (key1151, -288), (key1167, 240)]

def entry18_4 : Integer.Sparse Key := [(key981, 48), (key987, -48), (key1095, -288), (key1101, -240), (key1166, 240), (key1173, 288), (key1229, -192), (key1246, 192)]

def entry18_5 : Integer.Sparse Key := [(key1003, -96), (key1009, -96), (key1017, 96), (key1022, 96), (key1044, -48), (key1073, 48), (key1116, -144), (key1125, 144), (key1130, 48), (key1152, -48), (key1159, -144), (key1174, 144), (key1233, -96), (key1236, 96), (key1243, -96), (key1247, 96)]

def entry18_6 : Integer.Sparse Key := [(key1094, -720), (key1165, 720)]

def entry18_7 : Integer.Sparse Key := [(key1003, 96), (key1009, 48), (key1017, -48), (key1022, -96), (key1038, -96), (key1044, -48), (key1073, 48), (key1080, 96), (key1125, -192), (key1130, -192), (key1152, 192), (key1159, 192), (key1236, -192), (key1243, 192)]

def entry18_8 : Integer.Sparse Key := [(key25, 24), (key37, 32), (key40, 24), (key50, 24), (key76, 32), (key81, 24), (key117, 24), (key139, 24), (key162, 24), (key197, 12), (key201, 12), (key204, 16), (key210, -120), (key213, -96), (key215, 64), (key217, 72), (key379, -24), (key382, -48), (key430, -144), (key461, -96), (key464, 120), (key466, 48), (key483, 84), (key565, 16), (key567, -24), (key590, -72), (key592, -144), (key609, -108), (key612, 120), (key615, 80)]

def entry18_9 : Integer.Sparse Key := [(key1003, 96), (key1009, -96), (key1017, 96), (key1022, -96), (key1038, 96), (key1044, -96), (key1073, 96), (key1080, -96), (key1116, 48), (key1125, 144), (key1130, -144), (key1152, 144), (key1159, -144), (key1174, -48), (key1233, -48), (key1247, 48)]

def entry18_10 : Integer.Sparse Key := [(key24, -192), (key36, 192), (key49, -48), (key75, 48), (key106, -240), (key116, 288), (key138, -288), (key154, 240)]

def entry18_11 : Integer.Sparse Key := [(key981, 144), (key985, -144), (key1095, 576), (key1170, -576), (key1184, 144), (key1221, -144)]

def entry18_12 : Integer.Sparse Key := [(key981, 144), (key987, -144), (key1095, 576), (key1173, -576), (key1229, 144), (key1246, -144)]

def entry18_13 : Integer.Sparse Key := [(key714, 48), (key718, -48), (key891, -288), (key895, -240), (key916, -192), (key947, 240), (key948, 288), (key955, 192)]

def entry18_14 : Integer.Sparse Key := [(key9, 144), (key14, -144), (key88, 288), (key92, 288), (key94, 144), (key97, -144), (key153, 144), (key156, 144), (key161, -288), (key165, -144), (key167, -288), (key187, -144)]

def entry18_15 : Integer.Sparse Key := [(key981, 48), (key985, -48), (key1095, -288), (key1099, -240), (key1166, 240), (key1170, 288), (key1184, -192), (key1221, 192)]

def entry18_16 : Integer.Sparse Key := [(key1002, 144), (key1016, -144), (key1037, -144), (key1072, 144), (key1124, -576), (key1151, 576)]

def entry18_17 : Integer.Sparse Key := [(key1008, -192), (key1021, 192), (key1039, 48), (key1043, -96), (key1078, 96), (key1081, -48), (key1117, -48), (key1129, 96), (key1157, -96), (key1176, 48), (key1195, -192), (key1201, 192), (key1216, -192), (key1225, 192)]

def entry18_18 : Integer.Sparse Key := [(key10, 96), (key15, -96), (key93, 144), (key96, -96), (key158, 64), (key163, -192), (key169, 128), (key170, -96), (key189, 144), (key192, -96)]

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

def entry21_11 : Integer.Sparse Key := [(key2370, 72), (key2398, 72), (key2464, 240), (key2467, 144), (key2476, 144), (key2499, 144), (key2534, -288), (key2540, -144), (key2551, -144), (key2583, 72), (key2586, -144), (key2762, 72), (key2765, -144), (key2839, 192), (key2842, -144), (key2874, -144)]

def entry21_12 : Integer.Sparse Key := [(key2371, 144), (key2375, -144), (key2399, 144), (key2403, -144), (key2465, 432), (key2477, 144), (key2500, 144), (key2536, -432), (key2541, -144), (key2552, -144)]

def entry21_13 : Integer.Sparse Key := [(key2091, 48), (key2092, -48), (key2193, 48), (key2194, -48), (key2302, -96), (key2303, -240), (key2305, -192), (key2310, -192), (key2341, 336), (key2343, 192), (key2347, 192)]

def entry21_14 : Integer.Sparse Key := [(key994, 144), (key999, -144), (key1029, 144), (key1034, -144), (key1107, 432), (key1121, 144), (key1148, 144), (key1191, -432), (key1197, -144), (key1210, -144)]

def entry21_15 : Integer.Sparse Key := [(key2370, 24), (key2373, -72), (key2386, -16), (key2398, 24), (key2401, -72), (key2433, -16), (key2464, -128), (key2467, -240), (key2476, -216), (key2499, -216), (key2534, 300), (key2540, 160), (key2551, 160), (key2583, 24), (key2586, 24), (key2597, 16), (key2762, 24), (key2765, 24), (key2839, 32), (key2874, 36), (key2886, 24), (key2908, 32), (key2928, 16), (key2965, 24), (key2987, 32)]

def entry21_16 : Integer.Sparse Key := [(key2623, 144), (key2634, -144), (key2697, -144), (key2720, 144), (key2777, 144), (key2788, -144), (key2800, -144), (key2823, 144), (key2854, -432), (key2864, 432)]

def entry21_17 : Integer.Sparse Key := [(key2616, 48), (key2619, -48), (key2632, -48), (key2642, -144), (key2649, 48), (key2654, 144), (key2671, 48), (key2674, -48), (key2706, -48), (key2729, -144), (key2738, 48), (key2748, 144), (key2794, 48), (key2796, -96), (key2829, 48), (key2832, -96), (key2860, -48), (key2870, -48), (key2883, -144), (key2898, 96), (key2905, 96), (key2913, 144), (key2944, 48), (key2961, 48), (key2977, -48), (key2984, -48)]

def entry21_18 : Integer.Sparse Key := [(key1003, 96), (key1007, -96), (key1017, 96), (key1020, -96), (key1038, 96), (key1042, -96), (key1073, 96), (key1077, -96), (key1116, 48), (key1125, 144), (key1128, -144), (key1152, 144), (key1156, -144), (key1172, -48), (key1194, -48), (key1223, 48)]

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

def entry22_11 : Integer.Sparse Key := [(key2398, -144), (key2401, -288), (key2433, -144), (key2464, 144), (key2467, 144), (key2476, 144), (key2499, 144), (key2586, -144), (key2597, 144), (key2765, -144), (key2842, -144), (key2874, -144), (key2886, 288), (key2908, 144)]

def entry22_12 : Integer.Sparse Key := [(key2375, -144), (key2387, 144), (key2399, -144), (key2403, -432), (key2434, -144), (key2465, 144), (key2477, 432), (key2500, 144), (key2536, -144), (key2541, 144)]

def entry22_13 : Integer.Sparse Key := [(key2092, -48), (key2095, 48), (key2193, 192), (key2194, 336), (key2200, 192), (key2302, -192), (key2303, -240), (key2305, -96), (key2310, -192), (key2341, -48), (key2343, 48)]

def entry22_14 : Integer.Sparse Key := [(key999, -144), (key1013, 144), (key1029, -144), (key1034, -432), (key1069, -144), (key1107, 144), (key1121, 432), (key1148, 144), (key1191, -144), (key1197, 144)]

def entry22_15 : Integer.Sparse Key := [(key2370, 24), (key2373, 24), (key2386, 32), (key2398, 168), (key2401, 312), (key2433, 176), (key2464, -128), (key2467, -144), (key2476, -120), (key2499, -120), (key2534, 12), (key2540, 16), (key2551, 16), (key2583, -24), (key2586, -72), (key2597, 16), (key2762, 24), (key2765, 24), (key2839, -64), (key2842, -96), (key2874, -60), (key2886, 24), (key2908, 32), (key2928, 16), (key2965, -72), (key2987, -16)]

def entry22_16 : Integer.Sparse Key := [(key2607, -144), (key2623, 144), (key2662, 144), (key2697, -144), (key2777, 432), (key2788, 144), (key2800, -432), (key2823, -144), (key2854, -144), (key2864, 144)]

def entry22_17 : Integer.Sparse Key := [(key2616, 144), (key2619, 48), (key2632, -144), (key2642, -48), (key2649, -48), (key2654, 48), (key2671, 48), (key2706, -48), (key2729, -48), (key2748, 48), (key2786, -96), (key2794, 48), (key2809, 96), (key2829, 144), (key2832, 96), (key2860, -48), (key2870, -144), (key2883, -48), (key2905, -96), (key2913, 48), (key2939, -48), (key2944, 48), (key2951, 48), (key2961, 144), (key2977, -48), (key2984, -144)]

def entry22_18 : Integer.Sparse Key := [(key1003, -96), (key1007, -96), (key1017, 96), (key1020, 96), (key1042, -48), (key1073, 48), (key1116, -144), (key1125, 144), (key1128, 48), (key1152, -48), (key1156, -144), (key1172, 144), (key1194, -96), (key1200, 96), (key1213, -96), (key1223, 96)]

def entry22_19 : Integer.Sparse Key := [(key2678, 240), (key2687, 240), (key2709, -240), (key2713, -240), (key2816, 240), (key2862, -240)]

def entry22_20 : Integer.Sparse Key := [(key1937, -720), (key1940, 720)]

def entry22_21 : Integer.Sparse Key := [(key2608, 24), (key2611, -24), (key2624, -24), (key2627, -96), (key2636, -64), (key2645, 112), (key2651, 72), (key2663, 24), (key2666, -24), (key2698, -16), (key2701, -96), (key2722, -60), (key2734, 120), (key2745, 80), (key2778, 16), (key2781, -48), (key2790, -24), (key2801, 24), (key2804, -48), (key2825, -16), (key2851, -48), (key2856, -96), (key2866, -96), (key2892, 96), (key2895, 120), (key2902, 120), (key2935, 12), (key2941, 16), (key2947, 16), (key2958, 24), (key2971, -48), (key2974, -24), (key2981, -24)]

def entry22_22 : Integer.Sparse Key := [(key2608, 72), (key2611, 120), (key2624, -72), (key2627, -96), (key2636, -64), (key2645, 16), (key2651, 24), (key2663, 24), (key2666, 24), (key2698, -64), (key2701, -96), (key2722, -60), (key2734, 24), (key2745, 32), (key2778, 16), (key2790, 24), (key2801, 120), (key2804, 96), (key2825, 160), (key2851, -96), (key2856, -96), (key2866, -96), (key2895, 24), (key2902, 24), (key2935, 12), (key2941, 16), (key2947, 80), (key2958, 72), (key2971, -96), (key2974, -72), (key2981, -72)]

def entry23_0 : Integer.Sparse Key := [(key2362, 48), (key2367, -48), (key2457, -48), (key2460, -288), (key2521, -160), (key2525, -192), (key2532, 256), (key2533, 48), (key2562, 192), (key2564, 192)]

def entry23_1 : Integer.Sparse Key := [(key974, 720), (key1088, -720)]

def entry23_2 : Integer.Sparse Key := [(key976, 384), (key984, 336), (key1090, -384), (key1098, -240), (key1169, -96), (key1183, -96), (key1220, 96)]

def entry23_3 : Integer.Sparse Key := [(key2377, -96), (key2389, 96), (key2405, 336), (key2436, 384), (key2471, -240), (key2479, -96), (key2502, -384)]

def entry23_4 : Integer.Sparse Key := [(key2357, 192), (key2361, 192), (key2363, 224), (key2366, 112), (key2452, -240), (key2456, -144), (key2458, -144), (key2461, -96), (key2517, -32), (key2519, -108), (key2523, -144), (key2528, 32), (key2530, 48), (key2560, 64), (key2567, 12), (key2579, 32)]

def entry23_5 : Integer.Sparse Key := [(key2378, 24), (key2390, 32), (key2394, 24), (key2406, 216), (key2411, 96), (key2437, 128), (key2443, 216), (key2472, -96), (key2480, -72), (key2484, -96), (key2503, -72), (key2509, -96), (key2524, -72), (key2571, 12), (key2576, 12), (key2580, 16), (key2587, -72), (key2593, -48), (key2598, 16), (key2600, 24), (key2766, 24), (key2843, -96), (key2880, -48), (key2887, 24), (key2910, 36), (key2929, 16), (key2931, 24), (key2966, -72), (key2968, -96), (key2989, -60), (key2995, 24), (key3002, 32)]

def entry23_6 : Integer.Sparse Key := [(key2360, 720), (key2455, -720)]

def entry23_7 : Integer.Sparse Key := [(key2378, 192), (key2383, 96), (key2390, 96), (key2394, 192), (key2406, -192), (key2411, -96), (key2437, -96), (key2443, -192), (key2587, 96), (key2593, 48), (key2766, -96), (key2772, -48), (key2887, -96), (key2889, -96), (key2910, -96), (key2966, 96), (key2968, 96), (key2989, 96)]

def entry23_8 : Integer.Sparse Key := [(key1256, -48), (key1261, -48), (key1265, 48), (key1268, 48), (key1531, 240), (key1536, 96), (key1609, -192), (key1642, -48), (key1648, -48), (key1651, -96), (key1674, 48), (key1765, 144), (key1768, 240), (key1806, -144), (key1809, -192), (key1832, -48), (key1837, -48), (key1848, 48)]

def entry23_9 : Integer.Sparse Key := [(key2378, 24), (key2383, -48), (key2390, 32), (key2394, -72), (key2406, 24), (key2411, -48), (key2437, 32), (key2443, -72), (key2472, -96), (key2480, -72), (key2484, -192), (key2503, -72), (key2509, -192), (key2524, -168), (key2569, 96), (key2571, 204), (key2576, 204), (key2580, 112), (key2587, 24), (key2598, 16), (key2600, 24), (key2766, 24), (key2887, 24), (key2910, 36), (key2929, 16), (key2931, 24), (key2966, 24), (key2989, 36), (key2995, 24), (key3002, 32)]

def entry23_10 : Integer.Sparse Key := [(key1254, -96), (key1263, 96), (key1529, 336), (key1607, -240), (key1646, -96), (key1763, 384), (key1804, -384)]

def entry23_11 : Integer.Sparse Key := [(key2361, -288), (key2364, -432), (key2456, 288), (key2520, -288), (key2531, 432), (key2561, 288)]

def entry23_12 : Integer.Sparse Key := [(key2357, -144), (key2361, -144), (key2363, -192), (key2366, -240), (key2452, 288), (key2458, 144), (key2461, -144), (key2519, 144), (key2523, -288), (key2567, 288), (key2579, 288)]

def entry23_13 : Integer.Sparse Key := [(key1999, 384), (key2003, 336), (key2268, -384), (key2272, -240), (key2294, -96), (key2324, -96), (key2336, 96)]

def entry23_14 : Integer.Sparse Key := [(key976, -288), (key984, -432), (key1090, 288), (key1169, 432), (key1183, -288), (key1220, 288)]

def entry23_15 : Integer.Sparse Key := [(key2361, 384), (key2364, 336), (key2456, -384), (key2459, -240), (key2520, -96), (key2531, -96), (key2561, 96)]

def entry23_16 : Integer.Sparse Key := [(key2377, 432), (key2389, 288), (key2405, -432), (key2436, -288), (key2479, -288), (key2502, 288)]

def entry23_17 : Integer.Sparse Key := [(key2379, 24), (key2393, 64), (key2407, 120), (key2410, 192), (key2441, 256), (key2445, 96), (key2473, -96), (key2483, -192), (key2507, -192), (key2526, -96), (key2544, 32), (key2555, 32), (key2565, 48), (key2592, -24), (key2595, -96), (key2602, 32), (key2771, 24), (key2848, -48), (key2882, -96), (key2912, 64), (key2933, 32), (key2970, -96), (key2991, -32), (key2993, -96), (key3003, 48)]

def entry23_18 : Integer.Sparse Key := [(key982, 48), (key988, -48), (key1096, -48), (key1100, -288), (key1171, 288), (key1175, 48), (key1185, -192), (key1186, -192), (key1222, 192), (key1224, 192)]

def entry23_19 : Integer.Sparse Key := [(key2427, 480), (key2438, 240), (key2495, -480), (key2504, -240)]

def entry23_20 : Integer.Sparse Key := [(key1855, -720), (key1886, 720)]

def entry23_21 : Integer.Sparse Key := [(key2378, 48), (key2381, -48), (key2390, 48), (key2392, -48), (key2406, 48), (key2409, -48), (key2437, 48), (key2440, -48), (key2472, -96), (key2480, -48), (key2482, -192), (key2503, -48), (key2506, -192), (key2522, -144), (key2538, 96), (key2543, 240), (key2554, 240), (key2563, 144)]

def entry23_22 : Integer.Sparse Key := [(key2378, -48), (key2381, -48), (key2390, 48), (key2392, 48), (key2406, 240), (key2409, 96), (key2437, 144), (key2440, 240), (key2472, -192), (key2480, -48), (key2482, -96), (key2503, -144), (key2506, -192), (key2522, -48), (key2538, -48), (key2543, 48), (key2554, -48), (key2563, 48)]

def entry23_23 : Integer.Sparse Key := [(key2362, 144), (key2365, 480), (key2367, 96), (key2457, -144), (key2460, -384), (key2521, -256), (key2525, -192), (key2532, 64), (key2562, 96), (key2564, 96)]

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

def entry25_2 : Integer.Sparse Key := [(key1049, 144), (key1052, -144), (key1135, -144), (key1140, -576), (key1205, 144), (key1207, 576)]

def entry25_3 : Integer.Sparse Key := [(key3060, -576), (key3064, 576), (key3095, -144), (key3101, 144), (key3123, 144), (key3125, -144)]

def entry25_4 : Integer.Sparse Key := [(key2415, 144), (key2418, -144), (key2488, -144), (key2493, -576), (key2547, 144), (key2549, 576)]

def entry25_5 : Integer.Sparse Key := [(key2680, 144), (key2683, -144), (key2711, -144), (key2716, -432), (key2741, 144), (key2743, 432), (key2819, -144), (key2901, 144), (key2956, 144), (key2980, -144)]

def entry25_6 : Integer.Sparse Key := [(key3119, -720), (key3127, 720)]

def entry25_7 : Integer.Sparse Key := [(key2711, 144), (key2716, 288), (key2741, -144), (key2743, -288), (key2814, -144), (key2819, -288), (key2901, -288), (key2954, 144), (key2956, 288), (key2980, 288)]

def entry25_8 : Integer.Sparse Key := [(key1406, 144), (key1408, -144), (key1434, -144), (key1437, -432), (key1462, 144), (key1463, 432), (key1586, -144), (key1664, 144), (key1795, 144), (key1822, -144)]

def entry25_9 : Integer.Sparse Key := [(key2680, 432), (key2683, -432), (key2711, 144), (key2716, -144), (key2741, -144), (key2743, 144), (key2814, 144), (key2819, -144), (key2954, -144), (key2956, 144)]

def entry25_10 : Integer.Sparse Key := [(key1431, -576), (key1461, 576), (key1580, -144), (key1663, 144), (key1794, 144), (key1821, -144)]

def entry25_11 : Integer.Sparse Key := [(key2414, 144), (key2487, 180), (key2492, 432), (key2546, -144), (key2548, -432), (key3033, 288), (key3035, -432), (key3120, 108), (key3128, -144)]

def entry25_12 : Integer.Sparse Key := [(key2415, 432), (key2418, -432), (key2488, 288), (key2493, 432), (key2547, -288), (key2549, -432)]

def entry25_13 : Integer.Sparse Key := [(key2197, 144), (key2198, -144), (key2308, -144), (key2309, -576), (key2345, 144), (key2346, 576)]

def entry25_14 : Integer.Sparse Key := [(key1049, 432), (key1052, -432), (key1135, 288), (key1140, 432), (key1205, -288), (key1207, -432)]

def entry25_15 : Integer.Sparse Key := [(key2414, 48), (key2417, -144), (key2424, -144), (key2487, -144), (key2492, -576), (key2546, 144), (key2548, 468), (key3033, 96), (key3039, 144), (key3138, 108)]

def entry25_16 : Integer.Sparse Key := [(key3060, 432), (key3064, -432), (key3095, -432), (key3101, 432), (key3123, -288), (key3125, 288)]

def entry25_17 : Integer.Sparse Key := [(key2693, 288), (key2694, -288), (key2719, -288), (key2731, -288), (key2744, 288), (key2750, 288), (key2834, -144), (key2907, 144), (key2963, 144), (key2986, -144)]

def entry25_18 : Integer.Sparse Key := [(key1064, 576), (key1065, -576), (key1144, 144), (key1158, -144), (key1208, -144), (key1215, 144)]

def entry25_19 : Integer.Sparse Key := [(key3085, -720), (key3087, 720)]

def entry25_20 : Integer.Sparse Key := [(key1943, 720), (key1944, -720)]

def entry25_21 : Integer.Sparse Key := [(key2679, 216), (key2682, -144), (key2689, -48), (key2710, 72), (key2715, -144), (key2742, 72), (key2813, 48), (key2818, -144), (key2955, 48), (key3047, 216), (key3050, -288), (key3054, 48), (key3061, 72), (key3066, -144), (key3072, 72), (key3096, 96), (key3103, -144), (key3110, 96)]

def entry25_22 : Integer.Sparse Key := [(key2679, 72), (key2682, -144), (key2689, -48), (key2710, -144), (key2715, -432), (key2740, 144), (key2742, 360), (key2818, -144), (key2900, 144), (key2955, 48), (key2979, -144), (key3047, 72), (key3054, 48), (key3072, 72), (key3110, 96)]

def entry25_23 : Integer.Sparse Key := [(key2428, 288), (key2429, -288), (key2496, -288), (key2508, -432), (key2550, 288), (key2556, 432)]

def entry25_24 : Integer.Sparse Key := [(key1731, -720), (key1873, 720)]

def entry25_25 : Integer.Sparse Key := [(key3081, 288), (key3082, -288), (key3086, 432), (key3088, -864), (key3091, 432)]

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

def row9728 : Integer.Sparse Key := [(key2632, 2), (key2640, 2), (key2644, 2), (key2658, -2), (key2660, -4), (key2706, 2), (key2726, 2), (key2732, 2), (key2753, -2), (key2758, -4), (key2860, 2), (key2870, 2), (key2885, 2), (key2920, -4), (key2923, -4), (key2927, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

def row9729 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2621, -2), (key2640, 2), (key2644, -4), (key2660, 2), (key2671, 2), (key2676, -2), (key2726, 2), (key2732, -4), (key2758, 2), (key2794, 2), (key2798, -4), (key2829, 2), (key2835, -4), (key2885, -4), (key2927, 2), (key3010, 2), (key3017, 2), (key3030, 2)]

def row9730 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2621, -2), (key2640, 1), (key2644, -4), (key2646, 1), (key2653, 2), (key2671, 2), (key2676, -2), (key2726, 2), (key2732, -4), (key2758, 2), (key2794, 2), (key2798, -4), (key2829, 2), (key2835, -4), (key2885, -4), (key2927, 2), (key3010, 2), (key3017, 2), (key3030, 2)]

def row9731 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2621, -2), (key2640, 1), (key2644, -4), (key2646, 1), (key2653, 2), (key2671, 2), (key2676, -2), (key2726, 2), (key2732, -4), (key2758, 2), (key2794, 2), (key2798, -4), (key2829, 2), (key2835, -4), (key2885, -4), (key2927, 2), (key3010, 2), (key3017, 2), (key3030, 2)]

def row9732 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2621, -2), (key2640, 2), (key2644, -4), (key2660, 2), (key2667, 2), (key2676, -2), (key2726, 2), (key2732, -4), (key2735, 2), (key2747, 2), (key2758, 2), (key2798, -4), (key2829, 2), (key2835, -4), (key2885, -4), (key2927, 2), (key3017, 2), (key3030, 2)]

def row9733 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2621, -2), (key2640, 2), (key2644, -4), (key2660, 2), (key2667, 2), (key2676, -2), (key2726, 2), (key2732, -4), (key2735, 2), (key2747, 2), (key2758, 2), (key2798, -4), (key2829, 1), (key2835, -4), (key2885, -4), (key2927, 2), (key2948, 1), (key2960, 2), (key3030, 2)]

def row9734 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2621, -2), (key2640, 2), (key2644, -4), (key2660, 2), (key2667, 2), (key2676, -2), (key2726, 2), (key2732, -4), (key2735, 2), (key2747, 2), (key2758, 2), (key2798, -4), (key2829, 1), (key2835, -4), (key2885, -4), (key2927, 2), (key2948, 1), (key2960, 2), (key3030, 2)]

def row9735 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2621, -2), (key2640, 1), (key2644, -4), (key2646, 1), (key2653, 2), (key2667, 1), (key2671, 1), (key2676, -2), (key2726, 1), (key2732, -4), (key2735, 1), (key2747, 2), (key2794, 1), (key2798, -4), (key2829, 1), (key2835, -4), (key2885, -4), (key2936, 1), (key2943, 2), (key2948, 1), (key2960, 2), (key2998, 2), (key3000, 2)]

def row9736 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2621, -2), (key2640, 1), (key2644, -4), (key2646, 1), (key2653, 2), (key2667, 1), (key2671, 1), (key2676, -2), (key2726, 1), (key2732, -4), (key2735, 1), (key2747, 2), (key2794, 1), (key2798, -4), (key2829, 1), (key2835, -4), (key2885, -4), (key2936, 1), (key2943, 2), (key2948, 1), (key2960, 2), (key2998, 2), (key3000, 2)]

def row9737 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2621, -2), (key2640, 1), (key2644, -4), (key2646, 1), (key2653, 2), (key2667, 1), (key2671, 1), (key2676, -2), (key2726, 1), (key2732, -4), (key2735, 1), (key2747, 2), (key2794, 1), (key2798, -4), (key2829, 1), (key2835, -4), (key2885, -4), (key2936, 1), (key2943, 2), (key2948, 1), (key2960, 2), (key2998, 2), (key3000, 2)]

def row9738 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2621, -2), (key2640, 1), (key2644, -4), (key2646, 1), (key2653, 2), (key2667, 1), (key2671, 1), (key2676, -2), (key2726, 1), (key2732, -4), (key2735, 1), (key2747, 2), (key2794, 1), (key2798, -4), (key2829, 1), (key2835, -4), (key2885, -4), (key2936, 1), (key2943, 2), (key2948, 1), (key2960, 2), (key2998, 2), (key3000, 2)]

def row9741 : Integer.Sparse Key := [(key1294, -6), (key1314, 2), (key1335, 4), (key1544, 2), (key1571, -6), (key1653, 4), (key1770, 4), (key1786, -12), (key1811, 4), (key1838, 4)]

def row9742 : Integer.Sparse Key := [(key1294, -6), (key1314, 2), (key1335, 4), (key1544, 2), (key1571, -6), (key1653, 4), (key1770, 4), (key1786, -12), (key1811, 4), (key1838, 4)]

def row9743 : Integer.Sparse Key := [(key1294, -6), (key1314, 2), (key1335, 4), (key1544, 2), (key1571, -6), (key1653, 4), (key1770, 4), (key1786, -12), (key1811, 4), (key1838, 4)]

def row9744 : Integer.Sparse Key := [(key1294, -6), (key1314, 2), (key1335, 4), (key1544, 2), (key1571, -6), (key1653, 4), (key1770, 4), (key1786, -12), (key1811, 4), (key1838, 4)]

def row9745 : Integer.Sparse Key := [(key1294, -6), (key1314, 2), (key1335, 4), (key1544, 2), (key1571, -6), (key1653, 4), (key1770, 4), (key1786, -12), (key1811, 4), (key1838, 4)]

def row9746 : Integer.Sparse Key := [(key1294, -6), (key1314, 2), (key1335, 4), (key1544, 2), (key1571, -6), (key1653, 4), (key1770, 4), (key1786, -12), (key1811, 4), (key1838, 4)]

def row9747 : Integer.Sparse Key := [(key1294, -6), (key1314, 2), (key1335, 4), (key1544, 2), (key1571, -6), (key1653, 4), (key1770, 4), (key1786, -12), (key1811, 4), (key1838, 4)]

def row9748 : Integer.Sparse Key := [(key1294, -6), (key1314, 2), (key1335, 4), (key1544, 2), (key1571, -6), (key1653, 4), (key1770, 4), (key1786, -12), (key1811, 4), (key1838, 4)]

def row9749 : Integer.Sparse Key := [(key1294, -6), (key1314, 2), (key1335, 4), (key1544, 2), (key1571, -6), (key1653, 4), (key1770, 4), (key1786, -12), (key1811, 4), (key1838, 4)]

def row9750 : Integer.Sparse Key := [(key1294, -6), (key1314, 2), (key1335, 4), (key1544, 2), (key1571, -6), (key1653, 4), (key1770, 4), (key1786, -12), (key1811, 4), (key1838, 4)]

def row9751 : Integer.Sparse Key := [(key1294, -6), (key1314, 2), (key1335, 4), (key1544, 2), (key1571, -6), (key1653, 4), (key1770, 4), (key1786, -12), (key1811, 4), (key1838, 4)]

def row9752 : Integer.Sparse Key := [(key1294, -6), (key1314, 2), (key1335, 4), (key1544, 2), (key1571, -6), (key1653, 4), (key1770, 4), (key1786, -12), (key1811, 4), (key1838, 4)]

def row9753 : Integer.Sparse Key := [(key1294, 2), (key1314, -6), (key1335, 4), (key1389, 2), (key1422, -6), (key1453, 4), (key1770, 4), (key1786, 4), (key1811, -12), (key1838, 4)]

def row9754 : Integer.Sparse Key := [(key1294, 2), (key1314, -6), (key1335, 4), (key1389, 2), (key1422, -6), (key1453, 4), (key1770, 4), (key1786, 4), (key1811, -12), (key1838, 4)]

def row9755 : Integer.Sparse Key := [(key1294, 2), (key1314, -6), (key1335, 4), (key1389, 2), (key1422, -6), (key1453, 4), (key1770, 4), (key1786, 4), (key1811, -12), (key1838, 4)]

def row9756 : Integer.Sparse Key := [(key1294, 2), (key1314, -6), (key1335, 4), (key1389, 2), (key1422, -6), (key1453, 4), (key1770, 4), (key1786, 4), (key1811, -12), (key1838, 4)]

def row9757 : Integer.Sparse Key := [(key1294, 2), (key1314, -6), (key1335, 4), (key1389, 2), (key1422, -6), (key1453, 4), (key1770, 4), (key1786, 4), (key1811, -12), (key1838, 4)]

def row9758 : Integer.Sparse Key := [(key1294, 2), (key1314, -6), (key1335, 4), (key1389, 2), (key1422, -6), (key1453, 4), (key1770, 4), (key1786, 4), (key1811, -12), (key1838, 4)]

def row9759 : Integer.Sparse Key := [(key1294, 2), (key1314, -6), (key1335, 4), (key1389, 2), (key1422, -6), (key1453, 4), (key1770, 4), (key1786, 4), (key1811, -12), (key1838, 4)]

def row9760 : Integer.Sparse Key := [(key1294, 2), (key1314, -6), (key1335, 4), (key1389, 2), (key1422, -6), (key1453, 4), (key1770, 4), (key1786, 4), (key1811, -12), (key1838, 4)]

def row9761 : Integer.Sparse Key := [(key1294, 2), (key1314, -6), (key1335, 4), (key1389, 2), (key1422, -6), (key1453, 4), (key1770, 4), (key1786, 4), (key1811, -12), (key1838, 4)]

def row9762 : Integer.Sparse Key := [(key1294, 2), (key1314, -6), (key1335, 4), (key1389, 2), (key1422, -6), (key1453, 4), (key1770, 4), (key1786, 4), (key1811, -12), (key1838, 4)]

def row9763 : Integer.Sparse Key := [(key1294, 2), (key1314, -6), (key1335, 4), (key1389, 2), (key1422, -6), (key1453, 4), (key1770, 4), (key1786, 4), (key1811, -12), (key1838, 4)]

def row9764 : Integer.Sparse Key := [(key1294, 2), (key1314, -6), (key1335, 4), (key1389, 2), (key1422, -6), (key1453, 4), (key1770, 4), (key1786, 4), (key1811, -12), (key1838, 4)]

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

def row9816 : Integer.Sparse Key := [(key2078, 4), (key2082, 2), (key2175, -12), (key2179, -6), (key2189, -6), (key2275, 4), (key2289, 2), (key2327, 4), (key2328, 4), (key2333, 4)]

def row9817 : Integer.Sparse Key := [(key2078, 4), (key2082, 2), (key2175, -12), (key2179, -6), (key2189, -6), (key2275, 4), (key2289, 2), (key2327, 4), (key2328, 4), (key2333, 4)]

def row9818 : Integer.Sparse Key := [(key2078, 4), (key2082, 2), (key2175, -12), (key2179, -6), (key2189, -6), (key2275, 4), (key2289, 2), (key2327, 4), (key2328, 4), (key2333, 4)]

def row9819 : Integer.Sparse Key := [(key2078, 4), (key2082, 2), (key2175, -12), (key2179, -6), (key2189, -6), (key2275, 4), (key2289, 2), (key2327, 4), (key2328, 4), (key2333, 4)]

def row9820 : Integer.Sparse Key := [(key2078, 4), (key2082, 2), (key2175, -12), (key2179, -6), (key2189, -6), (key2275, 4), (key2289, 2), (key2327, 4), (key2328, 4), (key2333, 4)]

def row9821 : Integer.Sparse Key := [(key2078, 4), (key2082, 2), (key2175, -12), (key2179, -6), (key2189, -6), (key2275, 4), (key2289, 2), (key2327, 4), (key2328, 4), (key2333, 4)]

def row9822 : Integer.Sparse Key := [(key2078, 4), (key2082, 2), (key2175, -12), (key2179, -6), (key2189, -6), (key2275, 4), (key2289, 2), (key2327, 4), (key2328, 4), (key2333, 4)]

def row9823 : Integer.Sparse Key := [(key2078, 4), (key2082, 2), (key2175, -12), (key2179, -6), (key2189, -6), (key2275, 4), (key2289, 2), (key2327, 4), (key2328, 4), (key2333, 4)]

def row9824 : Integer.Sparse Key := [(key2078, 4), (key2082, 2), (key2175, -12), (key2179, -6), (key2189, -6), (key2275, 4), (key2289, 2), (key2327, 4), (key2328, 4), (key2333, 4)]

def row9825 : Integer.Sparse Key := [(key2078, 4), (key2087, 2), (key2175, 4), (key2189, 2), (key2275, -12), (key2281, -6), (key2289, -6), (key2327, 4), (key2330, 4), (key2333, 4)]

def row9826 : Integer.Sparse Key := [(key2078, 4), (key2087, 2), (key2175, 4), (key2189, 2), (key2275, -12), (key2281, -6), (key2289, -6), (key2327, 4), (key2330, 4), (key2333, 4)]

def row9827 : Integer.Sparse Key := [(key2078, 4), (key2087, 2), (key2175, 4), (key2189, 2), (key2275, -12), (key2281, -6), (key2289, -6), (key2327, 4), (key2330, 4), (key2333, 4)]

def row9828 : Integer.Sparse Key := [(key2078, 4), (key2087, 2), (key2175, 4), (key2189, 2), (key2275, -12), (key2281, -6), (key2289, -6), (key2327, 4), (key2330, 4), (key2333, 4)]

def row9829 : Integer.Sparse Key := [(key2078, 4), (key2087, 2), (key2175, 4), (key2189, 2), (key2275, -12), (key2281, -6), (key2289, -6), (key2327, 4), (key2330, 4), (key2333, 4)]

def row9830 : Integer.Sparse Key := [(key2078, 4), (key2087, 2), (key2175, 4), (key2189, 2), (key2275, -12), (key2281, -6), (key2289, -6), (key2327, 4), (key2330, 4), (key2333, 4)]

def row9831 : Integer.Sparse Key := [(key2078, 4), (key2087, 2), (key2175, 4), (key2189, 2), (key2275, -12), (key2281, -6), (key2289, -6), (key2327, 4), (key2330, 4), (key2333, 4)]

def row9832 : Integer.Sparse Key := [(key2078, 4), (key2087, 2), (key2175, 4), (key2189, 2), (key2275, -12), (key2281, -6), (key2289, -6), (key2327, 4), (key2330, 4), (key2333, 4)]

def row9833 : Integer.Sparse Key := [(key2078, 4), (key2087, 2), (key2175, 4), (key2189, 2), (key2275, -12), (key2281, -6), (key2289, -6), (key2327, 4), (key2330, 4), (key2333, 4)]

def row9834 : Integer.Sparse Key := [(key2078, 4), (key2087, 2), (key2175, 4), (key2189, 2), (key2275, -12), (key2281, -6), (key2289, -6), (key2327, 4), (key2330, 4), (key2333, 4)]

def row9835 : Integer.Sparse Key := [(key2078, 4), (key2087, 2), (key2175, 4), (key2189, 2), (key2275, -12), (key2281, -6), (key2289, -6), (key2327, 4), (key2330, 4), (key2333, 4)]

def row9836 : Integer.Sparse Key := [(key2078, 4), (key2087, 2), (key2175, 4), (key2189, 2), (key2275, -12), (key2281, -6), (key2289, -6), (key2327, 4), (key2330, 4), (key2333, 4)]

def row9837 : Integer.Sparse Key := [(key1019, -6), (key1033, 12), (key1041, 6), (key1076, 6), (key1127, -6), (key1199, -12)]

def row9838 : Integer.Sparse Key := [(key1019, -6), (key1033, 12), (key1041, 6), (key1076, 6), (key1127, -6), (key1199, -12)]

def row9839 : Integer.Sparse Key := [(key1019, -6), (key1033, 12), (key1041, 6), (key1076, 6), (key1127, -6), (key1199, -12)]

def row9840 : Integer.Sparse Key := [(key1019, -6), (key1033, 12), (key1041, 6), (key1076, 6), (key1127, -6), (key1199, -12)]

def row9841 : Integer.Sparse Key := [(key1019, -6), (key1033, 12), (key1041, 6), (key1076, 6), (key1127, -6), (key1199, -12)]

def row9842 : Integer.Sparse Key := [(key1019, -6), (key1033, 12), (key1041, 6), (key1076, 6), (key1127, -6), (key1199, -12)]

def row9843 : Integer.Sparse Key := [(key1019, -6), (key1033, 12), (key1041, 6), (key1076, 6), (key1127, -6), (key1199, -12)]

def row9844 : Integer.Sparse Key := [(key1019, -6), (key1033, 12), (key1041, 6), (key1076, 6), (key1127, -6), (key1199, -12)]

def row9845 : Integer.Sparse Key := [(key1019, -6), (key1033, 12), (key1041, 6), (key1076, 6), (key1127, -6), (key1199, -12)]

def row9846 : Integer.Sparse Key := [(key1019, -6), (key1033, 12), (key1041, 6), (key1076, 6), (key1127, -6), (key1199, -12)]

def row9847 : Integer.Sparse Key := [(key1019, -6), (key1033, 12), (key1041, 6), (key1076, 6), (key1127, -6), (key1199, -12)]

def row9848 : Integer.Sparse Key := [(key1019, -6), (key1033, 12), (key1041, 6), (key1076, 6), (key1127, -6), (key1199, -12)]

def row9849 : Integer.Sparse Key := [(key1006, -6), (key1041, -6), (key1111, 12), (key1127, 6), (key1155, 6), (key1193, -12)]

def row9850 : Integer.Sparse Key := [(key1006, -6), (key1041, -6), (key1111, 12), (key1127, 6), (key1155, 6), (key1193, -12)]

def row9851 : Integer.Sparse Key := [(key1006, -6), (key1041, -6), (key1111, 12), (key1127, 6), (key1155, 6), (key1193, -12)]

def row9852 : Integer.Sparse Key := [(key1006, -6), (key1041, -6), (key1111, 12), (key1127, 6), (key1155, 6), (key1193, -12)]

def row9853 : Integer.Sparse Key := [(key1006, -6), (key1041, -6), (key1111, 12), (key1127, 6), (key1155, 6), (key1193, -12)]

def row9854 : Integer.Sparse Key := [(key1006, -6), (key1041, -6), (key1111, 12), (key1127, 6), (key1155, 6), (key1193, -12)]

def row9855 : Integer.Sparse Key := [(key1006, -6), (key1041, -6), (key1111, 12), (key1127, 6), (key1155, 6), (key1193, -12)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block101
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row9856 : Integer.Sparse Key := [(key1006, -6), (key1041, -6), (key1111, 12), (key1127, 6), (key1155, 6), (key1193, -12)]

def row9857 : Integer.Sparse Key := [(key1006, -6), (key1041, -6), (key1111, 12), (key1127, 6), (key1155, 6), (key1193, -12)]

def row9858 : Integer.Sparse Key := [(key1006, -6), (key1041, -6), (key1111, 12), (key1127, 6), (key1155, 6), (key1193, -12)]

def row9859 : Integer.Sparse Key := [(key1006, -6), (key1041, -6), (key1111, 12), (key1127, 6), (key1155, 6), (key1193, -12)]

def row9860 : Integer.Sparse Key := [(key1006, -6), (key1041, -6), (key1111, 12), (key1127, 6), (key1155, 6), (key1193, -12)]

def row9861 : Integer.Sparse Key := [(key2591, 4), (key2594, 2), (key2770, -12), (key2773, -6), (key2847, 4), (key2878, 4), (key2881, 4), (key2932, -6), (key2969, 2), (key2990, 4)]

def row9862 : Integer.Sparse Key := [(key2591, 4), (key2594, 2), (key2770, -12), (key2773, -6), (key2847, 4), (key2878, 4), (key2881, 4), (key2932, -6), (key2969, 2), (key2990, 4)]

def row9863 : Integer.Sparse Key := [(key2591, 4), (key2594, 2), (key2770, -12), (key2773, -6), (key2847, 4), (key2878, 4), (key2881, 4), (key2932, -6), (key2969, 2), (key2990, 4)]

def row9864 : Integer.Sparse Key := [(key2591, 4), (key2594, 2), (key2770, -12), (key2773, -6), (key2847, 4), (key2878, 4), (key2881, 4), (key2932, -6), (key2969, 2), (key2990, 4)]

def row9865 : Integer.Sparse Key := [(key2591, 4), (key2594, 2), (key2770, -12), (key2773, -6), (key2847, 4), (key2878, 4), (key2881, 4), (key2932, -6), (key2969, 2), (key2990, 4)]

def row9866 : Integer.Sparse Key := [(key2591, 4), (key2594, 2), (key2770, -12), (key2773, -6), (key2847, 4), (key2878, 4), (key2881, 4), (key2932, -6), (key2969, 2), (key2990, 4)]

def row9867 : Integer.Sparse Key := [(key2591, 4), (key2594, 2), (key2770, -12), (key2773, -6), (key2847, 4), (key2878, 4), (key2881, 4), (key2932, -6), (key2969, 2), (key2990, 4)]

def row9868 : Integer.Sparse Key := [(key2591, 4), (key2594, 2), (key2770, -12), (key2773, -6), (key2847, 4), (key2878, 4), (key2881, 4), (key2932, -6), (key2969, 2), (key2990, 4)]

def row9869 : Integer.Sparse Key := [(key2591, 4), (key2594, 2), (key2770, -12), (key2773, -6), (key2847, 4), (key2878, 4), (key2881, 4), (key2932, -6), (key2969, 2), (key2990, 4)]

def row9870 : Integer.Sparse Key := [(key2591, 4), (key2594, 2), (key2770, -12), (key2773, -6), (key2847, 4), (key2878, 4), (key2881, 4), (key2932, -6), (key2969, 2), (key2990, 4)]

def row9871 : Integer.Sparse Key := [(key2591, 4), (key2594, 2), (key2770, -12), (key2773, -6), (key2847, 4), (key2878, 4), (key2881, 4), (key2932, -6), (key2969, 2), (key2990, 4)]

def row9872 : Integer.Sparse Key := [(key2591, 4), (key2594, 2), (key2770, -12), (key2773, -6), (key2847, 4), (key2878, 4), (key2881, 4), (key2932, -6), (key2969, 2), (key2990, 4)]

def row9873 : Integer.Sparse Key := [(key2591, 4), (key2601, 2), (key2770, 4), (key2847, -12), (key2878, 4), (key2890, -6), (key2911, 4), (key2932, 2), (key2969, -6), (key2990, 4)]

def row9874 : Integer.Sparse Key := [(key2591, 4), (key2601, 2), (key2770, 4), (key2847, -12), (key2878, 4), (key2890, -6), (key2911, 4), (key2932, 2), (key2969, -6), (key2990, 4)]

def row9875 : Integer.Sparse Key := [(key2591, 4), (key2601, 2), (key2770, 4), (key2847, -12), (key2878, 4), (key2890, -6), (key2911, 4), (key2932, 2), (key2969, -6), (key2990, 4)]

def row9876 : Integer.Sparse Key := [(key2591, 4), (key2601, 2), (key2770, 4), (key2847, -12), (key2878, 4), (key2890, -6), (key2911, 4), (key2932, 2), (key2969, -6), (key2990, 4)]

def row9877 : Integer.Sparse Key := [(key2591, 4), (key2601, 2), (key2770, 4), (key2847, -12), (key2878, 4), (key2890, -6), (key2911, 4), (key2932, 2), (key2969, -6), (key2990, 4)]

def row9878 : Integer.Sparse Key := [(key2591, 4), (key2601, 2), (key2770, 4), (key2847, -12), (key2878, 4), (key2890, -6), (key2911, 4), (key2932, 2), (key2969, -6), (key2990, 4)]

def row9879 : Integer.Sparse Key := [(key2591, 4), (key2601, 2), (key2770, 4), (key2847, -12), (key2878, 4), (key2890, -6), (key2911, 4), (key2932, 2), (key2969, -6), (key2990, 4)]

def row9880 : Integer.Sparse Key := [(key2591, 4), (key2601, 2), (key2770, 4), (key2847, -12), (key2878, 4), (key2890, -6), (key2911, 4), (key2932, 2), (key2969, -6), (key2990, 4)]

def row9881 : Integer.Sparse Key := [(key2591, 4), (key2601, 2), (key2770, 4), (key2847, -12), (key2878, 4), (key2890, -6), (key2911, 4), (key2932, 2), (key2969, -6), (key2990, 4)]

def row9882 : Integer.Sparse Key := [(key2591, 4), (key2601, 2), (key2770, 4), (key2847, -12), (key2878, 4), (key2890, -6), (key2911, 4), (key2932, 2), (key2969, -6), (key2990, 4)]

def row9883 : Integer.Sparse Key := [(key2591, 4), (key2601, 2), (key2770, 4), (key2847, -12), (key2878, 4), (key2890, -6), (key2911, 4), (key2932, 2), (key2969, -6), (key2990, 4)]

def row9884 : Integer.Sparse Key := [(key2591, 4), (key2601, 2), (key2770, 4), (key2847, -12), (key2878, 4), (key2890, -6), (key2911, 4), (key2932, 2), (key2969, -6), (key2990, 4)]

def row9885 : Integer.Sparse Key := [(key2615, 6), (key2670, -6), (key2785, -6), (key2793, -12), (key2808, 6), (key2828, 12)]

def row9886 : Integer.Sparse Key := [(key2615, 6), (key2670, -6), (key2785, -6), (key2793, -12), (key2808, 6), (key2828, 12)]

def row9887 : Integer.Sparse Key := [(key2615, 6), (key2670, -6), (key2785, -6), (key2793, -12), (key2808, 6), (key2828, 12)]

def row9888 : Integer.Sparse Key := [(key2615, 6), (key2670, -6), (key2785, -6), (key2793, -12), (key2808, 6), (key2828, 12)]

def row9889 : Integer.Sparse Key := [(key2615, 6), (key2670, -6), (key2785, -6), (key2793, -12), (key2808, 6), (key2828, 12)]

def row9890 : Integer.Sparse Key := [(key2615, 6), (key2670, -6), (key2785, -6), (key2793, -12), (key2808, 6), (key2828, 12)]

def row9891 : Integer.Sparse Key := [(key2615, 6), (key2670, -6), (key2785, -6), (key2793, -12), (key2808, 6), (key2828, 12)]

def row9892 : Integer.Sparse Key := [(key2615, 6), (key2670, -6), (key2785, -6), (key2793, -12), (key2808, 6), (key2828, 12)]

def row9893 : Integer.Sparse Key := [(key2615, 6), (key2670, -6), (key2785, -6), (key2793, -12), (key2808, 6), (key2828, 12)]

def row9894 : Integer.Sparse Key := [(key2615, 6), (key2670, -6), (key2785, -6), (key2793, -12), (key2808, 6), (key2828, 12)]

def row9895 : Integer.Sparse Key := [(key2615, 6), (key2670, -6), (key2785, -6), (key2793, -12), (key2808, 6), (key2828, 12)]

def row9896 : Integer.Sparse Key := [(key2615, 6), (key2670, -6), (key2785, -6), (key2793, -12), (key2808, 6), (key2828, 12)]

def row9897 : Integer.Sparse Key := [(key2631, 6), (key2705, -6), (key2785, 6), (key2808, -6), (key2859, -12), (key2869, 12)]

def row9898 : Integer.Sparse Key := [(key2631, 6), (key2705, -6), (key2785, 6), (key2808, -6), (key2859, -12), (key2869, 12)]

def row9899 : Integer.Sparse Key := [(key2631, 6), (key2705, -6), (key2785, 6), (key2808, -6), (key2859, -12), (key2869, 12)]

def row9900 : Integer.Sparse Key := [(key2631, 6), (key2705, -6), (key2785, 6), (key2808, -6), (key2859, -12), (key2869, 12)]

def row9901 : Integer.Sparse Key := [(key2631, 6), (key2705, -6), (key2785, 6), (key2808, -6), (key2859, -12), (key2869, 12)]

def row9902 : Integer.Sparse Key := [(key2631, 6), (key2705, -6), (key2785, 6), (key2808, -6), (key2859, -12), (key2869, 12)]

def row9903 : Integer.Sparse Key := [(key2631, 6), (key2705, -6), (key2785, 6), (key2808, -6), (key2859, -12), (key2869, 12)]

def row9904 : Integer.Sparse Key := [(key2631, 6), (key2705, -6), (key2785, 6), (key2808, -6), (key2859, -12), (key2869, 12)]

def row9905 : Integer.Sparse Key := [(key2631, 6), (key2705, -6), (key2785, 6), (key2808, -6), (key2859, -12), (key2869, 12)]

def row9906 : Integer.Sparse Key := [(key2631, 6), (key2705, -6), (key2785, 6), (key2808, -6), (key2859, -12), (key2869, 12)]

def row9907 : Integer.Sparse Key := [(key2631, 6), (key2705, -6), (key2785, 6), (key2808, -6), (key2859, -12), (key2869, 12)]

def row9908 : Integer.Sparse Key := [(key2631, 6), (key2705, -6), (key2785, 6), (key2808, -6), (key2859, -12), (key2869, 12)]

def row9909 : Integer.Sparse Key := [(key2617, -2), (key2620, -4), (key2633, 2), (key2643, 4), (key2707, 2), (key2730, 4), (key2810, -2), (key2833, -4), (key2952, -4), (key2962, -4), (key2964, -4), (key2978, 4), (key2985, 4), (key2994, 4)]

def row9910 : Integer.Sparse Key := [(key2617, -2), (key2620, -4), (key2633, 2), (key2643, 4), (key2707, 2), (key2730, 4), (key2810, -2), (key2833, -4), (key2952, -4), (key2962, -4), (key2964, -4), (key2978, 4), (key2985, 4), (key2994, 4)]

def row9911 : Integer.Sparse Key := [(key2617, -2), (key2620, -4), (key2633, 2), (key2643, 4), (key2707, 2), (key2730, 4), (key2810, -2), (key2833, -4), (key2952, -4), (key2962, -4), (key2964, -4), (key2978, 4), (key2985, 4), (key2994, 4)]

def row9912 : Integer.Sparse Key := [(key2617, -2), (key2620, -4), (key2633, 2), (key2643, 4), (key2707, 2), (key2730, 4), (key2810, -2), (key2833, -8), (key2962, -4), (key2964, -4), (key2978, 4), (key2985, 4), (key2994, 4)]

def row9913 : Integer.Sparse Key := [(key2617, -2), (key2620, -4), (key2633, 2), (key2643, 4), (key2707, 2), (key2730, 4), (key2810, -2), (key2833, -8), (key2962, -4), (key2964, -4), (key2978, 4), (key2985, 4), (key2994, 4)]

def row9914 : Integer.Sparse Key := [(key2617, -2), (key2620, -4), (key2633, 2), (key2643, 4), (key2707, 2), (key2730, 4), (key2810, -2), (key2833, -8), (key2962, -4), (key2964, -4), (key2978, 4), (key2985, 4), (key2994, 4)]

def row9915 : Integer.Sparse Key := [(key2617, -2), (key2620, -4), (key2633, 2), (key2643, 4), (key2707, 2), (key2730, 4), (key2810, -2), (key2833, -4), (key2952, -4), (key2962, -4), (key2964, -4), (key2978, 4), (key2985, 4), (key2994, 4)]

def row9916 : Integer.Sparse Key := [(key2617, -2), (key2620, -4), (key2633, 2), (key2643, 4), (key2707, 2), (key2730, 4), (key2810, -2), (key2833, -4), (key2952, -4), (key2962, -4), (key2964, -4), (key2978, 4), (key2985, 4), (key2994, 4)]

def row9917 : Integer.Sparse Key := [(key2617, -2), (key2620, -4), (key2633, 2), (key2643, 4), (key2707, 2), (key2730, 4), (key2810, -2), (key2833, -6), (key2952, -2), (key2962, -4), (key2964, -4), (key2978, 4), (key2985, 4), (key2994, 4)]

def row9918 : Integer.Sparse Key := [(key2617, -2), (key2620, -4), (key2633, 2), (key2643, 4), (key2707, 2), (key2730, 4), (key2810, -2), (key2833, -6), (key2952, -2), (key2962, -4), (key2964, -4), (key2978, 4), (key2985, 4), (key2994, 4)]

def row9919 : Integer.Sparse Key := [(key2617, -2), (key2620, -4), (key2633, 2), (key2643, 4), (key2707, 2), (key2730, 4), (key2810, -2), (key2833, -4), (key2952, -4), (key2962, -4), (key2964, -4), (key2978, 4), (key2985, 4), (key2994, 4)]

def row9920 : Integer.Sparse Key := [(key2617, -2), (key2620, -4), (key2633, 2), (key2643, 4), (key2707, 2), (key2730, 4), (key2810, -2), (key2833, -4), (key2952, -4), (key2962, -4), (key2964, -4), (key2978, 4), (key2985, 4), (key2994, 4)]

def row9921 : Integer.Sparse Key := [(key2617, 2), (key2633, -2), (key2643, -4), (key2655, 4), (key2672, 2), (key2707, -2), (key2730, -4), (key2749, 4), (key2945, 4), (key2962, 4), (key2978, -4), (key2985, -4), (key2994, -4), (key3004, 4)]

def row9922 : Integer.Sparse Key := [(key2617, 2), (key2633, -2), (key2643, -4), (key2655, 4), (key2672, 2), (key2707, -2), (key2730, -4), (key2749, 4), (key2945, 4), (key2962, 4), (key2978, -4), (key2985, -4), (key2994, -4), (key3004, 4)]

def row9923 : Integer.Sparse Key := [(key2617, 2), (key2633, -2), (key2643, -4), (key2655, 4), (key2672, 2), (key2707, -2), (key2730, -4), (key2749, 4), (key2945, 4), (key2962, 4), (key2978, -4), (key2985, -4), (key2994, -4), (key3004, 4)]

def row9924 : Integer.Sparse Key := [(key2617, 2), (key2633, -2), (key2643, -4), (key2655, 4), (key2672, 2), (key2707, -2), (key2730, -4), (key2749, 8), (key2962, 4), (key2978, -4), (key2985, -4), (key2994, -4), (key3004, 4)]

def row9925 : Integer.Sparse Key := [(key2617, 2), (key2633, -2), (key2643, -4), (key2655, 4), (key2672, 2), (key2707, -2), (key2730, -4), (key2749, 8), (key2962, 4), (key2978, -4), (key2985, -4), (key2994, -4), (key3004, 4)]

def row9926 : Integer.Sparse Key := [(key2617, 2), (key2633, -2), (key2643, -4), (key2655, 4), (key2672, 2), (key2707, -2), (key2730, -4), (key2749, 8), (key2962, 4), (key2978, -4), (key2985, -4), (key2994, -4), (key3004, 4)]

def row9927 : Integer.Sparse Key := [(key2617, 2), (key2633, -2), (key2643, -4), (key2655, 4), (key2672, 2), (key2707, -2), (key2730, -4), (key2749, 4), (key2945, 4), (key2962, 4), (key2978, -4), (key2985, -4), (key2994, -4), (key3004, 4)]

def row9928 : Integer.Sparse Key := [(key2617, 2), (key2633, -2), (key2643, -4), (key2655, 4), (key2672, 2), (key2707, -2), (key2730, -4), (key2749, 4), (key2945, 4), (key2962, 4), (key2978, -4), (key2985, -4), (key2994, -4), (key3004, 4)]

def row9929 : Integer.Sparse Key := [(key2617, 2), (key2633, -2), (key2643, -4), (key2655, 4), (key2672, 2), (key2707, -2), (key2730, -4), (key2749, 6), (key2945, 2), (key2962, 4), (key2978, -4), (key2985, -4), (key2994, -4), (key3004, 4)]

def row9930 : Integer.Sparse Key := [(key2617, 2), (key2633, -2), (key2643, -4), (key2655, 4), (key2672, 2), (key2707, -2), (key2730, -4), (key2749, 6), (key2945, 2), (key2962, 4), (key2978, -4), (key2985, -4), (key2994, -4), (key3004, 4)]

def row9931 : Integer.Sparse Key := [(key2617, 2), (key2633, -2), (key2643, -4), (key2655, 4), (key2672, 2), (key2707, -2), (key2730, -4), (key2749, 4), (key2945, 4), (key2962, 4), (key2978, -4), (key2985, -4), (key2994, -4), (key3004, 4)]

def row9932 : Integer.Sparse Key := [(key2617, 2), (key2633, -2), (key2643, -4), (key2655, 4), (key2672, 2), (key2707, -2), (key2730, -4), (key2749, 4), (key2945, 4), (key2962, 4), (key2978, -4), (key2985, -4), (key2994, -4), (key3004, 4)]

def row9933 : Integer.Sparse Key := [(key982, 2), (key988, -2), (key1096, 2), (key1100, -4), (key1175, -4), (key1185, 4), (key1186, -2), (key1222, 4)]

def row9957 : Integer.Sparse Key := [(key8, 6), (key91, -18), (key152, 12)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block72
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row6171 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key251, -2), (key260, 2), (key271, -1), (key302, 1), (key305, -1), (key316, -1), (key319, 1), (key328, -1), (key340, 1), (key385, -1), (key388, 2), (key397, -1), (key406, 1), (key409, -1), (key467, -1), (key469, 1), (key593, 1), (key595, -1)]

def row6172 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key251, 1), (key302, -1), (key305, 1), (key316, 1), (key319, -2), (key328, 1), (key340, -1), (key385, 1), (key388, -1), (key397, 1), (key406, -1), (key409, 2), (key418, -2), (key467, -1), (key475, 1), (key583, 1), (key593, 1), (key601, -1)]

def row6173 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key251, 1), (key302, -1), (key305, 1), (key316, 1), (key319, -2), (key328, 1), (key340, -1), (key385, 1), (key388, -1), (key397, 1), (key406, -1), (key409, 2), (key418, -2), (key467, -1), (key475, 1), (key583, 1), (key593, 1), (key601, -1)]

def row6174 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key251, 1), (key302, -1), (key305, 1), (key319, -2), (key328, 1), (key335, 1), (key340, -1), (key385, 2), (key388, -1), (key406, -1), (key409, 2), (key418, -1), (key467, -1), (key475, 1), (key578, -1), (key583, 1), (key593, 1), (key601, -1)]

def row6175 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key251, 1), (key302, -1), (key305, 1), (key319, -2), (key328, 1), (key335, 1), (key340, -1), (key385, 2), (key388, -1), (key406, -1), (key409, 2), (key418, -1), (key467, -1), (key475, 1), (key578, -1), (key583, 1), (key593, 1), (key601, -1)]

def row6176 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key251, -2), (key260, 1), (key267, 1), (key271, -1), (key302, 1), (key305, -1), (key316, -1), (key319, 1), (key385, -1), (key388, 2), (key397, -1), (key406, 1), (key409, -1), (key467, -1), (key469, 1), (key568, -1), (key572, 1), (key593, 1), (key595, -1)]

def row6177 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key251, -2), (key260, 1), (key267, 1), (key271, -1), (key302, 1), (key305, -1), (key316, -1), (key319, 1), (key385, -1), (key388, 2), (key397, -1), (key406, 1), (key409, -1), (key467, -1), (key469, 1), (key568, -1), (key572, 1), (key593, 1), (key595, -1)]

def row6178 : Integer.Sparse Key := [(key2630, 1), (key2638, -3), (key2657, 1), (key2659, 1), (key2698, 2), (key2704, 1), (key2724, -1), (key2752, -1), (key2757, -1), (key2778, -2), (key2784, -1), (key2792, 1), (key2807, -1), (key2827, 3), (key2918, 2), (key2919, -1), (key2922, -1), (key3007, 1), (key3009, 1), (key3011, -1), (key3016, -1), (key3021, -2), (key3022, 1), (key3025, 1)]

def row6179 : Integer.Sparse Key := [(key2630, 1), (key2638, -3), (key2657, 1), (key2659, 1), (key2698, 2), (key2704, 1), (key2724, -1), (key2752, -1), (key2757, -1), (key2778, -2), (key2784, -1), (key2792, 1), (key2807, -1), (key2827, 3), (key2918, 2), (key2919, -1), (key2922, -1), (key3007, 1), (key3009, 1), (key3011, -1), (key3016, -1), (key3021, -2), (key3022, 1), (key3025, 1)]

def row6180 : Integer.Sparse Key := [(key2630, 1), (key2638, -3), (key2657, 1), (key2659, 1), (key2698, 1), (key2704, 1), (key2752, -2), (key2778, -1), (key2784, -1), (key2792, 2), (key2807, -1), (key2827, 3), (key2918, 2), (key2919, -1), (key2922, -1), (key3011, -1), (key3016, -1), (key3021, -2), (key3022, 1), (key3025, 1)]

def row6181 : Integer.Sparse Key := [(key2630, 1), (key2638, -3), (key2657, 1), (key2659, 1), (key2698, 1), (key2704, 1), (key2752, -2), (key2778, -1), (key2784, -1), (key2792, 2), (key2807, -1), (key2827, 3), (key2918, 2), (key2919, -1), (key2922, -1), (key3011, -1), (key3016, -1), (key3021, -2), (key3022, 1), (key3025, 1)]

def row6182 : Integer.Sparse Key := [(key2630, 1), (key2638, -2), (key2659, 1), (key2704, 1), (key2757, 1), (key2784, -1), (key2807, -1), (key2827, 2), (key2918, 2), (key2919, -1), (key2922, -1), (key3009, -1), (key3016, -1), (key3021, -2), (key3022, 1), (key3025, 1)]

def row6183 : Integer.Sparse Key := [(key2630, 1), (key2638, -2), (key2659, 1), (key2704, 1), (key2757, 1), (key2784, -1), (key2807, -1), (key2827, 2), (key2918, 2), (key2919, -1), (key2922, -1), (key3009, -1), (key3016, -1), (key3021, -2), (key3022, 1), (key3025, 1)]

def row6184 : Integer.Sparse Key := [(key2630, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2704, 1), (key2724, -1), (key2752, -1), (key2757, 1), (key2784, -1), (key2792, 1), (key2807, -1), (key2827, 1), (key2918, 2), (key2919, -1), (key2922, -1), (key3007, 1), (key3009, -1), (key3011, 1), (key3016, -1), (key3021, -2), (key3022, 1), (key3025, 1)]

def row6185 : Integer.Sparse Key := [(key2630, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2704, 1), (key2724, -1), (key2752, -1), (key2757, 1), (key2784, -1), (key2792, 1), (key2807, -1), (key2827, 1), (key2918, 2), (key2919, -1), (key2922, -1), (key3007, 1), (key3009, -1), (key3011, 1), (key3016, -1), (key3021, -2), (key3022, 1), (key3025, 1)]

def row6186 : Integer.Sparse Key := [(key2630, -2), (key2638, 2), (key2657, 2), (key2659, -2), (key2704, -2), (key2724, 2), (key2752, 2), (key2757, -2), (key2784, 2), (key2792, -2), (key2807, 2), (key2827, -2), (key2918, -4), (key2919, 2), (key2922, 2), (key3007, -2), (key3009, 2), (key3011, -2), (key3016, 2), (key3021, 4), (key3022, -2), (key3025, -2)]

def row6187 : Integer.Sparse Key := [(key2630, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2704, 1), (key2724, -1), (key2752, -1), (key2757, 1), (key2784, -1), (key2792, 1), (key2807, -1), (key2827, 1), (key2918, 2), (key2919, -1), (key2922, -1), (key3007, 1), (key3009, -1), (key3011, 1), (key3016, -1), (key3021, -2), (key3022, 1), (key3025, 1)]

def row6188 : Integer.Sparse Key := [(key2630, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2704, 1), (key2724, -1), (key2752, -1), (key2757, 1), (key2784, -1), (key2792, 1), (key2807, -1), (key2827, 1), (key2918, 2), (key2919, -1), (key2922, -1), (key3007, 1), (key3009, -1), (key3011, 1), (key3016, -1), (key3021, -2), (key3022, 1), (key3025, 1)]

def row6189 : Integer.Sparse Key := [(key2630, -2), (key2638, 2), (key2657, 2), (key2659, -2), (key2704, -2), (key2724, 2), (key2752, 2), (key2757, -2), (key2784, 2), (key2792, -2), (key2807, 2), (key2827, -2), (key2918, -4), (key2919, 2), (key2922, 2), (key3007, -2), (key3009, 2), (key3011, -2), (key3016, 2), (key3021, 4), (key3022, -2), (key3025, -2)]

def row6190 : Integer.Sparse Key := [(key2630, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2704, 1), (key2724, -1), (key2752, -1), (key2757, 1), (key2784, -1), (key2792, 1), (key2807, -1), (key2827, 1), (key2918, 2), (key2919, -1), (key2922, -1), (key3007, 1), (key3009, -1), (key3011, 1), (key3016, -1), (key3021, -2), (key3022, 1), (key3025, 1)]

def row6191 : Integer.Sparse Key := [(key2630, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2704, 1), (key2724, -1), (key2752, -1), (key2757, 1), (key2784, -1), (key2792, 1), (key2807, -1), (key2827, 1), (key2918, 2), (key2919, -1), (key2922, -1), (key3007, 1), (key3009, -1), (key3011, 1), (key3016, -1), (key3021, -2), (key3022, 1), (key3025, 1)]

def row6192 : Integer.Sparse Key := [(key2630, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2704, 1), (key2724, -1), (key2752, -1), (key2757, 1), (key2784, -1), (key2792, 1), (key2807, -1), (key2827, 1), (key2918, 2), (key2919, -1), (key2922, -1), (key3007, 1), (key3009, -1), (key3011, 1), (key3016, -1), (key3021, -2), (key3022, 1), (key3025, 1)]

def row6193 : Integer.Sparse Key := [(key2630, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2704, 1), (key2724, -1), (key2752, -1), (key2757, 1), (key2784, -1), (key2792, 1), (key2807, -1), (key2827, 1), (key2918, 2), (key2919, -1), (key2922, -1), (key3007, 1), (key3009, -1), (key3011, 1), (key3016, -1), (key3021, -2), (key3022, 1), (key3025, 1)]

def row6194 : Integer.Sparse Key := [(key2630, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2704, 1), (key2724, -1), (key2752, -1), (key2757, 1), (key2784, -1), (key2792, 1), (key2807, -1), (key2827, 1), (key2918, 2), (key2919, -1), (key2922, -1), (key3007, 1), (key3009, -1), (key3011, 1), (key3016, -1), (key3021, -2), (key3022, 1), (key3025, 1)]

def row6195 : Integer.Sparse Key := [(key2630, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2704, 1), (key2724, -1), (key2752, -1), (key2757, 1), (key2784, -1), (key2792, 1), (key2807, -1), (key2827, 1), (key2918, 2), (key2919, -1), (key2922, -1), (key3007, 1), (key3009, -1), (key3011, 1), (key3016, -1), (key3021, -2), (key3022, 1), (key3025, 1)]

def row6196 : Integer.Sparse Key := [(key2630, -2), (key2638, 2), (key2657, 2), (key2659, -2), (key2704, -2), (key2724, 2), (key2752, 2), (key2757, -2), (key2784, 2), (key2792, -2), (key2807, 2), (key2827, -2), (key2918, -4), (key2919, 2), (key2922, 2), (key3007, -2), (key3009, 2), (key3011, -2), (key3016, 2), (key3021, 4), (key3022, -2), (key3025, -2)]

def row6197 : Integer.Sparse Key := [(key2630, -2), (key2638, 2), (key2657, 2), (key2659, -2), (key2704, -2), (key2724, 2), (key2752, 2), (key2757, -2), (key2784, 2), (key2792, -2), (key2807, 2), (key2827, -2), (key2918, -4), (key2919, 2), (key2922, 2), (key3007, -2), (key3009, 2), (key3011, -2), (key3016, 2), (key3021, 4), (key3022, -2), (key3025, -2)]

def row6198 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -2), (key1445, 1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, -1), (key1568, -1), (key1576, 2), (key1594, -1), (key1682, -1), (key1690, 1), (key1904, -1), (key1912, 1), (key1919, 1), (key1927, -1)]

def row6199 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -2), (key1445, 1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, -1), (key1568, -1), (key1576, 2), (key1594, -1), (key1682, -1), (key1690, 1), (key1904, -1), (key1912, 1), (key1919, 1), (key1927, -1)]

def row6200 : Integer.Sparse Key := [(key1291, -2), (key1299, 2), (key1311, 2), (key1319, -2), (key1386, 2), (key1394, -2), (key1419, -2), (key1427, 4), (key1445, -2), (key1473, -2), (key1481, 2), (key1541, -2), (key1549, 2), (key1568, 2), (key1576, -4), (key1594, 2), (key1682, 2), (key1690, -2), (key1904, 2), (key1912, -2), (key1919, -2), (key1927, 2)]

def row6201 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -2), (key1445, 1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, -1), (key1568, -1), (key1576, 2), (key1594, -1), (key1682, -1), (key1690, 1), (key1904, -1), (key1912, 1), (key1919, 1), (key1927, -1)]

def row6202 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -2), (key1445, 1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, -1), (key1568, -1), (key1576, 2), (key1594, -1), (key1682, -1), (key1690, 1), (key1904, -1), (key1912, 1), (key1919, 1), (key1927, -1)]

def row6203 : Integer.Sparse Key := [(key1291, -2), (key1299, 2), (key1311, 2), (key1319, -2), (key1386, 2), (key1394, -2), (key1419, -2), (key1427, 4), (key1445, -2), (key1473, -2), (key1481, 2), (key1541, -2), (key1549, 2), (key1568, 2), (key1576, -4), (key1594, 2), (key1682, 2), (key1690, -2), (key1904, 2), (key1912, -2), (key1919, -2), (key1927, 2)]

def row6204 : Integer.Sparse Key := [(key1291, -2), (key1299, 2), (key1311, 2), (key1319, -2), (key1386, 2), (key1394, -2), (key1419, -2), (key1427, 4), (key1445, -2), (key1473, -2), (key1481, 2), (key1541, -2), (key1549, 2), (key1568, 2), (key1576, -4), (key1594, 2), (key1682, 2), (key1690, -2), (key1904, 2), (key1912, -2), (key1919, -2), (key1927, 2)]

def row6205 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -2), (key1445, 1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, -1), (key1568, -1), (key1576, 2), (key1594, -1), (key1682, -1), (key1690, 1), (key1904, -1), (key1912, 1), (key1919, 1), (key1927, -1)]

def row6206 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -2), (key1445, 1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, -1), (key1568, -1), (key1576, 2), (key1594, -1), (key1682, -1), (key1690, 1), (key1904, -1), (key1912, 1), (key1919, 1), (key1927, -1)]

def row6207 : Integer.Sparse Key := [(key1291, -2), (key1299, 2), (key1311, 2), (key1319, -2), (key1386, 2), (key1394, -2), (key1419, -2), (key1427, 4), (key1445, -2), (key1473, -2), (key1481, 2), (key1541, -2), (key1549, 2), (key1568, 2), (key1576, -4), (key1594, 2), (key1682, 2), (key1690, -2), (key1904, 2), (key1912, -2), (key1919, -2), (key1927, 2)]

def row6208 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -2), (key1445, 1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, -1), (key1568, -1), (key1576, 2), (key1594, -1), (key1682, -1), (key1690, 1), (key1904, -1), (key1912, 1), (key1919, 1), (key1927, -1)]

def row6209 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -2), (key1445, 1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, -1), (key1568, -1), (key1576, 2), (key1594, -1), (key1682, -1), (key1690, 1), (key1904, -1), (key1912, 1), (key1919, 1), (key1927, -1)]

def row6210 : Integer.Sparse Key := [(key1319, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1427, 1), (key1445, -1), (key1473, -1), (key1481, 1), (key1549, -1), (key1557, 1), (key1576, -1), (key1594, 1), (key1682, 2), (key1684, -1), (key1690, -1), (key1897, 1), (key1900, -1), (key1904, 1), (key1912, -1), (key1919, -2), (key1921, 1), (key1927, 1)]

def row6211 : Integer.Sparse Key := [(key1319, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1427, 1), (key1445, -1), (key1473, -1), (key1481, 1), (key1549, -1), (key1557, 1), (key1576, -1), (key1594, 1), (key1682, 2), (key1684, -1), (key1690, -1), (key1897, 1), (key1900, -1), (key1904, 1), (key1912, -1), (key1919, -2), (key1921, 1), (key1927, 1)]

def row6212 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -2), (key1445, 1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, -1), (key1568, -1), (key1576, 2), (key1594, -1), (key1682, -1), (key1690, 1), (key1904, -1), (key1912, 1), (key1919, 1), (key1927, -1)]

def row6213 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -2), (key1445, 1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, -1), (key1568, -1), (key1576, 2), (key1594, -1), (key1682, -1), (key1690, 1), (key1904, -1), (key1912, 1), (key1919, 1), (key1927, -1)]

def row6214 : Integer.Sparse Key := [(key1319, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1427, 1), (key1445, -1), (key1473, -1), (key1481, 1), (key1549, -1), (key1557, 1), (key1576, -1), (key1594, 1), (key1682, 2), (key1684, -1), (key1690, -1), (key1897, 1), (key1900, -1), (key1904, 1), (key1912, -1), (key1919, -2), (key1921, 1), (key1927, 1)]

def row6215 : Integer.Sparse Key := [(key1319, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1427, 1), (key1445, -1), (key1473, -1), (key1481, 1), (key1549, -1), (key1557, 1), (key1576, -1), (key1594, 1), (key1682, 2), (key1684, -1), (key1690, -1), (key1897, 1), (key1900, -1), (key1904, 1), (key1912, -1), (key1919, -2), (key1921, 1), (key1927, 1)]

def row6216 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -2), (key1445, 1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, -1), (key1568, -1), (key1576, 2), (key1594, -1), (key1682, -1), (key1690, 1), (key1904, -1), (key1912, 1), (key1919, 1), (key1927, -1)]

def row6217 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -2), (key1445, 1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, -1), (key1568, -1), (key1576, 2), (key1594, -1), (key1682, -1), (key1690, 1), (key1904, -1), (key1912, 1), (key1919, 1), (key1927, -1)]

def row6218 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -2), (key1445, 1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, -1), (key1568, -1), (key1576, 2), (key1594, -1), (key1682, -1), (key1690, 1), (key1904, -1), (key1912, 1), (key1919, 1), (key1927, -1)]

def row6219 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -2), (key1445, 1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, -1), (key1568, -1), (key1576, 2), (key1594, -1), (key1682, -1), (key1690, 1), (key1904, -1), (key1912, 1), (key1919, 1), (key1927, -1)]

def row6220 : Integer.Sparse Key := [(key1319, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1427, 1), (key1445, -1), (key1473, -1), (key1481, 1), (key1549, -1), (key1557, 1), (key1576, -1), (key1594, 1), (key1682, 2), (key1684, -1), (key1690, -1), (key1897, 1), (key1900, -1), (key1904, 1), (key1912, -1), (key1919, -2), (key1921, 1), (key1927, 1)]

def row6221 : Integer.Sparse Key := [(key1319, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1427, 1), (key1445, -1), (key1473, -1), (key1481, 1), (key1549, -1), (key1557, 1), (key1576, -1), (key1594, 1), (key1682, 2), (key1684, -1), (key1690, -1), (key1897, 1), (key1900, -1), (key1904, 1), (key1912, -1), (key1919, -2), (key1921, 1), (key1927, 1)]

def row6222 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -2), (key1445, 1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, -1), (key1568, -1), (key1576, 2), (key1594, -1), (key1682, -1), (key1690, 1), (key1904, -1), (key1912, 1), (key1919, 1), (key1927, -1)]

def row6223 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -2), (key1445, 1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, -1), (key1568, -1), (key1576, 2), (key1594, -1), (key1682, -1), (key1690, 1), (key1904, -1), (key1912, 1), (key1919, 1), (key1927, -1)]

def row6224 : Integer.Sparse Key := [(key1319, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1427, 1), (key1445, -1), (key1473, -1), (key1481, 1), (key1549, -1), (key1557, 1), (key1576, -1), (key1594, 1), (key1682, 2), (key1684, -1), (key1690, -1), (key1897, 1), (key1900, -1), (key1904, 1), (key1912, -1), (key1919, -2), (key1921, 1), (key1927, 1)]

def row6225 : Integer.Sparse Key := [(key1319, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1427, 1), (key1445, -1), (key1473, -1), (key1481, 1), (key1549, -1), (key1557, 1), (key1576, -1), (key1594, 1), (key1682, 2), (key1684, -1), (key1690, -1), (key1897, 1), (key1900, -1), (key1904, 1), (key1912, -1), (key1919, -2), (key1921, 1), (key1927, 1)]

def row6226 : Integer.Sparse Key := [(key1319, -2), (key1327, 2), (key1352, 2), (key1355, -2), (key1427, -2), (key1445, 2), (key1473, 2), (key1481, -2), (key1549, 2), (key1557, -2), (key1576, 2), (key1594, -2), (key1682, -4), (key1684, 2), (key1690, 2), (key1897, -2), (key1900, 2), (key1904, -2), (key1912, 2), (key1919, 4), (key1921, -2), (key1927, -2)]

def row6227 : Integer.Sparse Key := [(key1319, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1427, 1), (key1445, -1), (key1473, -1), (key1481, 1), (key1549, -1), (key1557, 1), (key1576, -1), (key1594, 1), (key1682, 2), (key1684, -1), (key1690, -1), (key1897, 1), (key1900, -1), (key1904, 1), (key1912, -1), (key1919, -2), (key1921, 1), (key1927, 1)]

def row6228 : Integer.Sparse Key := [(key1319, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1427, 1), (key1445, -1), (key1473, -1), (key1481, 1), (key1549, -1), (key1557, 1), (key1576, -1), (key1594, 1), (key1682, 2), (key1684, -1), (key1690, -1), (key1897, 1), (key1900, -1), (key1904, 1), (key1912, -1), (key1919, -2), (key1921, 1), (key1927, 1)]

def row6229 : Integer.Sparse Key := [(key1319, -2), (key1327, 2), (key1352, 2), (key1355, -2), (key1427, -2), (key1445, 2), (key1473, 2), (key1481, -2), (key1549, 2), (key1557, -2), (key1576, 2), (key1594, -2), (key1682, -4), (key1684, 2), (key1690, 2), (key1897, -2), (key1900, 2), (key1904, -2), (key1912, 2), (key1919, 4), (key1921, -2), (key1927, -2)]

def row6230 : Integer.Sparse Key := [(key1319, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1427, 1), (key1445, -1), (key1473, -1), (key1481, 1), (key1549, -1), (key1557, 1), (key1576, -1), (key1594, 1), (key1682, 2), (key1684, -1), (key1690, -1), (key1897, 1), (key1900, -1), (key1904, 1), (key1912, -1), (key1919, -2), (key1921, 1), (key1927, 1)]

def row6231 : Integer.Sparse Key := [(key1319, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1427, 1), (key1445, -1), (key1473, -1), (key1481, 1), (key1549, -1), (key1557, 1), (key1576, -1), (key1594, 1), (key1682, 2), (key1684, -1), (key1690, -1), (key1897, 1), (key1900, -1), (key1904, 1), (key1912, -1), (key1919, -2), (key1921, 1), (key1927, 1)]

def row6232 : Integer.Sparse Key := [(key1319, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1427, 1), (key1445, -1), (key1473, -1), (key1481, 1), (key1549, -1), (key1557, 1), (key1576, -1), (key1594, 1), (key1682, 2), (key1684, -1), (key1690, -1), (key1897, 1), (key1900, -1), (key1904, 1), (key1912, -1), (key1919, -2), (key1921, 1), (key1927, 1)]

def row6233 : Integer.Sparse Key := [(key1319, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1427, 1), (key1445, -1), (key1473, -1), (key1481, 1), (key1549, -1), (key1557, 1), (key1576, -1), (key1594, 1), (key1682, 2), (key1684, -1), (key1690, -1), (key1897, 1), (key1900, -1), (key1904, 1), (key1912, -1), (key1919, -2), (key1921, 1), (key1927, 1)]

def row6234 : Integer.Sparse Key := [(key1319, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1427, 1), (key1445, -1), (key1473, -1), (key1481, 1), (key1549, -1), (key1557, 1), (key1576, -1), (key1594, 1), (key1682, 2), (key1684, -1), (key1690, -1), (key1897, 1), (key1900, -1), (key1904, 1), (key1912, -1), (key1919, -2), (key1921, 1), (key1927, 1)]

def row6235 : Integer.Sparse Key := [(key1319, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1427, 1), (key1445, -1), (key1473, -1), (key1481, 1), (key1549, -1), (key1557, 1), (key1576, -1), (key1594, 1), (key1682, 2), (key1684, -1), (key1690, -1), (key1897, 1), (key1900, -1), (key1904, 1), (key1912, -1), (key1919, -2), (key1921, 1), (key1927, 1)]

def row6236 : Integer.Sparse Key := [(key1319, -2), (key1327, 2), (key1352, 2), (key1355, -2), (key1427, -2), (key1445, 2), (key1473, 2), (key1481, -2), (key1549, 2), (key1557, -2), (key1576, 2), (key1594, -2), (key1682, -4), (key1684, 2), (key1690, 2), (key1897, -2), (key1900, 2), (key1904, -2), (key1912, 2), (key1919, 4), (key1921, -2), (key1927, -2)]

def row6237 : Integer.Sparse Key := [(key1319, -2), (key1327, 2), (key1352, 2), (key1355, -2), (key1427, -2), (key1445, 2), (key1473, 2), (key1481, -2), (key1549, 2), (key1557, -2), (key1576, 2), (key1594, -2), (key1682, -4), (key1684, 2), (key1690, 2), (key1897, -2), (key1900, 2), (key1904, -2), (key1912, 2), (key1919, 4), (key1921, -2), (key1927, -2)]

def row6238 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, 2), (key2826, -1), (key2857, -1), (key2867, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row6239 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, 2), (key2826, -1), (key2857, -1), (key2867, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row6240 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, 2), (key2629, -2), (key2664, 2), (key2668, -2), (key2699, -2), (key2703, 2), (key2779, -2), (key2783, 4), (key2791, -2), (key2802, 2), (key2806, -4), (key2826, 2), (key2857, 2), (key2867, -2), (key2937, -2), (key2942, 2), (key2949, 2), (key2959, -2), (key2975, -2), (key2982, 2)]

def row6241 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, 2), (key2826, -1), (key2857, -1), (key2867, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row6242 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, 2), (key2826, -1), (key2857, -1), (key2867, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row6243 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, 2), (key2629, -2), (key2664, 2), (key2668, -2), (key2699, -2), (key2703, 2), (key2779, -2), (key2783, 4), (key2791, -2), (key2802, 2), (key2806, -4), (key2826, 2), (key2857, 2), (key2867, -2), (key2937, -2), (key2942, 2), (key2949, 2), (key2959, -2), (key2975, -2), (key2982, 2)]

def row6244 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, 2), (key2629, -2), (key2664, 2), (key2668, -2), (key2699, -2), (key2703, 2), (key2779, -2), (key2783, 4), (key2791, -2), (key2802, 2), (key2806, -4), (key2826, 2), (key2857, 2), (key2867, -2), (key2937, -2), (key2942, 2), (key2949, 2), (key2959, -2), (key2975, -2), (key2982, 2)]

def row6245 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, 2), (key2826, -1), (key2857, -1), (key2867, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row6246 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, 2), (key2826, -1), (key2857, -1), (key2867, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row6247 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, 2), (key2629, -2), (key2664, 2), (key2668, -2), (key2699, -2), (key2703, 2), (key2779, -2), (key2783, 4), (key2791, -2), (key2802, 2), (key2806, -4), (key2826, 2), (key2857, 2), (key2867, -2), (key2937, -2), (key2942, 2), (key2949, 2), (key2959, -2), (key2975, -2), (key2982, 2)]

def row6248 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, 2), (key2826, -1), (key2857, -1), (key2867, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row6249 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, 2), (key2826, -1), (key2857, -1), (key2867, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row6250 : Integer.Sparse Key := [(key2629, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2703, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2783, 1), (key2791, -1), (key2806, -1), (key2826, 1), (key2857, 2), (key2867, -2), (key2896, -1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row6251 : Integer.Sparse Key := [(key2629, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2703, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2783, 1), (key2791, -1), (key2806, -1), (key2826, 1), (key2857, 2), (key2867, -2), (key2896, -1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row6252 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, 2), (key2826, -1), (key2857, -1), (key2867, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row6253 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, 2), (key2826, -1), (key2857, -1), (key2867, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row6254 : Integer.Sparse Key := [(key2629, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2703, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2783, 1), (key2791, -1), (key2806, -1), (key2826, 1), (key2857, 2), (key2867, -2), (key2896, -1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row6255 : Integer.Sparse Key := [(key2629, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2703, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2783, 1), (key2791, -1), (key2806, -1), (key2826, 1), (key2857, 2), (key2867, -2), (key2896, -1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row6256 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, 2), (key2826, -1), (key2857, -1), (key2867, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row6257 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, 2), (key2826, -1), (key2857, -1), (key2867, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row6258 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, 2), (key2826, -1), (key2857, -1), (key2867, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row6259 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, 2), (key2826, -1), (key2857, -1), (key2867, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row6260 : Integer.Sparse Key := [(key2629, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2703, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2783, 1), (key2791, -1), (key2806, -1), (key2826, 1), (key2857, 2), (key2867, -2), (key2896, -1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row6261 : Integer.Sparse Key := [(key2629, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2703, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2783, 1), (key2791, -1), (key2806, -1), (key2826, 1), (key2857, 2), (key2867, -2), (key2896, -1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row6262 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, 2), (key2826, -1), (key2857, -1), (key2867, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row6263 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, 2), (key2826, -1), (key2857, -1), (key2867, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row6264 : Integer.Sparse Key := [(key2629, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2703, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2783, 1), (key2791, -1), (key2806, -1), (key2826, 1), (key2857, 2), (key2867, -2), (key2896, -1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row6265 : Integer.Sparse Key := [(key2629, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2703, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2783, 1), (key2791, -1), (key2806, -1), (key2826, 1), (key2857, 2), (key2867, -2), (key2896, -1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row6266 : Integer.Sparse Key := [(key2629, -2), (key2637, 2), (key2647, 2), (key2652, -2), (key2703, 2), (key2723, -2), (key2736, -2), (key2746, 2), (key2783, -2), (key2791, 2), (key2806, 2), (key2826, -2), (key2857, -4), (key2867, 4), (key2896, 2), (key2903, -2), (key2937, 2), (key2942, -2), (key2949, -2), (key2959, 2), (key2975, 2), (key2982, -2)]

def row6267 : Integer.Sparse Key := [(key2629, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2703, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2783, 1), (key2791, -1), (key2806, -1), (key2826, 1), (key2857, 2), (key2867, -2), (key2896, -1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row6268 : Integer.Sparse Key := [(key2629, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2703, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2783, 1), (key2791, -1), (key2806, -1), (key2826, 1), (key2857, 2), (key2867, -2), (key2896, -1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row6269 : Integer.Sparse Key := [(key2629, -2), (key2637, 2), (key2647, 2), (key2652, -2), (key2703, 2), (key2723, -2), (key2736, -2), (key2746, 2), (key2783, -2), (key2791, 2), (key2806, 2), (key2826, -2), (key2857, -4), (key2867, 4), (key2896, 2), (key2903, -2), (key2937, 2), (key2942, -2), (key2949, -2), (key2959, 2), (key2975, 2), (key2982, -2)]

def row6270 : Integer.Sparse Key := [(key2629, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2703, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2783, 1), (key2791, -1), (key2806, -1), (key2826, 1), (key2857, 2), (key2867, -2), (key2896, -1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row6271 : Integer.Sparse Key := [(key2629, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2703, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2783, 1), (key2791, -1), (key2806, -1), (key2826, 1), (key2857, 2), (key2867, -2), (key2896, -1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block73
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row6272 : Integer.Sparse Key := [(key2629, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2703, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2783, 1), (key2791, -1), (key2806, -1), (key2826, 1), (key2857, 2), (key2867, -2), (key2896, -1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row6273 : Integer.Sparse Key := [(key2629, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2703, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2783, 1), (key2791, -1), (key2806, -1), (key2826, 1), (key2857, 2), (key2867, -2), (key2896, -1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row6274 : Integer.Sparse Key := [(key2629, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2703, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2783, 1), (key2791, -1), (key2806, -1), (key2826, 1), (key2857, 2), (key2867, -2), (key2896, -1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row6275 : Integer.Sparse Key := [(key2629, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2703, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2783, 1), (key2791, -1), (key2806, -1), (key2826, 1), (key2857, 2), (key2867, -2), (key2896, -1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row6276 : Integer.Sparse Key := [(key2629, -2), (key2637, 2), (key2647, 2), (key2652, -2), (key2703, 2), (key2723, -2), (key2736, -2), (key2746, 2), (key2783, -2), (key2791, 2), (key2806, 2), (key2826, -2), (key2857, -4), (key2867, 4), (key2896, 2), (key2903, -2), (key2937, 2), (key2942, -2), (key2949, -2), (key2959, 2), (key2975, 2), (key2982, -2)]

def row6277 : Integer.Sparse Key := [(key2629, -2), (key2637, 2), (key2647, 2), (key2652, -2), (key2703, 2), (key2723, -2), (key2736, -2), (key2746, 2), (key2783, -2), (key2791, 2), (key2806, 2), (key2826, -2), (key2857, -4), (key2867, 4), (key2896, 2), (key2903, -2), (key2937, 2), (key2942, -2), (key2949, -2), (key2959, 2), (key2975, 2), (key2982, -2)]

def row6279 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1116, 1), (key1125, 1), (key1130, -2), (key1152, -2), (key1159, 1), (key1174, 1), (key1233, -1), (key1236, 1), (key1243, 1), (key1247, -1)]

def row6280 : Integer.Sparse Key := [(key1003, -2), (key1009, 2), (key1017, 2), (key1022, -2), (key1038, 4), (key1044, -4), (key1073, -4), (key1080, 4), (key1116, -2), (key1125, -2), (key1130, 4), (key1152, 4), (key1159, -2), (key1174, -2), (key1233, 2), (key1236, -2), (key1243, -2), (key1247, 2)]

def row6281 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1116, 1), (key1125, 1), (key1130, -2), (key1152, -2), (key1159, 1), (key1174, 1), (key1233, -1), (key1236, 1), (key1243, 1), (key1247, -1)]

def row6282 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1116, 1), (key1125, 1), (key1130, -2), (key1152, -2), (key1159, 1), (key1174, 1), (key1233, -1), (key1236, 1), (key1243, 1), (key1247, -1)]

def row6283 : Integer.Sparse Key := [(key1003, -2), (key1009, 2), (key1017, 2), (key1022, -2), (key1038, 4), (key1044, -4), (key1073, -4), (key1080, 4), (key1116, -2), (key1125, -2), (key1130, 4), (key1152, 4), (key1159, -2), (key1174, -2), (key1233, 2), (key1236, -2), (key1243, -2), (key1247, 2)]

def row6284 : Integer.Sparse Key := [(key1003, -2), (key1009, 2), (key1017, 2), (key1022, -2), (key1038, 4), (key1044, -4), (key1073, -4), (key1080, 4), (key1116, -2), (key1125, -2), (key1130, 4), (key1152, 4), (key1159, -2), (key1174, -2), (key1233, 2), (key1236, -2), (key1243, -2), (key1247, 2)]

def row6285 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1116, 1), (key1125, 1), (key1130, -2), (key1152, -2), (key1159, 1), (key1174, 1), (key1233, -1), (key1236, 1), (key1243, 1), (key1247, -1)]

def row6286 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1116, 1), (key1125, 1), (key1130, -2), (key1152, -2), (key1159, 1), (key1174, 1), (key1233, -1), (key1236, 1), (key1243, 1), (key1247, -1)]

def row6287 : Integer.Sparse Key := [(key1003, -2), (key1009, 2), (key1017, 2), (key1022, -2), (key1038, 4), (key1044, -4), (key1073, -4), (key1080, 4), (key1116, -2), (key1125, -2), (key1130, 4), (key1152, 4), (key1159, -2), (key1174, -2), (key1233, 2), (key1236, -2), (key1243, -2), (key1247, 2)]

def row6288 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1116, 1), (key1125, 1), (key1130, -2), (key1152, -2), (key1159, 1), (key1174, 1), (key1233, -1), (key1236, 1), (key1243, 1), (key1247, -1)]

def row6289 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1116, 1), (key1125, 1), (key1130, -2), (key1152, -2), (key1159, 1), (key1174, 1), (key1233, -1), (key1236, 1), (key1243, 1), (key1247, -1)]

def row6290 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1116, -2), (key1125, 1), (key1130, 1), (key1152, 1), (key1159, 1), (key1174, -2), (key1233, 2), (key1236, -2), (key1243, -2), (key1247, 2)]

def row6291 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1116, -2), (key1125, 1), (key1130, 1), (key1152, 1), (key1159, 1), (key1174, -2), (key1233, 2), (key1236, -2), (key1243, -2), (key1247, 2)]

def row6292 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1116, 1), (key1125, 1), (key1130, -2), (key1152, -2), (key1159, 1), (key1174, 1), (key1233, -1), (key1236, 1), (key1243, 1), (key1247, -1)]

def row6293 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1116, 1), (key1125, 1), (key1130, -2), (key1152, -2), (key1159, 1), (key1174, 1), (key1233, -1), (key1236, 1), (key1243, 1), (key1247, -1)]

def row6294 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1116, -2), (key1125, 1), (key1130, 1), (key1152, 1), (key1159, 1), (key1174, -2), (key1233, 2), (key1236, -2), (key1243, -2), (key1247, 2)]

def row6295 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1116, -2), (key1125, 1), (key1130, 1), (key1152, 1), (key1159, 1), (key1174, -2), (key1233, 2), (key1236, -2), (key1243, -2), (key1247, 2)]

def row6296 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1116, 1), (key1125, 1), (key1130, -2), (key1152, -2), (key1159, 1), (key1174, 1), (key1233, -1), (key1236, 1), (key1243, 1), (key1247, -1)]

def row6297 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1116, 1), (key1125, 1), (key1130, -2), (key1152, -2), (key1159, 1), (key1174, 1), (key1233, -1), (key1236, 1), (key1243, 1), (key1247, -1)]

def row6298 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1116, 1), (key1125, 1), (key1130, -2), (key1152, -2), (key1159, 1), (key1174, 1), (key1233, -1), (key1236, 1), (key1243, 1), (key1247, -1)]

def row6299 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1116, 1), (key1125, 1), (key1130, -2), (key1152, -2), (key1159, 1), (key1174, 1), (key1233, -1), (key1236, 1), (key1243, 1), (key1247, -1)]

def row6300 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1116, -2), (key1125, 1), (key1130, 1), (key1152, 1), (key1159, 1), (key1174, -2), (key1233, 2), (key1236, -2), (key1243, -2), (key1247, 2)]

def row6301 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1116, -2), (key1125, 1), (key1130, 1), (key1152, 1), (key1159, 1), (key1174, -2), (key1233, 2), (key1236, -2), (key1243, -2), (key1247, 2)]

def row6302 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1116, 1), (key1125, 1), (key1130, -2), (key1152, -2), (key1159, 1), (key1174, 1), (key1233, -1), (key1236, 1), (key1243, 1), (key1247, -1)]

def row6303 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1116, 1), (key1125, 1), (key1130, -2), (key1152, -2), (key1159, 1), (key1174, 1), (key1233, -1), (key1236, 1), (key1243, 1), (key1247, -1)]

def row6304 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1116, -2), (key1125, 1), (key1130, 1), (key1152, 1), (key1159, 1), (key1174, -2), (key1233, 2), (key1236, -2), (key1243, -2), (key1247, 2)]

def row6305 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1116, -2), (key1125, 1), (key1130, 1), (key1152, 1), (key1159, 1), (key1174, -2), (key1233, 2), (key1236, -2), (key1243, -2), (key1247, 2)]

def row6306 : Integer.Sparse Key := [(key1003, -2), (key1009, 2), (key1017, 2), (key1022, -2), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1116, 4), (key1125, -2), (key1130, -2), (key1152, -2), (key1159, -2), (key1174, 4), (key1233, -4), (key1236, 4), (key1243, 4), (key1247, -4)]

def row6307 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1116, -2), (key1125, 1), (key1130, 1), (key1152, 1), (key1159, 1), (key1174, -2), (key1233, 2), (key1236, -2), (key1243, -2), (key1247, 2)]

def row6308 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1116, -2), (key1125, 1), (key1130, 1), (key1152, 1), (key1159, 1), (key1174, -2), (key1233, 2), (key1236, -2), (key1243, -2), (key1247, 2)]

def row6309 : Integer.Sparse Key := [(key1003, -2), (key1009, 2), (key1017, 2), (key1022, -2), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1116, 4), (key1125, -2), (key1130, -2), (key1152, -2), (key1159, -2), (key1174, 4), (key1233, -4), (key1236, 4), (key1243, 4), (key1247, -4)]

def row6310 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1116, -2), (key1125, 1), (key1130, 1), (key1152, 1), (key1159, 1), (key1174, -2), (key1233, 2), (key1236, -2), (key1243, -2), (key1247, 2)]

def row6311 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1116, -2), (key1125, 1), (key1130, 1), (key1152, 1), (key1159, 1), (key1174, -2), (key1233, 2), (key1236, -2), (key1243, -2), (key1247, 2)]

def row6312 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1116, -2), (key1125, 1), (key1130, 1), (key1152, 1), (key1159, 1), (key1174, -2), (key1233, 2), (key1236, -2), (key1243, -2), (key1247, 2)]

def row6313 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1116, -2), (key1125, 1), (key1130, 1), (key1152, 1), (key1159, 1), (key1174, -2), (key1233, 2), (key1236, -2), (key1243, -2), (key1247, 2)]

def row6314 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1116, -2), (key1125, 1), (key1130, 1), (key1152, 1), (key1159, 1), (key1174, -2), (key1233, 2), (key1236, -2), (key1243, -2), (key1247, 2)]

def row6315 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1116, -2), (key1125, 1), (key1130, 1), (key1152, 1), (key1159, 1), (key1174, -2), (key1233, 2), (key1236, -2), (key1243, -2), (key1247, 2)]

def row6316 : Integer.Sparse Key := [(key1003, -2), (key1009, 2), (key1017, 2), (key1022, -2), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1116, 4), (key1125, -2), (key1130, -2), (key1152, -2), (key1159, -2), (key1174, 4), (key1233, -4), (key1236, 4), (key1243, 4), (key1247, -4)]

def row6317 : Integer.Sparse Key := [(key1003, -2), (key1009, 2), (key1017, 2), (key1022, -2), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1116, 4), (key1125, -2), (key1130, -2), (key1152, -2), (key1159, -2), (key1174, 4), (key1233, -4), (key1236, 4), (key1243, 4), (key1247, -4)]

def row6318 : Integer.Sparse Key := [(key2406, -2), (key2411, 2), (key2437, 2), (key2443, -2), (key2587, 1), (key2593, -1), (key2598, -1), (key2600, 1), (key2843, 1), (key2880, -1), (key2887, 1), (key2889, -2), (key2910, 1), (key2966, -2), (key2968, 1), (key2989, 1), (key2995, 1), (key3002, -1)]

def row6319 : Integer.Sparse Key := [(key2406, -2), (key2411, 2), (key2437, 2), (key2443, -2), (key2587, 1), (key2593, -1), (key2598, -1), (key2600, 1), (key2843, 1), (key2880, -1), (key2887, 1), (key2889, -2), (key2910, 1), (key2966, -2), (key2968, 1), (key2989, 1), (key2995, 1), (key3002, -1)]

def row6320 : Integer.Sparse Key := [(key2406, 4), (key2411, -4), (key2437, -4), (key2443, 4), (key2587, -2), (key2593, 2), (key2598, 2), (key2600, -2), (key2843, -2), (key2880, 2), (key2887, -2), (key2889, 4), (key2910, -2), (key2966, 4), (key2968, -2), (key2989, -2), (key2995, -2), (key3002, 2)]

def row6321 : Integer.Sparse Key := [(key2406, -2), (key2411, 2), (key2437, 2), (key2443, -2), (key2587, 1), (key2593, -1), (key2598, -1), (key2600, 1), (key2843, 1), (key2880, -1), (key2887, 1), (key2889, -2), (key2910, 1), (key2966, -2), (key2968, 1), (key2989, 1), (key2995, 1), (key3002, -1)]

def row6322 : Integer.Sparse Key := [(key2406, -2), (key2411, 2), (key2437, 2), (key2443, -2), (key2587, 1), (key2593, -1), (key2598, -1), (key2600, 1), (key2843, 1), (key2880, -1), (key2887, 1), (key2889, -2), (key2910, 1), (key2966, -2), (key2968, 1), (key2989, 1), (key2995, 1), (key3002, -1)]

def row6323 : Integer.Sparse Key := [(key2406, 4), (key2411, -4), (key2437, -4), (key2443, 4), (key2587, -2), (key2593, 2), (key2598, 2), (key2600, -2), (key2843, -2), (key2880, 2), (key2887, -2), (key2889, 4), (key2910, -2), (key2966, 4), (key2968, -2), (key2989, -2), (key2995, -2), (key3002, 2)]

def row6324 : Integer.Sparse Key := [(key2406, 4), (key2411, -4), (key2437, -4), (key2443, 4), (key2587, -2), (key2593, 2), (key2598, 2), (key2600, -2), (key2843, -2), (key2880, 2), (key2887, -2), (key2889, 4), (key2910, -2), (key2966, 4), (key2968, -2), (key2989, -2), (key2995, -2), (key3002, 2)]

def row6325 : Integer.Sparse Key := [(key2406, -2), (key2411, 2), (key2437, 2), (key2443, -2), (key2587, 1), (key2593, -1), (key2598, -1), (key2600, 1), (key2843, 1), (key2880, -1), (key2887, 1), (key2889, -2), (key2910, 1), (key2966, -2), (key2968, 1), (key2989, 1), (key2995, 1), (key3002, -1)]

def row6326 : Integer.Sparse Key := [(key2406, -2), (key2411, 2), (key2437, 2), (key2443, -2), (key2587, 1), (key2593, -1), (key2598, -1), (key2600, 1), (key2843, 1), (key2880, -1), (key2887, 1), (key2889, -2), (key2910, 1), (key2966, -2), (key2968, 1), (key2989, 1), (key2995, 1), (key3002, -1)]

def row6327 : Integer.Sparse Key := [(key2406, 4), (key2411, -4), (key2437, -4), (key2443, 4), (key2587, -2), (key2593, 2), (key2598, 2), (key2600, -2), (key2843, -2), (key2880, 2), (key2887, -2), (key2889, 4), (key2910, -2), (key2966, 4), (key2968, -2), (key2989, -2), (key2995, -2), (key3002, 2)]

def row6328 : Integer.Sparse Key := [(key2406, -2), (key2411, 2), (key2437, 2), (key2443, -2), (key2587, 1), (key2593, -1), (key2598, -1), (key2600, 1), (key2843, 1), (key2880, -1), (key2887, 1), (key2889, -2), (key2910, 1), (key2966, -2), (key2968, 1), (key2989, 1), (key2995, 1), (key3002, -1)]

def row6329 : Integer.Sparse Key := [(key2406, -2), (key2411, 2), (key2437, 2), (key2443, -2), (key2587, 1), (key2593, -1), (key2598, -1), (key2600, 1), (key2843, 1), (key2880, -1), (key2887, 1), (key2889, -2), (key2910, 1), (key2966, -2), (key2968, 1), (key2989, 1), (key2995, 1), (key3002, -1)]

def row6330 : Integer.Sparse Key := [(key2378, 2), (key2390, -1), (key2394, -1), (key2472, -4), (key2480, 2), (key2484, 2), (key2503, 2), (key2509, 2), (key2524, -4), (key2587, -1), (key2593, -1), (key2600, 2), (key2766, 1), (key2772, -1), (key2843, 2), (key2880, 2), (key2887, -1), (key2889, -1), (key2910, -2), (key2929, -1), (key2931, 1), (key2966, -1), (key2968, -1), (key2989, -2), (key2995, 2), (key3002, 2)]

def row6331 : Integer.Sparse Key := [(key2378, 2), (key2390, -1), (key2394, -1), (key2472, -4), (key2480, 2), (key2484, 2), (key2503, 2), (key2509, 2), (key2524, -4), (key2587, -1), (key2593, -1), (key2600, 2), (key2766, 1), (key2772, -1), (key2843, 2), (key2880, 2), (key2887, -1), (key2889, -1), (key2910, -2), (key2929, -1), (key2931, 1), (key2966, -1), (key2968, -1), (key2989, -2), (key2995, 2), (key3002, 2)]

def row6332 : Integer.Sparse Key := [(key2378, -1), (key2390, -1), (key2394, 2), (key2472, 2), (key2480, 2), (key2484, -4), (key2503, -4), (key2509, 2), (key2524, 2), (key2587, 2), (key2593, -1), (key2600, -1), (key2766, -2), (key2772, 2), (key2843, -1), (key2880, -1), (key2887, -1), (key2889, 2), (key2910, 1), (key2929, 2), (key2931, -2), (key2966, 2), (key2968, -1), (key2989, 1), (key2995, -1), (key3002, -1)]

def row6333 : Integer.Sparse Key := [(key2378, -1), (key2390, -1), (key2394, 2), (key2472, 2), (key2480, 2), (key2484, -4), (key2503, -4), (key2509, 2), (key2524, 2), (key2587, 2), (key2593, -1), (key2600, -1), (key2766, -2), (key2772, 2), (key2843, -1), (key2880, -1), (key2887, -1), (key2889, 2), (key2910, 1), (key2929, 2), (key2931, -2), (key2966, 2), (key2968, -1), (key2989, 1), (key2995, -1), (key3002, -1)]

def row6334 : Integer.Sparse Key := [(key2406, 2), (key2437, -1), (key2443, -1), (key2472, -4), (key2480, 2), (key2484, 2), (key2503, 2), (key2509, 2), (key2524, -4), (key2587, 1), (key2593, -1), (key2598, -1), (key2600, 1), (key2766, -1), (key2772, -1), (key2843, 2), (key2880, 2), (key2887, -1), (key2889, -1), (key2910, -2), (key2931, 2), (key2966, -1), (key2968, -1), (key2989, -2), (key2995, 2), (key3002, 2)]

def row6335 : Integer.Sparse Key := [(key2406, 2), (key2437, -1), (key2443, -1), (key2472, -4), (key2480, 2), (key2484, 2), (key2503, 2), (key2509, 2), (key2524, -4), (key2587, 1), (key2593, -1), (key2598, -1), (key2600, 1), (key2766, -1), (key2772, -1), (key2843, 2), (key2880, 2), (key2887, -1), (key2889, -1), (key2910, -2), (key2931, 2), (key2966, -1), (key2968, -1), (key2989, -2), (key2995, 2), (key3002, 2)]

def row6336 : Integer.Sparse Key := [(key2406, -1), (key2437, 2), (key2443, -1), (key2472, 2), (key2480, 2), (key2484, -4), (key2503, -4), (key2509, 2), (key2524, 2), (key2587, 1), (key2593, -1), (key2598, -1), (key2600, 1), (key2766, -1), (key2772, 2), (key2843, -1), (key2880, -1), (key2887, -1), (key2889, 2), (key2910, 1), (key2931, -1), (key2966, 2), (key2968, -1), (key2989, 1), (key2995, -1), (key3002, -1)]

def row6337 : Integer.Sparse Key := [(key2406, -1), (key2437, 2), (key2443, -1), (key2472, 2), (key2480, 2), (key2484, -4), (key2503, -4), (key2509, 2), (key2524, 2), (key2587, 1), (key2593, -1), (key2598, -1), (key2600, 1), (key2766, -1), (key2772, 2), (key2843, -1), (key2880, -1), (key2887, -1), (key2889, 2), (key2910, 1), (key2931, -1), (key2966, 2), (key2968, -1), (key2989, 1), (key2995, -1), (key3002, -1)]

def row6338 : Integer.Sparse Key := [(key2437, 2), (key2472, 2), (key2480, 1), (key2484, -4), (key2503, -2), (key2509, 2), (key2524, 1), (key2587, 1), (key2593, -1), (key2598, -1), (key2600, 1), (key2766, -2), (key2772, 2), (key2843, -1), (key2880, -1), (key2889, 2), (key2910, 1), (key2931, -2), (key2968, -1), (key2989, 1), (key3002, -1)]

def row6339 : Integer.Sparse Key := [(key2437, 2), (key2472, 2), (key2480, 1), (key2484, -4), (key2503, -2), (key2509, 2), (key2524, 1), (key2587, 1), (key2593, -1), (key2598, -1), (key2600, 1), (key2766, -2), (key2772, 2), (key2843, -1), (key2880, -1), (key2889, 2), (key2910, 1), (key2931, -2), (key2968, -1), (key2989, 1), (key3002, -1)]

def row6340 : Integer.Sparse Key := [(key2390, -1), (key2437, -1), (key2472, -4), (key2480, 1), (key2484, 2), (key2503, 1), (key2509, 2), (key2524, -2), (key2580, 2), (key2587, 1), (key2593, -1), (key2600, 1), (key2766, 1), (key2772, -1), (key2843, 2), (key2880, 2), (key2889, -1), (key2910, -2), (key2931, 1), (key2968, -1), (key2989, -2)]

def row6341 : Integer.Sparse Key := [(key2390, -1), (key2437, -1), (key2472, -4), (key2480, 1), (key2484, 2), (key2503, 1), (key2509, 2), (key2524, -2), (key2580, 2), (key2587, 1), (key2593, -1), (key2600, 1), (key2766, 1), (key2772, -1), (key2843, 2), (key2880, 2), (key2889, -1), (key2910, -2), (key2931, 1), (key2968, -1), (key2989, -2)]

def row6342 : Integer.Sparse Key := [(key2378, -1), (key2390, -1), (key2394, 2), (key2406, -1), (key2437, 2), (key2443, -1), (key2472, 2), (key2480, 1), (key2484, -4), (key2503, -2), (key2509, 2), (key2524, 1), (key2571, 2), (key2576, -1), (key2580, -1), (key2587, 2), (key2593, -1), (key2600, -1), (key2766, -1), (key2772, 2), (key2843, -1), (key2880, -1), (key2889, 2), (key2910, -1), (key2931, -1), (key2968, -1), (key2989, 2)]

def row6343 : Integer.Sparse Key := [(key2378, -1), (key2390, -1), (key2394, 2), (key2406, -1), (key2437, 2), (key2443, -1), (key2472, 2), (key2480, 1), (key2484, -4), (key2503, -2), (key2509, 2), (key2524, 1), (key2571, 2), (key2576, -1), (key2580, -1), (key2587, 2), (key2593, -1), (key2600, -1), (key2766, -1), (key2772, 2), (key2843, -1), (key2880, -1), (key2889, 2), (key2910, -1), (key2931, -1), (key2968, -1), (key2989, 2)]

def row6344 : Integer.Sparse Key := [(key2378, 2), (key2390, -1), (key2394, -1), (key2406, 2), (key2437, -1), (key2443, -1), (key2472, -4), (key2480, 1), (key2484, 2), (key2503, 1), (key2509, 2), (key2524, -2), (key2571, -1), (key2576, -1), (key2580, 2), (key2587, -1), (key2593, -1), (key2600, 2), (key2766, -1), (key2772, -1), (key2843, 2), (key2880, 2), (key2889, -1), (key2910, -1), (key2931, 2), (key2968, -1), (key2989, -1)]

def row6345 : Integer.Sparse Key := [(key2378, 2), (key2390, -1), (key2394, -1), (key2406, 2), (key2437, -1), (key2443, -1), (key2472, -4), (key2480, 1), (key2484, 2), (key2503, 1), (key2509, 2), (key2524, -2), (key2571, -1), (key2576, -1), (key2580, 2), (key2587, -1), (key2593, -1), (key2600, 2), (key2766, -1), (key2772, -1), (key2843, 2), (key2880, 2), (key2889, -1), (key2910, -1), (key2931, 2), (key2968, -1), (key2989, -1)]

def row6346 : Integer.Sparse Key := [(key2378, -2), (key2383, 2), (key2390, 2), (key2394, -2), (key2406, -2), (key2411, 2), (key2437, 2), (key2443, -2), (key2472, 4), (key2480, -2), (key2484, -2), (key2503, -2), (key2509, -2), (key2524, 4), (key2569, -4), (key2571, 4), (key2576, 4), (key2580, -4)]

def row6347 : Integer.Sparse Key := [(key2378, 1), (key2383, -1), (key2390, -1), (key2394, 1), (key2406, 1), (key2411, -1), (key2437, -1), (key2443, 1), (key2472, -2), (key2480, 1), (key2484, 1), (key2503, 1), (key2509, 1), (key2524, -2), (key2569, 2), (key2571, -2), (key2576, -2), (key2580, 2)]

def row6348 : Integer.Sparse Key := [(key2378, 1), (key2383, -1), (key2390, -1), (key2394, 1), (key2406, 1), (key2411, -1), (key2437, -1), (key2443, 1), (key2472, -2), (key2480, 1), (key2484, 1), (key2503, 1), (key2509, 1), (key2524, -2), (key2569, 2), (key2571, -2), (key2576, -2), (key2580, 2)]

def row6349 : Integer.Sparse Key := [(key2378, -2), (key2383, 2), (key2390, 2), (key2394, -2), (key2406, -2), (key2411, 2), (key2437, 2), (key2443, -2), (key2472, 4), (key2480, -2), (key2484, -2), (key2503, -2), (key2509, -2), (key2524, 4), (key2569, -4), (key2571, 4), (key2576, 4), (key2580, -4)]

def row6350 : Integer.Sparse Key := [(key2378, 1), (key2383, -1), (key2390, -1), (key2394, 1), (key2406, 1), (key2411, -1), (key2437, -1), (key2443, 1), (key2472, -2), (key2480, 1), (key2484, 1), (key2503, 1), (key2509, 1), (key2524, -2), (key2569, 2), (key2571, -2), (key2576, -2), (key2580, 2)]

def row6351 : Integer.Sparse Key := [(key2378, 1), (key2383, -1), (key2390, -1), (key2394, 1), (key2406, 1), (key2411, -1), (key2437, -1), (key2443, 1), (key2472, -2), (key2480, 1), (key2484, 1), (key2503, 1), (key2509, 1), (key2524, -2), (key2569, 2), (key2571, -2), (key2576, -2), (key2580, 2)]

def row6352 : Integer.Sparse Key := [(key2378, 1), (key2383, -1), (key2390, -1), (key2394, 1), (key2406, 1), (key2411, -1), (key2437, -1), (key2443, 1), (key2472, -2), (key2480, 1), (key2484, 1), (key2503, 1), (key2509, 1), (key2524, -2), (key2569, 2), (key2571, -2), (key2576, -2), (key2580, 2)]

def row6353 : Integer.Sparse Key := [(key2378, 1), (key2383, -1), (key2390, -1), (key2394, 1), (key2406, 1), (key2411, -1), (key2437, -1), (key2443, 1), (key2472, -2), (key2480, 1), (key2484, 1), (key2503, 1), (key2509, 1), (key2524, -2), (key2569, 2), (key2571, -2), (key2576, -2), (key2580, 2)]

def row6354 : Integer.Sparse Key := [(key2378, 1), (key2383, -1), (key2390, -1), (key2394, 1), (key2406, 1), (key2411, -1), (key2437, -1), (key2443, 1), (key2472, -2), (key2480, 1), (key2484, 1), (key2503, 1), (key2509, 1), (key2524, -2), (key2569, 2), (key2571, -2), (key2576, -2), (key2580, 2)]

def row6355 : Integer.Sparse Key := [(key2378, 1), (key2383, -1), (key2390, -1), (key2394, 1), (key2406, 1), (key2411, -1), (key2437, -1), (key2443, 1), (key2472, -2), (key2480, 1), (key2484, 1), (key2503, 1), (key2509, 1), (key2524, -2), (key2569, 2), (key2571, -2), (key2576, -2), (key2580, 2)]

def row6356 : Integer.Sparse Key := [(key2378, -2), (key2383, 2), (key2390, 2), (key2394, -2), (key2406, -2), (key2411, 2), (key2437, 2), (key2443, -2), (key2472, 4), (key2480, -2), (key2484, -2), (key2503, -2), (key2509, -2), (key2524, 4), (key2569, -4), (key2571, 4), (key2576, 4), (key2580, -4)]

def row6357 : Integer.Sparse Key := [(key2378, -2), (key2383, 2), (key2390, 2), (key2394, -2), (key2406, -2), (key2411, 2), (key2437, 2), (key2443, -2), (key2472, 4), (key2480, -2), (key2484, -2), (key2503, -2), (key2509, -2), (key2524, 4), (key2569, -4), (key2571, 4), (key2576, 4), (key2580, -4)]

def row6358 : Integer.Sparse Key := [(key2612, -1), (key2618, 1), (key2628, 1), (key2641, -1), (key2648, -1), (key2653, 1), (key2702, 1), (key2728, -1), (key2735, -1), (key2747, 1), (key2805, -1), (key2831, 1), (key2893, 1), (key2904, -1), (key2948, 2), (key2950, -1), (key2960, -1), (key2972, -2), (key2976, 1), (key2983, 1), (key2997, 1), (key2998, -1)]

def row6359 : Integer.Sparse Key := [(key2612, 1), (key2616, -2), (key2618, 1), (key2628, 1), (key2641, -1), (key2648, -1), (key2653, 1), (key2702, 1), (key2728, -1), (key2735, -1), (key2747, 1), (key2805, -1), (key2831, 1), (key2893, 1), (key2904, -1), (key2948, 2), (key2950, -1), (key2960, -1), (key2972, -2), (key2976, 1), (key2983, 1), (key2997, 1), (key2998, -1)]

def row6360 : Integer.Sparse Key := [(key2616, 2), (key2621, -2), (key2628, -2), (key2641, 2), (key2648, 2), (key2653, -2), (key2702, -2), (key2728, 2), (key2735, 2), (key2747, -2), (key2805, 2), (key2831, -2), (key2893, -2), (key2904, 2), (key2948, -4), (key2950, 2), (key2960, 2), (key2972, 4), (key2976, -2), (key2983, -2), (key2997, -2), (key2998, 2)]

def row6361 : Integer.Sparse Key := [(key2612, -1), (key2618, 1), (key2628, 1), (key2641, -1), (key2648, -1), (key2653, 1), (key2702, 1), (key2728, -1), (key2735, -1), (key2747, 1), (key2805, 1), (key2809, -2), (key2829, 1), (key2831, 1), (key2835, 1), (key2893, 1), (key2904, -1), (key2948, 1), (key2950, -2), (key2960, -1), (key2972, -2), (key2976, 1), (key2983, 1), (key2997, 1), (key2998, -1)]

def row6362 : Integer.Sparse Key := [(key2612, 1), (key2616, -2), (key2618, 1), (key2628, 1), (key2641, -1), (key2648, -1), (key2653, 1), (key2702, 1), (key2728, -1), (key2735, -1), (key2747, 1), (key2805, 1), (key2809, -2), (key2829, 1), (key2831, 1), (key2835, 1), (key2893, 1), (key2904, -1), (key2948, 1), (key2950, -2), (key2960, -1), (key2972, -2), (key2976, 1), (key2983, 1), (key2997, 1), (key2998, -1)]

def row6363 : Integer.Sparse Key := [(key2612, 2), (key2618, -2), (key2628, -2), (key2641, 2), (key2648, 2), (key2653, -2), (key2702, -2), (key2728, 2), (key2735, 2), (key2747, -2), (key2805, 1), (key2809, 1), (key2829, -4), (key2831, -2), (key2835, 1), (key2893, -2), (key2904, 2), (key2950, 1), (key2960, 2), (key2972, 4), (key2976, -2), (key2983, -2), (key2997, -2), (key2998, 2)]

def row6364 : Integer.Sparse Key := [(key2612, 2), (key2618, -2), (key2628, -2), (key2641, 2), (key2648, 2), (key2653, -2), (key2702, -2), (key2728, 2), (key2735, 2), (key2747, -2), (key2805, 1), (key2809, 1), (key2829, -4), (key2831, -2), (key2835, 1), (key2893, -2), (key2904, 2), (key2950, 1), (key2960, 2), (key2972, 4), (key2976, -2), (key2983, -2), (key2997, -2), (key2998, 2)]

def row6365 : Integer.Sparse Key := [(key2612, -2), (key2616, 1), (key2618, 1), (key2628, 1), (key2641, -1), (key2648, -1), (key2653, 1), (key2702, 1), (key2728, -1), (key2735, -1), (key2747, 1), (key2805, -2), (key2809, 1), (key2829, 2), (key2831, 1), (key2835, -2), (key2893, 1), (key2904, -1), (key2950, 1), (key2960, 1), (key2972, -2), (key2976, 1), (key2983, 1), (key2997, 1), (key2998, -1), (key3017, -2)]

def row6366 : Integer.Sparse Key := [(key2612, -2), (key2616, 1), (key2618, 1), (key2628, 1), (key2641, -1), (key2648, -1), (key2653, 1), (key2702, 1), (key2728, -1), (key2735, -1), (key2747, 1), (key2805, -2), (key2809, 1), (key2829, 2), (key2831, 1), (key2835, -2), (key2893, 1), (key2904, -1), (key2950, 1), (key2960, 1), (key2972, -2), (key2976, 1), (key2983, 1), (key2997, 1), (key2998, -1), (key3017, -2)]

def row6367 : Integer.Sparse Key := [(key2616, 2), (key2621, -2), (key2628, -2), (key2641, 2), (key2648, 2), (key2653, -2), (key2702, -2), (key2728, 2), (key2735, 2), (key2747, -2), (key2809, 2), (key2829, -4), (key2835, 2), (key2893, -2), (key2904, 2), (key2972, 4), (key2976, -2), (key2983, -2), (key2997, -2), (key2998, 2), (key3012, -2), (key3017, 2)]

def row6368 : Integer.Sparse Key := [(key2616, -1), (key2621, 1), (key2628, 1), (key2641, -1), (key2648, -1), (key2653, 1), (key2702, 1), (key2728, -1), (key2735, -1), (key2747, 1), (key2809, -1), (key2829, 2), (key2835, -1), (key2893, 1), (key2904, -1), (key2972, -2), (key2976, 1), (key2983, 1), (key2997, 1), (key2998, -1), (key3012, 1), (key3017, -1)]

def row6369 : Integer.Sparse Key := [(key2616, -1), (key2621, 1), (key2628, 1), (key2641, -1), (key2648, -1), (key2653, 1), (key2702, 1), (key2728, -1), (key2735, -1), (key2747, 1), (key2809, -1), (key2829, 2), (key2835, -1), (key2893, 1), (key2904, -1), (key2972, -2), (key2976, 1), (key2983, 1), (key2997, 1), (key2998, -1), (key3012, 1), (key3017, -1)]

def row6370 : Integer.Sparse Key := [(key2612, 1), (key2618, -1), (key2628, 1), (key2632, -2), (key2640, 1), (key2641, 1), (key2644, 1), (key2646, -1), (key2653, -1), (key2667, 1), (key2673, -1), (key2706, -2), (key2726, 1), (key2732, 1), (key2735, -1), (key2737, 1), (key2782, 1), (key2795, 1), (key2860, 1), (key2870, 1), (key2885, -2), (key2897, -1), (key2904, -1), (key2936, -1), (key2943, -1), (key2948, -1), (key2950, 1), (key2976, -1), (key2983, -1), (key2998, 2), (key3000, 2), (key3023, 1), (key3026, 1), (key3030, -2)]

def row6371 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2628, 1), (key2632, -2), (key2640, 1), (key2641, 1), (key2644, 1), (key2646, -1), (key2653, -1), (key2667, 1), (key2673, -1), (key2706, -2), (key2726, 1), (key2732, 1), (key2735, -1), (key2737, 1), (key2782, 1), (key2795, 1), (key2860, 1), (key2870, 1), (key2885, -2), (key2897, -1), (key2904, -1), (key2936, -1), (key2943, -1), (key2948, -1), (key2950, 1), (key2976, -1), (key2983, -1), (key2998, 2), (key3000, 2), (key3023, 1), (key3026, 1), (key3030, -2)]

def row6372 : Integer.Sparse Key := [(key2616, -1), (key2618, 1), (key2632, 1), (key2641, -1), (key2644, -2), (key2648, 1), (key2653, -1), (key2660, 2), (key2702, 1), (key2706, 1), (key2726, -2), (key2728, -1), (key2732, 1), (key2735, -1), (key2747, 1), (key2782, -1), (key2805, -1), (key2831, 1), (key2860, 1), (key2870, -2), (key2885, 1), (key2904, 1), (key2936, 2), (key2938, -1), (key2948, 2), (key2950, -1), (key2960, -1), (key2976, 1), (key2998, -1), (key3000, -1), (key3023, -2), (key3026, 1), (key3030, 1)]

def row6373 : Integer.Sparse Key := [(key2616, -1), (key2618, 1), (key2632, 1), (key2641, -1), (key2644, -2), (key2648, 1), (key2653, -1), (key2660, 2), (key2702, 1), (key2706, 1), (key2726, -2), (key2728, -1), (key2732, 1), (key2735, -1), (key2747, 1), (key2782, -1), (key2805, -1), (key2831, 1), (key2860, 1), (key2870, -2), (key2885, 1), (key2904, 1), (key2936, 2), (key2938, -1), (key2948, 2), (key2950, -1), (key2960, -1), (key2976, 1), (key2998, -1), (key3000, -1), (key3023, -2), (key3026, 1), (key3030, 1)]

def row6374 : Integer.Sparse Key := [(key2612, 1), (key2618, -1), (key2628, 1), (key2632, -2), (key2640, 1), (key2641, 1), (key2644, 1), (key2646, -1), (key2653, -1), (key2667, -1), (key2671, 2), (key2673, -1), (key2706, -2), (key2732, 1), (key2735, -1), (key2737, 1), (key2758, -1), (key2782, 1), (key2795, 1), (key2860, 1), (key2870, 1), (key2885, -2), (key2897, -1), (key2904, -1), (key2948, -1), (key2950, 1), (key2976, -1), (key2983, -1), (key2998, 2), (key3000, 2), (key3023, 1), (key3026, 1), (key3030, -2)]

def row6375 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2628, 1), (key2632, -2), (key2640, 1), (key2641, 1), (key2644, 1), (key2646, -1), (key2653, -1), (key2667, -1), (key2671, 2), (key2673, -1), (key2706, -2), (key2732, 1), (key2735, -1), (key2737, 1), (key2758, -1), (key2782, 1), (key2795, 1), (key2860, 1), (key2870, 1), (key2885, -2), (key2897, -1), (key2904, -1), (key2948, -1), (key2950, 1), (key2976, -1), (key2983, -1), (key2998, 2), (key3000, 2), (key3023, 1), (key3026, 1), (key3030, -2)]

def row6376 : Integer.Sparse Key := [(key2612, -1), (key2618, 1), (key2632, 1), (key2640, 1), (key2641, -1), (key2644, -2), (key2646, -1), (key2648, 1), (key2653, 1), (key2667, 1), (key2671, -1), (key2702, 1), (key2706, 1), (key2728, -1), (key2732, 1), (key2735, -1), (key2747, 1), (key2758, -1), (key2782, -1), (key2805, -1), (key2829, 2), (key2831, 1), (key2860, 1), (key2870, -2), (key2885, 1), (key2904, 1), (key2938, -1), (key2943, 1), (key2950, -1), (key2960, -1), (key2976, 1), (key2998, -1), (key3000, -1), (key3023, -2), (key3026, 1), (key3030, 1)]

def row6377 : Integer.Sparse Key := [(key2612, -1), (key2618, 1), (key2632, 1), (key2640, 1), (key2641, -1), (key2644, -2), (key2646, -1), (key2648, 1), (key2653, 1), (key2667, 1), (key2671, -1), (key2702, 1), (key2706, 1), (key2728, -1), (key2732, 1), (key2735, -1), (key2747, 1), (key2758, -1), (key2782, -1), (key2805, -1), (key2829, 2), (key2831, 1), (key2860, 1), (key2870, -2), (key2885, 1), (key2904, 1), (key2938, -1), (key2943, 1), (key2950, -1), (key2960, -1), (key2976, 1), (key2998, -1), (key3000, -1), (key3023, -2), (key3026, 1), (key3030, 1)]

def row6378 : Integer.Sparse Key := [(key2612, -1), (key2618, 1), (key2632, 1), (key2641, -1), (key2644, -2), (key2648, 1), (key2653, 1), (key2702, 1), (key2706, 1), (key2728, -1), (key2732, 1), (key2747, 1), (key2782, -1), (key2794, -1), (key2805, -1), (key2829, 2), (key2831, 1), (key2860, 1), (key2870, -2), (key2885, 1), (key2904, 1), (key2927, -1), (key2938, -1), (key2950, -1), (key2960, -1), (key2976, 1), (key3023, -2), (key3026, 1)]

def row6379 : Integer.Sparse Key := [(key2612, -1), (key2618, 1), (key2632, 1), (key2641, -1), (key2644, -2), (key2648, 1), (key2653, 1), (key2702, 1), (key2706, 1), (key2728, -1), (key2732, 1), (key2747, 1), (key2782, -1), (key2794, -1), (key2805, -1), (key2829, 2), (key2831, 1), (key2860, 1), (key2870, -2), (key2885, 1), (key2904, 1), (key2927, -1), (key2938, -1), (key2950, -1), (key2960, -1), (key2976, 1), (key3023, -2), (key3026, 1)]

def row6380 : Integer.Sparse Key := [(key2612, 1), (key2618, -1), (key2628, 1), (key2632, -2), (key2641, 1), (key2644, 1), (key2653, -1), (key2667, 1), (key2673, -1), (key2706, -2), (key2732, 1), (key2737, 1), (key2782, 1), (key2794, -1), (key2795, 1), (key2829, -1), (key2860, 1), (key2870, 1), (key2885, -2), (key2897, -1), (key2904, -1), (key2927, 2), (key2943, -1), (key2950, 1), (key2976, -1), (key2983, -1), (key3023, 1), (key3026, 1)]

def row6381 : Integer.Sparse Key := [(key2612, 1), (key2618, -1), (key2628, 1), (key2632, -2), (key2641, 1), (key2644, 1), (key2653, -1), (key2667, 1), (key2673, -1), (key2706, -2), (key2732, 1), (key2737, 1), (key2782, 1), (key2794, -1), (key2795, 1), (key2829, -1), (key2860, 1), (key2870, 1), (key2885, -2), (key2897, -1), (key2904, -1), (key2927, 2), (key2943, -1), (key2950, 1), (key2976, -1), (key2983, -1), (key3023, 1), (key3026, 1)]

def row6382 : Integer.Sparse Key := [(key2616, -1), (key2618, 1), (key2632, 1), (key2641, -1), (key2644, -2), (key2648, 1), (key2653, -1), (key2660, 2), (key2667, 1), (key2671, -1), (key2702, 1), (key2706, 1), (key2728, -1), (key2732, 1), (key2747, -1), (key2758, -1), (key2782, -1), (key2794, -1), (key2805, -1), (key2829, 2), (key2831, 1), (key2860, 1), (key2870, -2), (key2885, 1), (key2904, 1), (key2927, -1), (key2938, -1), (key2943, 1), (key2950, -1), (key2976, 1), (key3010, 2), (key3017, -1), (key3023, -2), (key3026, 1)]

def row6383 : Integer.Sparse Key := [(key2616, -1), (key2618, 1), (key2632, 1), (key2641, -1), (key2644, -2), (key2648, 1), (key2653, -1), (key2660, 2), (key2667, 1), (key2671, -1), (key2702, 1), (key2706, 1), (key2728, -1), (key2732, 1), (key2747, -1), (key2758, -1), (key2782, -1), (key2794, -1), (key2805, -1), (key2829, 2), (key2831, 1), (key2860, 1), (key2870, -2), (key2885, 1), (key2904, 1), (key2927, -1), (key2938, -1), (key2943, 1), (key2950, -1), (key2976, 1), (key3010, 2), (key3017, -1), (key3023, -2), (key3026, 1)]

def row6384 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2628, 1), (key2632, -2), (key2641, 1), (key2644, 1), (key2660, -1), (key2667, -1), (key2671, 2), (key2673, -1), (key2706, -2), (key2732, 1), (key2737, 1), (key2747, 1), (key2758, -1), (key2782, 1), (key2794, -1), (key2795, 1), (key2829, -1), (key2860, 1), (key2870, 1), (key2885, -2), (key2897, -1), (key2904, -1), (key2927, 2), (key2950, 1), (key2960, 1), (key2976, -1), (key2983, -1), (key3010, -1), (key3017, -1), (key3023, 1), (key3026, 1)]

def row6385 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2628, 1), (key2632, -2), (key2641, 1), (key2644, 1), (key2660, -1), (key2667, -1), (key2671, 2), (key2673, -1), (key2706, -2), (key2732, 1), (key2737, 1), (key2747, 1), (key2758, -1), (key2782, 1), (key2794, -1), (key2795, 1), (key2829, -1), (key2860, 1), (key2870, 1), (key2885, -2), (key2897, -1), (key2904, -1), (key2927, 2), (key2950, 1), (key2960, 1), (key2976, -1), (key2983, -1), (key3010, -1), (key3017, -1), (key3023, 1), (key3026, 1)]

def row6386 : Integer.Sparse Key := [(key2616, -2), (key2621, 2), (key2632, 2), (key2644, -2), (key2658, -2), (key2660, 2), (key2671, -2), (key2676, 2), (key2706, 2), (key2732, -2), (key2753, -2), (key2758, 2), (key2794, 2), (key2798, -2), (key2829, 2), (key2835, -2), (key2860, -2), (key2870, -2), (key2885, 4), (key2920, 2), (key2923, 2), (key2927, -4)]

def row6387 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2632, -1), (key2644, 1), (key2658, 1), (key2660, -1), (key2671, 1), (key2676, -1), (key2706, -1), (key2732, 1), (key2753, 1), (key2758, -1), (key2794, -1), (key2798, 1), (key2829, -1), (key2835, 1), (key2860, 1), (key2870, 1), (key2885, -2), (key2920, -1), (key2923, -1), (key2927, 2)]

def row6388 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2632, -1), (key2644, 1), (key2658, 1), (key2660, -1), (key2671, 1), (key2676, -1), (key2706, -1), (key2732, 1), (key2753, 1), (key2758, -1), (key2794, -1), (key2798, 1), (key2829, -1), (key2835, 1), (key2860, 1), (key2870, 1), (key2885, -2), (key2920, -1), (key2923, -1), (key2927, 2)]

def row6389 : Integer.Sparse Key := [(key2616, -2), (key2621, 2), (key2632, 2), (key2644, -2), (key2658, -2), (key2660, 2), (key2671, -2), (key2676, 2), (key2706, 2), (key2732, -2), (key2753, -2), (key2758, 2), (key2794, 2), (key2798, -2), (key2829, 2), (key2835, -2), (key2860, -2), (key2870, -2), (key2885, 4), (key2920, 2), (key2923, 2), (key2927, -4)]

def row6390 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2632, -1), (key2644, 1), (key2658, 1), (key2660, -1), (key2671, 1), (key2676, -1), (key2706, -1), (key2732, 1), (key2753, 1), (key2758, -1), (key2794, -1), (key2798, 1), (key2829, -1), (key2835, 1), (key2860, 1), (key2870, 1), (key2885, -2), (key2920, -1), (key2923, -1), (key2927, 2)]

def row6391 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2632, -1), (key2644, 1), (key2658, 1), (key2660, -1), (key2671, 1), (key2676, -1), (key2706, -1), (key2732, 1), (key2753, 1), (key2758, -1), (key2794, -1), (key2798, 1), (key2829, -1), (key2835, 1), (key2860, 1), (key2870, 1), (key2885, -2), (key2920, -1), (key2923, -1), (key2927, 2)]

def row6392 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2632, -1), (key2644, 1), (key2658, 1), (key2660, -1), (key2671, 1), (key2676, -1), (key2706, -1), (key2732, 1), (key2753, 1), (key2758, -1), (key2794, -1), (key2798, 1), (key2829, -1), (key2835, 1), (key2860, 1), (key2870, 1), (key2885, -2), (key2920, -1), (key2923, -1), (key2927, 2)]

def row6393 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2632, -1), (key2644, 1), (key2658, 1), (key2660, -1), (key2671, 1), (key2676, -1), (key2706, -1), (key2732, 1), (key2753, 1), (key2758, -1), (key2794, -1), (key2798, 1), (key2829, -1), (key2835, 1), (key2860, 1), (key2870, 1), (key2885, -2), (key2920, -1), (key2923, -1), (key2927, 2)]

def row6394 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2632, -1), (key2644, 1), (key2658, 1), (key2660, -1), (key2671, 1), (key2676, -1), (key2706, -1), (key2732, 1), (key2753, 1), (key2758, -1), (key2794, -1), (key2798, 1), (key2829, -1), (key2835, 1), (key2860, 1), (key2870, 1), (key2885, -2), (key2920, -1), (key2923, -1), (key2927, 2)]

def row6395 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2632, -1), (key2644, 1), (key2658, 1), (key2660, -1), (key2671, 1), (key2676, -1), (key2706, -1), (key2732, 1), (key2753, 1), (key2758, -1), (key2794, -1), (key2798, 1), (key2829, -1), (key2835, 1), (key2860, 1), (key2870, 1), (key2885, -2), (key2920, -1), (key2923, -1), (key2927, 2)]

def row6396 : Integer.Sparse Key := [(key2616, -2), (key2621, 2), (key2632, 2), (key2644, -2), (key2658, -2), (key2660, 2), (key2671, -2), (key2676, 2), (key2706, 2), (key2732, -2), (key2753, -2), (key2758, 2), (key2794, 2), (key2798, -2), (key2829, 2), (key2835, -2), (key2860, -2), (key2870, -2), (key2885, 4), (key2920, 2), (key2923, 2), (key2927, -4)]

def row6397 : Integer.Sparse Key := [(key2616, -2), (key2621, 2), (key2632, 2), (key2644, -2), (key2658, -2), (key2660, 2), (key2671, -2), (key2676, 2), (key2706, 2), (key2732, -2), (key2753, -2), (key2758, 2), (key2794, 2), (key2798, -2), (key2829, 2), (key2835, -2), (key2860, -2), (key2870, -2), (key2885, 4), (key2920, 2), (key2923, 2), (key2927, -4)]

def row6398 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -2), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, 1), (key1548, -1), (key1569, -1), (key1575, 2), (key1593, -1), (key1681, -1), (key1689, 1), (key1903, -1), (key1911, 1), (key1918, 1), (key1926, -1)]

def row6399 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -2), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, 1), (key1548, -1), (key1569, -1), (key1575, 2), (key1593, -1), (key1681, -1), (key1689, 1), (key1903, -1), (key1911, 1), (key1918, 1), (key1926, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block74
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row6400 : Integer.Sparse Key := [(key1292, -2), (key1298, 2), (key1312, 2), (key1318, -2), (key1387, 2), (key1393, -2), (key1420, -2), (key1426, 4), (key1444, -2), (key1472, -2), (key1480, 2), (key1542, -2), (key1548, 2), (key1569, 2), (key1575, -4), (key1593, 2), (key1681, 2), (key1689, -2), (key1903, 2), (key1911, -2), (key1918, -2), (key1926, 2)]

def row6401 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -2), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, 1), (key1548, -1), (key1569, -1), (key1575, 2), (key1593, -1), (key1681, -1), (key1689, 1), (key1903, -1), (key1911, 1), (key1918, 1), (key1926, -1)]

def row6402 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -2), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, 1), (key1548, -1), (key1569, -1), (key1575, 2), (key1593, -1), (key1681, -1), (key1689, 1), (key1903, -1), (key1911, 1), (key1918, 1), (key1926, -1)]

def row6403 : Integer.Sparse Key := [(key1292, -2), (key1298, 2), (key1312, 2), (key1318, -2), (key1387, 2), (key1393, -2), (key1420, -2), (key1426, 4), (key1444, -2), (key1472, -2), (key1480, 2), (key1542, -2), (key1548, 2), (key1569, 2), (key1575, -4), (key1593, 2), (key1681, 2), (key1689, -2), (key1903, 2), (key1911, -2), (key1918, -2), (key1926, 2)]

def row6404 : Integer.Sparse Key := [(key1292, -2), (key1298, 2), (key1312, 2), (key1318, -2), (key1387, 2), (key1393, -2), (key1420, -2), (key1426, 4), (key1444, -2), (key1472, -2), (key1480, 2), (key1542, -2), (key1548, 2), (key1569, 2), (key1575, -4), (key1593, 2), (key1681, 2), (key1689, -2), (key1903, 2), (key1911, -2), (key1918, -2), (key1926, 2)]

def row6405 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -2), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, 1), (key1548, -1), (key1569, -1), (key1575, 2), (key1593, -1), (key1681, -1), (key1689, 1), (key1903, -1), (key1911, 1), (key1918, 1), (key1926, -1)]

def row6406 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -2), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, 1), (key1548, -1), (key1569, -1), (key1575, 2), (key1593, -1), (key1681, -1), (key1689, 1), (key1903, -1), (key1911, 1), (key1918, 1), (key1926, -1)]

def row6407 : Integer.Sparse Key := [(key1292, -2), (key1298, 2), (key1312, 2), (key1318, -2), (key1387, 2), (key1393, -2), (key1420, -2), (key1426, 4), (key1444, -2), (key1472, -2), (key1480, 2), (key1542, -2), (key1548, 2), (key1569, 2), (key1575, -4), (key1593, 2), (key1681, 2), (key1689, -2), (key1903, 2), (key1911, -2), (key1918, -2), (key1926, 2)]

def row6408 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -2), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, 1), (key1548, -1), (key1569, -1), (key1575, 2), (key1593, -1), (key1681, -1), (key1689, 1), (key1903, -1), (key1911, 1), (key1918, 1), (key1926, -1)]

def row6409 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -2), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, 1), (key1548, -1), (key1569, -1), (key1575, 2), (key1593, -1), (key1681, -1), (key1689, 1), (key1903, -1), (key1911, 1), (key1918, 1), (key1926, -1)]

def row6410 : Integer.Sparse Key := [(key1318, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1426, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1548, -1), (key1556, 1), (key1575, -1), (key1593, 1), (key1681, 2), (key1683, -1), (key1689, -1), (key1896, 1), (key1899, -1), (key1903, 1), (key1911, -1), (key1918, -2), (key1920, 1), (key1926, 1)]

def row6411 : Integer.Sparse Key := [(key1318, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1426, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1548, -1), (key1556, 1), (key1575, -1), (key1593, 1), (key1681, 2), (key1683, -1), (key1689, -1), (key1896, 1), (key1899, -1), (key1903, 1), (key1911, -1), (key1918, -2), (key1920, 1), (key1926, 1)]

def row6412 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -2), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, 1), (key1548, -1), (key1569, -1), (key1575, 2), (key1593, -1), (key1681, -1), (key1689, 1), (key1903, -1), (key1911, 1), (key1918, 1), (key1926, -1)]

def row6413 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -2), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, 1), (key1548, -1), (key1569, -1), (key1575, 2), (key1593, -1), (key1681, -1), (key1689, 1), (key1903, -1), (key1911, 1), (key1918, 1), (key1926, -1)]

def row6414 : Integer.Sparse Key := [(key1318, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1426, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1548, -1), (key1556, 1), (key1575, -1), (key1593, 1), (key1681, 2), (key1683, -1), (key1689, -1), (key1896, 1), (key1899, -1), (key1903, 1), (key1911, -1), (key1918, -2), (key1920, 1), (key1926, 1)]

def row6415 : Integer.Sparse Key := [(key1318, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1426, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1548, -1), (key1556, 1), (key1575, -1), (key1593, 1), (key1681, 2), (key1683, -1), (key1689, -1), (key1896, 1), (key1899, -1), (key1903, 1), (key1911, -1), (key1918, -2), (key1920, 1), (key1926, 1)]

def row6416 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -2), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, 1), (key1548, -1), (key1569, -1), (key1575, 2), (key1593, -1), (key1681, -1), (key1689, 1), (key1903, -1), (key1911, 1), (key1918, 1), (key1926, -1)]

def row6417 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -2), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, 1), (key1548, -1), (key1569, -1), (key1575, 2), (key1593, -1), (key1681, -1), (key1689, 1), (key1903, -1), (key1911, 1), (key1918, 1), (key1926, -1)]

def row6418 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -2), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, 1), (key1548, -1), (key1569, -1), (key1575, 2), (key1593, -1), (key1681, -1), (key1689, 1), (key1903, -1), (key1911, 1), (key1918, 1), (key1926, -1)]

def row6419 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -2), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, 1), (key1548, -1), (key1569, -1), (key1575, 2), (key1593, -1), (key1681, -1), (key1689, 1), (key1903, -1), (key1911, 1), (key1918, 1), (key1926, -1)]

def row6420 : Integer.Sparse Key := [(key1318, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1426, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1548, -1), (key1556, 1), (key1575, -1), (key1593, 1), (key1681, 2), (key1683, -1), (key1689, -1), (key1896, 1), (key1899, -1), (key1903, 1), (key1911, -1), (key1918, -2), (key1920, 1), (key1926, 1)]

def row6421 : Integer.Sparse Key := [(key1318, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1426, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1548, -1), (key1556, 1), (key1575, -1), (key1593, 1), (key1681, 2), (key1683, -1), (key1689, -1), (key1896, 1), (key1899, -1), (key1903, 1), (key1911, -1), (key1918, -2), (key1920, 1), (key1926, 1)]

def row6422 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -2), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, 1), (key1548, -1), (key1569, -1), (key1575, 2), (key1593, -1), (key1681, -1), (key1689, 1), (key1903, -1), (key1911, 1), (key1918, 1), (key1926, -1)]

def row6423 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -2), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, 1), (key1548, -1), (key1569, -1), (key1575, 2), (key1593, -1), (key1681, -1), (key1689, 1), (key1903, -1), (key1911, 1), (key1918, 1), (key1926, -1)]

def row6424 : Integer.Sparse Key := [(key1318, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1426, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1548, -1), (key1556, 1), (key1575, -1), (key1593, 1), (key1681, 2), (key1683, -1), (key1689, -1), (key1896, 1), (key1899, -1), (key1903, 1), (key1911, -1), (key1918, -2), (key1920, 1), (key1926, 1)]

def row6425 : Integer.Sparse Key := [(key1318, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1426, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1548, -1), (key1556, 1), (key1575, -1), (key1593, 1), (key1681, 2), (key1683, -1), (key1689, -1), (key1896, 1), (key1899, -1), (key1903, 1), (key1911, -1), (key1918, -2), (key1920, 1), (key1926, 1)]

def row6426 : Integer.Sparse Key := [(key1318, -2), (key1326, 2), (key1351, 2), (key1354, -2), (key1426, -2), (key1444, 2), (key1472, 2), (key1480, -2), (key1548, 2), (key1556, -2), (key1575, 2), (key1593, -2), (key1681, -4), (key1683, 2), (key1689, 2), (key1896, -2), (key1899, 2), (key1903, -2), (key1911, 2), (key1918, 4), (key1920, -2), (key1926, -2)]

def row6427 : Integer.Sparse Key := [(key1318, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1426, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1548, -1), (key1556, 1), (key1575, -1), (key1593, 1), (key1681, 2), (key1683, -1), (key1689, -1), (key1896, 1), (key1899, -1), (key1903, 1), (key1911, -1), (key1918, -2), (key1920, 1), (key1926, 1)]

def row6428 : Integer.Sparse Key := [(key1318, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1426, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1548, -1), (key1556, 1), (key1575, -1), (key1593, 1), (key1681, 2), (key1683, -1), (key1689, -1), (key1896, 1), (key1899, -1), (key1903, 1), (key1911, -1), (key1918, -2), (key1920, 1), (key1926, 1)]

def row6429 : Integer.Sparse Key := [(key1318, -2), (key1326, 2), (key1351, 2), (key1354, -2), (key1426, -2), (key1444, 2), (key1472, 2), (key1480, -2), (key1548, 2), (key1556, -2), (key1575, 2), (key1593, -2), (key1681, -4), (key1683, 2), (key1689, 2), (key1896, -2), (key1899, 2), (key1903, -2), (key1911, 2), (key1918, 4), (key1920, -2), (key1926, -2)]

def row6430 : Integer.Sparse Key := [(key1318, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1426, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1548, -1), (key1556, 1), (key1575, -1), (key1593, 1), (key1681, 2), (key1683, -1), (key1689, -1), (key1896, 1), (key1899, -1), (key1903, 1), (key1911, -1), (key1918, -2), (key1920, 1), (key1926, 1)]

def row6431 : Integer.Sparse Key := [(key1318, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1426, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1548, -1), (key1556, 1), (key1575, -1), (key1593, 1), (key1681, 2), (key1683, -1), (key1689, -1), (key1896, 1), (key1899, -1), (key1903, 1), (key1911, -1), (key1918, -2), (key1920, 1), (key1926, 1)]

def row6432 : Integer.Sparse Key := [(key1318, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1426, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1548, -1), (key1556, 1), (key1575, -1), (key1593, 1), (key1681, 2), (key1683, -1), (key1689, -1), (key1896, 1), (key1899, -1), (key1903, 1), (key1911, -1), (key1918, -2), (key1920, 1), (key1926, 1)]

def row6433 : Integer.Sparse Key := [(key1318, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1426, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1548, -1), (key1556, 1), (key1575, -1), (key1593, 1), (key1681, 2), (key1683, -1), (key1689, -1), (key1896, 1), (key1899, -1), (key1903, 1), (key1911, -1), (key1918, -2), (key1920, 1), (key1926, 1)]

def row6434 : Integer.Sparse Key := [(key1318, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1426, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1548, -1), (key1556, 1), (key1575, -1), (key1593, 1), (key1681, 2), (key1683, -1), (key1689, -1), (key1896, 1), (key1899, -1), (key1903, 1), (key1911, -1), (key1918, -2), (key1920, 1), (key1926, 1)]

def row6435 : Integer.Sparse Key := [(key1318, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1426, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1548, -1), (key1556, 1), (key1575, -1), (key1593, 1), (key1681, 2), (key1683, -1), (key1689, -1), (key1896, 1), (key1899, -1), (key1903, 1), (key1911, -1), (key1918, -2), (key1920, 1), (key1926, 1)]

def row6436 : Integer.Sparse Key := [(key1318, -2), (key1326, 2), (key1351, 2), (key1354, -2), (key1426, -2), (key1444, 2), (key1472, 2), (key1480, -2), (key1548, 2), (key1556, -2), (key1575, 2), (key1593, -2), (key1681, -4), (key1683, 2), (key1689, 2), (key1896, -2), (key1899, 2), (key1903, -2), (key1911, 2), (key1918, 4), (key1920, -2), (key1926, -2)]

def row6437 : Integer.Sparse Key := [(key1318, -2), (key1326, 2), (key1351, 2), (key1354, -2), (key1426, -2), (key1444, 2), (key1472, 2), (key1480, -2), (key1548, 2), (key1556, -2), (key1575, 2), (key1593, -2), (key1681, -4), (key1683, 2), (key1689, 2), (key1896, -2), (key1899, 2), (key1903, -2), (key1911, 2), (key1918, 4), (key1920, -2), (key1926, -2)]

def row6438 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 1), (key2657, 1), (key2659, -1), (key2704, -1), (key2724, 1), (key2752, 1), (key2757, -1), (key2801, -1), (key2807, 2), (key2827, -1), (key2851, 1), (key2858, -1), (key2918, -2), (key2919, 1), (key2922, 1), (key3011, -1), (key3016, 1), (key3021, 1), (key3025, -1)]

def row6439 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 1), (key2657, 1), (key2659, -1), (key2704, -1), (key2724, 1), (key2752, 1), (key2757, -1), (key2801, -1), (key2807, 2), (key2827, -1), (key2851, 1), (key2858, -1), (key2918, -2), (key2919, 1), (key2922, 1), (key3011, -1), (key3016, 1), (key3021, 1), (key3025, -1)]

def row6440 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, 2), (key2638, -2), (key2657, -2), (key2659, 2), (key2704, 2), (key2724, -2), (key2752, -2), (key2757, 2), (key2801, 2), (key2807, -4), (key2827, 2), (key2851, -2), (key2858, 2), (key2918, 4), (key2919, -2), (key2922, -2), (key3011, 2), (key3016, -2), (key3021, -2), (key3025, 2)]

def row6441 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 1), (key2657, 1), (key2659, -1), (key2704, -1), (key2724, 1), (key2752, 1), (key2757, -1), (key2801, -1), (key2807, 2), (key2827, -3), (key2851, 1), (key2858, -1), (key2918, -2), (key2919, 1), (key2922, 1), (key3011, 1), (key3016, 1), (key3021, 1), (key3025, -1)]

def row6442 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 1), (key2657, 1), (key2659, -1), (key2704, -1), (key2724, 1), (key2752, 1), (key2757, -1), (key2801, -1), (key2807, 2), (key2827, -3), (key2851, 1), (key2858, -1), (key2918, -2), (key2919, 1), (key2922, 1), (key3011, 1), (key3016, 1), (key3021, 1), (key3025, -1)]

def row6443 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, 2), (key2638, -2), (key2657, -2), (key2659, 2), (key2704, 2), (key2724, -2), (key2752, -2), (key2757, 2), (key2801, 2), (key2807, -4), (key2827, 4), (key2851, -2), (key2858, 2), (key2918, 4), (key2919, -2), (key2922, -2), (key3016, -2), (key3021, -2), (key3025, 2)]

def row6444 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, 2), (key2638, -2), (key2657, -2), (key2659, 2), (key2704, 2), (key2724, -2), (key2752, -2), (key2757, 2), (key2801, 2), (key2807, -4), (key2827, 4), (key2851, -2), (key2858, 2), (key2918, 4), (key2919, -2), (key2922, -2), (key3016, -2), (key3021, -2), (key3025, 2)]

def row6445 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 1), (key2657, 1), (key2659, -1), (key2704, -1), (key2724, 1), (key2752, 1), (key2757, -1), (key2801, -1), (key2807, 2), (key2827, -3), (key2851, 1), (key2858, -1), (key2918, -2), (key2919, 1), (key2922, 1), (key3011, 1), (key3016, 1), (key3021, 1), (key3025, -1)]

def row6446 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 1), (key2657, 1), (key2659, -1), (key2704, -1), (key2724, 1), (key2752, 1), (key2757, -1), (key2801, -1), (key2807, 2), (key2827, -3), (key2851, 1), (key2858, -1), (key2918, -2), (key2919, 1), (key2922, 1), (key3011, 1), (key3016, 1), (key3021, 1), (key3025, -1)]

def row6447 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, 2), (key2638, -2), (key2657, -2), (key2659, 2), (key2704, 2), (key2724, -2), (key2752, -2), (key2757, 2), (key2801, 2), (key2807, -4), (key2827, 2), (key2851, -2), (key2858, 2), (key2918, 4), (key2919, -2), (key2922, -2), (key3011, 2), (key3016, -2), (key3021, -2), (key3025, 2)]

def row6448 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 1), (key2657, 1), (key2659, -1), (key2704, -1), (key2724, 1), (key2752, 1), (key2757, -1), (key2801, -1), (key2807, 2), (key2827, -1), (key2851, 1), (key2858, -1), (key2918, -2), (key2919, 1), (key2922, 1), (key3011, -1), (key3016, 1), (key3021, 1), (key3025, -1)]

def row6449 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 1), (key2657, 1), (key2659, -1), (key2704, -1), (key2724, 1), (key2752, 1), (key2757, -1), (key2801, -1), (key2807, 2), (key2827, -1), (key2851, 1), (key2858, -1), (key2918, -2), (key2919, 1), (key2922, 1), (key3011, -1), (key3016, 1), (key3021, 1), (key3025, -1)]

def row6450 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -3), (key2657, 1), (key2659, 1), (key2663, -1), (key2669, 1), (key2698, 2), (key2724, -2), (key2784, -1), (key2792, -1), (key2801, 1), (key2807, -1), (key2851, -2), (key2858, 3), (key2868, 3), (key2919, -1), (key2922, -1), (key3007, 1), (key3009, 1), (key3021, -2)]

def row6451 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -3), (key2657, 1), (key2659, 1), (key2663, -1), (key2669, 1), (key2698, 2), (key2724, -2), (key2784, -1), (key2792, -1), (key2801, 1), (key2807, -1), (key2851, -2), (key2858, 3), (key2868, 3), (key2919, -1), (key2922, -1), (key3007, 1), (key3009, 1), (key3021, -2)]

def row6452 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 3), (key2657, -1), (key2659, -1), (key2698, 1), (key2704, -3), (key2724, 2), (key2752, 1), (key2757, -1), (key2778, -1), (key2784, 2), (key2801, -1), (key2807, 2), (key2827, -1), (key2851, 1), (key2858, -3), (key2919, 1), (key3007, -1), (key3011, -1), (key3016, 1), (key3021, 1), (key3022, 1), (key3025, -1)]

def row6453 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 3), (key2657, -1), (key2659, -1), (key2698, 1), (key2704, -3), (key2724, 2), (key2752, 1), (key2757, -1), (key2778, -1), (key2784, 2), (key2801, -1), (key2807, 2), (key2827, -1), (key2851, 1), (key2858, -3), (key2919, 1), (key3007, -1), (key3011, -1), (key3016, 1), (key3021, 1), (key3022, 1), (key3025, -1)]

def row6454 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -3), (key2657, 1), (key2659, 1), (key2663, -1), (key2669, 1), (key2698, 2), (key2724, -1), (key2757, 1), (key2784, -1), (key2792, -1), (key2801, 1), (key2807, -1), (key2851, -2), (key2858, 3), (key2868, 3), (key2919, -1), (key2922, -1), (key3021, -2)]

def row6455 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -3), (key2657, 1), (key2659, 1), (key2663, -1), (key2669, 1), (key2698, 2), (key2724, -1), (key2757, 1), (key2784, -1), (key2792, -1), (key2801, 1), (key2807, -1), (key2851, -2), (key2858, 3), (key2868, 3), (key2919, -1), (key2922, -1), (key3021, -2)]

def row6456 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 2), (key2659, -1), (key2704, -3), (key2724, 1), (key2752, 2), (key2757, -1), (key2784, 2), (key2792, -1), (key2801, -1), (key2807, 2), (key2827, -2), (key2851, 1), (key2858, -3), (key2919, 1), (key3016, 1), (key3021, 1), (key3022, 1), (key3025, -1)]

def row6457 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 2), (key2659, -1), (key2704, -3), (key2724, 1), (key2752, 2), (key2757, -1), (key2784, 2), (key2792, -1), (key2801, -1), (key2807, 2), (key2827, -2), (key2851, 1), (key2858, -3), (key2919, 1), (key3016, 1), (key3021, 1), (key3022, 1), (key3025, -1)]

def row6458 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 2), (key2659, -1), (key2704, -3), (key2724, 1), (key2757, -1), (key2784, 2), (key2792, 1), (key2801, -1), (key2807, 2), (key2827, -2), (key2851, 1), (key2858, -3), (key2919, 1), (key3016, 1), (key3021, 1), (key3022, 1), (key3025, -1)]

def row6459 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 2), (key2659, -1), (key2704, -3), (key2724, 1), (key2757, -1), (key2784, 2), (key2792, 1), (key2801, -1), (key2807, 2), (key2827, -2), (key2851, 1), (key2858, -3), (key2919, 1), (key3016, 1), (key3021, 1), (key3022, 1), (key3025, -1)]

def row6460 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -2), (key2659, 1), (key2663, -1), (key2669, 1), (key2698, 1), (key2724, -1), (key2757, 1), (key2778, 1), (key2784, -1), (key2792, -1), (key2801, 1), (key2807, -1), (key2851, -2), (key2858, 3), (key2868, 3), (key2919, -1), (key2922, -1), (key3021, -2)]

def row6461 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -2), (key2659, 1), (key2663, -1), (key2669, 1), (key2698, 1), (key2724, -1), (key2757, 1), (key2778, 1), (key2784, -1), (key2792, -1), (key2801, 1), (key2807, -1), (key2851, -2), (key2858, 3), (key2868, 3), (key2919, -1), (key2922, -1), (key3021, -2)]

def row6462 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 3), (key2657, -1), (key2659, -1), (key2698, 1), (key2704, -3), (key2724, 2), (key2752, 1), (key2778, -1), (key2784, 2), (key2801, -1), (key2807, 2), (key2827, -2), (key2851, 1), (key2858, -3), (key2919, 1), (key3007, -1), (key3009, -1), (key3016, 1), (key3021, 1), (key3022, 1), (key3025, -1)]

def row6463 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 3), (key2657, -1), (key2659, -1), (key2698, 1), (key2704, -3), (key2724, 2), (key2752, 1), (key2778, -1), (key2784, 2), (key2801, -1), (key2807, 2), (key2827, -2), (key2851, 1), (key2858, -3), (key2919, 1), (key3007, -1), (key3009, -1), (key3016, 1), (key3021, 1), (key3022, 1), (key3025, -1)]

def row6464 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -2), (key2659, 1), (key2663, -1), (key2669, 1), (key2698, 1), (key2724, -2), (key2757, 1), (key2778, 1), (key2784, -1), (key2792, -1), (key2801, 1), (key2807, -1), (key2827, -1), (key2851, -2), (key2858, 3), (key2868, 3), (key2919, -1), (key2922, -1), (key3007, 1), (key3011, 1), (key3021, -2)]

def row6465 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -2), (key2659, 1), (key2663, -1), (key2669, 1), (key2698, 1), (key2724, -2), (key2757, 1), (key2778, 1), (key2784, -1), (key2792, -1), (key2801, 1), (key2807, -1), (key2827, -1), (key2851, -2), (key2858, 3), (key2868, 3), (key2919, -1), (key2922, -1), (key3007, 1), (key3011, 1), (key3021, -2)]

def row6466 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2638, 2), (key2657, 2), (key2659, -2), (key2663, 2), (key2669, -2), (key2698, -2), (key2724, 2), (key2752, 2), (key2757, -2), (key2778, -2), (key2784, 2), (key2801, -2), (key2807, 2), (key2851, 4), (key2858, -2), (key2868, -2), (key2918, -4), (key2919, 2), (key2922, 2)]

def row6467 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2663, -1), (key2669, 1), (key2698, 1), (key2724, -1), (key2752, -1), (key2757, 1), (key2778, 1), (key2784, -1), (key2801, 1), (key2807, -1), (key2851, -2), (key2858, 1), (key2868, 1), (key2918, 2), (key2919, -1), (key2922, -1)]

def row6468 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2663, -1), (key2669, 1), (key2698, 1), (key2724, -1), (key2752, -1), (key2757, 1), (key2778, 1), (key2784, -1), (key2801, 1), (key2807, -1), (key2851, -2), (key2858, 1), (key2868, 1), (key2918, 2), (key2919, -1), (key2922, -1)]

def row6469 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2638, 2), (key2657, 2), (key2659, -2), (key2663, 2), (key2669, -2), (key2698, -4), (key2724, 2), (key2752, 2), (key2757, -2), (key2784, 2), (key2801, -2), (key2807, 2), (key2851, 4), (key2858, -2), (key2868, -2), (key2918, -4), (key2919, 2), (key2922, 2)]

def row6470 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2663, -1), (key2669, 1), (key2698, 2), (key2724, -1), (key2752, -1), (key2757, 1), (key2784, -1), (key2801, 1), (key2807, -1), (key2851, -2), (key2858, 1), (key2868, 1), (key2918, 2), (key2919, -1), (key2922, -1)]

def row6471 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2663, -1), (key2669, 1), (key2698, 2), (key2724, -1), (key2752, -1), (key2757, 1), (key2784, -1), (key2801, 1), (key2807, -1), (key2851, -2), (key2858, 1), (key2868, 1), (key2918, 2), (key2919, -1), (key2922, -1)]

def row6472 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2663, -1), (key2669, 1), (key2698, -2), (key2724, -1), (key2752, -1), (key2757, 1), (key2778, 4), (key2784, -1), (key2801, 1), (key2807, -1), (key2851, -2), (key2858, 1), (key2868, 1), (key2918, 2), (key2919, -1), (key2922, -1)]

def row6473 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2663, -1), (key2669, 1), (key2698, -2), (key2724, -1), (key2752, -1), (key2757, 1), (key2778, 4), (key2784, -1), (key2801, 1), (key2807, -1), (key2851, -2), (key2858, 1), (key2868, 1), (key2918, 2), (key2919, -1), (key2922, -1)]

def row6474 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2663, -1), (key2669, 1), (key2698, 3), (key2724, -1), (key2752, -1), (key2757, 1), (key2778, -1), (key2784, -1), (key2801, 1), (key2807, -1), (key2851, -2), (key2858, 1), (key2868, 1), (key2918, 2), (key2919, -1), (key2922, -1)]

def row6475 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2663, -1), (key2669, 1), (key2698, 3), (key2724, -1), (key2752, -1), (key2757, 1), (key2778, -1), (key2784, -1), (key2801, 1), (key2807, -1), (key2851, -2), (key2858, 1), (key2868, 1), (key2918, 2), (key2919, -1), (key2922, -1)]

def row6476 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2638, 2), (key2657, 2), (key2659, -2), (key2663, 2), (key2669, -2), (key2698, -2), (key2724, 2), (key2752, 2), (key2757, -2), (key2778, -2), (key2784, 2), (key2801, -2), (key2807, 2), (key2851, 4), (key2858, -2), (key2868, -2), (key2918, -4), (key2919, 2), (key2922, 2)]

def row6477 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2638, 2), (key2657, 2), (key2659, -2), (key2663, 2), (key2669, -2), (key2698, -2), (key2724, 2), (key2752, 2), (key2757, -2), (key2778, -2), (key2784, 2), (key2801, -2), (key2807, 2), (key2851, 4), (key2858, -2), (key2868, -2), (key2918, -4), (key2919, 2), (key2922, 2)]

def row6478 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2621, 2), (key2632, -2), (key2640, 4), (key2644, -2), (key2658, 2), (key2660, -2), (key2671, 2), (key2676, -2), (key2706, 2), (key2726, -4), (key2732, 2), (key2753, -2), (key2758, 2), (key2794, -2), (key2798, 2), (key2829, 2), (key2835, -2), (key2860, -2), (key2870, 2), (key2920, 2), (key2923, -2)]

def row6479 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2632, 1), (key2640, -2), (key2644, 1), (key2658, -1), (key2660, 1), (key2671, -1), (key2676, 1), (key2706, -1), (key2726, 2), (key2732, -1), (key2753, 1), (key2758, -1), (key2794, 1), (key2798, -1), (key2829, -1), (key2835, 1), (key2860, 1), (key2870, -1), (key2920, -1), (key2923, 1)]

def row6480 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2632, 1), (key2640, -2), (key2644, 1), (key2658, -1), (key2660, 1), (key2671, -1), (key2676, 1), (key2706, -1), (key2726, 2), (key2732, -1), (key2753, 1), (key2758, -1), (key2794, 1), (key2798, -1), (key2829, -1), (key2835, 1), (key2860, 1), (key2870, -1), (key2920, -1), (key2923, 1)]

def row6481 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2621, 2), (key2628, -2), (key2640, 4), (key2641, 2), (key2644, -2), (key2660, -2), (key2671, 2), (key2676, -2), (key2706, 2), (key2726, -4), (key2732, 2), (key2753, -2), (key2758, 2), (key2794, -2), (key2798, 2), (key2829, 2), (key2835, -2), (key2860, -2), (key2870, 2), (key2920, 2), (key2923, -2)]

def row6482 : Integer.Sparse Key := [(key2612, 2), (key2616, -1), (key2621, -1), (key2628, 1), (key2640, -1), (key2641, -1), (key2644, 1), (key2646, -1), (key2653, 1), (key2671, -1), (key2676, 1), (key2706, -1), (key2726, 2), (key2732, -1), (key2753, 1), (key2758, -1), (key2794, 1), (key2798, -1), (key2829, -1), (key2835, 1), (key2860, 1), (key2870, -1), (key2920, -1), (key2923, 1)]

def row6483 : Integer.Sparse Key := [(key2612, 2), (key2616, -1), (key2621, -1), (key2628, 1), (key2640, -1), (key2641, -1), (key2644, 1), (key2646, -1), (key2653, 1), (key2671, -1), (key2676, 1), (key2706, -1), (key2726, 2), (key2732, -1), (key2753, 1), (key2758, -1), (key2794, 1), (key2798, -1), (key2829, -1), (key2835, 1), (key2860, 1), (key2870, -1), (key2920, -1), (key2923, 1)]

def row6484 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2628, 2), (key2632, -1), (key2640, -1), (key2641, -1), (key2646, -1), (key2648, 1), (key2653, 1), (key2671, -1), (key2676, 1), (key2706, -1), (key2726, 2), (key2732, -1), (key2753, 1), (key2758, -1), (key2794, 1), (key2798, -1), (key2829, -1), (key2835, 1), (key2860, 1), (key2870, -1), (key2920, -1), (key2923, 1)]

def row6485 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2628, 2), (key2632, -1), (key2640, -1), (key2641, -1), (key2646, -1), (key2648, 1), (key2653, 1), (key2671, -1), (key2676, 1), (key2706, -1), (key2726, 2), (key2732, -1), (key2753, 1), (key2758, -1), (key2794, 1), (key2798, -1), (key2829, -1), (key2835, 1), (key2860, 1), (key2870, -1), (key2920, -1), (key2923, 1)]

def row6486 : Integer.Sparse Key := [(key2612, 2), (key2616, -1), (key2618, -1), (key2628, -1), (key2632, 2), (key2640, -1), (key2641, -1), (key2646, -1), (key2648, 1), (key2653, 1), (key2671, -1), (key2676, 1), (key2706, -1), (key2726, 2), (key2732, -1), (key2753, 1), (key2758, -1), (key2794, 1), (key2798, -1), (key2829, -1), (key2835, 1), (key2860, 1), (key2870, -1), (key2920, -1), (key2923, 1)]

def row6487 : Integer.Sparse Key := [(key2612, 2), (key2616, -1), (key2618, -1), (key2628, -1), (key2632, 2), (key2640, -1), (key2641, -1), (key2646, -1), (key2648, 1), (key2653, 1), (key2671, -1), (key2676, 1), (key2706, -1), (key2726, 2), (key2732, -1), (key2753, 1), (key2758, -1), (key2794, 1), (key2798, -1), (key2829, -1), (key2835, 1), (key2860, 1), (key2870, -1), (key2920, -1), (key2923, 1)]

def row6488 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2618, 2), (key2628, -1), (key2632, -1), (key2640, 2), (key2641, 2), (key2646, 2), (key2648, -2), (key2653, -2), (key2671, 2), (key2676, -2), (key2706, 2), (key2726, -4), (key2732, 2), (key2753, -2), (key2758, 2), (key2794, -2), (key2798, 2), (key2829, 2), (key2835, -2), (key2860, -2), (key2870, 2), (key2920, 2), (key2923, -2)]

def row6489 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2618, 2), (key2628, -1), (key2632, -1), (key2640, 2), (key2641, 2), (key2646, 2), (key2648, -2), (key2653, -2), (key2671, 2), (key2676, -2), (key2706, 2), (key2726, -4), (key2732, 2), (key2753, -2), (key2758, 2), (key2794, -2), (key2798, 2), (key2829, 2), (key2835, -2), (key2860, -2), (key2870, 2), (key2920, 2), (key2923, -2)]

def row6490 : Integer.Sparse Key := [(key2612, 1), (key2618, -1), (key2628, 1), (key2641, -1), (key2646, -2), (key2648, 1), (key2653, 1), (key2667, -1), (key2673, 1), (key2735, 1), (key2737, -1), (key2782, -1), (key2795, 1), (key2893, 1), (key2897, -1), (key2936, 2), (key2938, -1), (key2943, -1), (key2948, -1), (key2950, 1), (key2972, -1), (key2976, 1)]

def row6491 : Integer.Sparse Key := [(key2612, 1), (key2618, -1), (key2628, 1), (key2641, -1), (key2646, -2), (key2648, 1), (key2653, 1), (key2667, -1), (key2673, 1), (key2735, 1), (key2737, -1), (key2782, -1), (key2795, 1), (key2893, 1), (key2897, -1), (key2936, 2), (key2938, -1), (key2943, -1), (key2948, -1), (key2950, 1), (key2972, -1), (key2976, 1)]

def row6492 : Integer.Sparse Key := [(key2612, 1), (key2618, -1), (key2628, 1), (key2641, -1), (key2646, -2), (key2648, 1), (key2653, 1), (key2667, -1), (key2673, 1), (key2735, 1), (key2737, -1), (key2782, -1), (key2795, 1), (key2893, 1), (key2897, -1), (key2936, 2), (key2938, -1), (key2943, -1), (key2948, -1), (key2950, 1), (key2972, -1), (key2976, 1)]

def row6493 : Integer.Sparse Key := [(key2612, 1), (key2618, -1), (key2628, 1), (key2641, -1), (key2646, -2), (key2648, 1), (key2653, 1), (key2667, -1), (key2673, 1), (key2735, 1), (key2737, -1), (key2782, -1), (key2795, 1), (key2893, 1), (key2897, -1), (key2936, 2), (key2938, -1), (key2943, -1), (key2948, -1), (key2950, 1), (key2972, -1), (key2976, 1)]

def row6494 : Integer.Sparse Key := [(key2612, 1), (key2618, -1), (key2628, 1), (key2641, -1), (key2646, -2), (key2648, 1), (key2653, 1), (key2667, -1), (key2673, 1), (key2735, 1), (key2737, -1), (key2782, -1), (key2795, 1), (key2893, 1), (key2897, -1), (key2936, 2), (key2938, -1), (key2943, -1), (key2948, -1), (key2950, 1), (key2972, -1), (key2976, 1)]

def row6495 : Integer.Sparse Key := [(key2612, 1), (key2618, -1), (key2628, 1), (key2641, -1), (key2646, -2), (key2648, 1), (key2653, 1), (key2667, -1), (key2673, 1), (key2735, 1), (key2737, -1), (key2782, -1), (key2795, 1), (key2893, 1), (key2897, -1), (key2936, 2), (key2938, -1), (key2943, -1), (key2948, -1), (key2950, 1), (key2972, -1), (key2976, 1)]

def row6496 : Integer.Sparse Key := [(key2612, 1), (key2618, -1), (key2628, 1), (key2641, -1), (key2646, -2), (key2648, 1), (key2653, 1), (key2667, -1), (key2673, 1), (key2735, 1), (key2737, -1), (key2782, -1), (key2795, 1), (key2893, 1), (key2897, -1), (key2936, 2), (key2938, -1), (key2943, -1), (key2948, -1), (key2950, 1), (key2972, -1), (key2976, 1)]

def row6497 : Integer.Sparse Key := [(key2612, 1), (key2618, -1), (key2628, 1), (key2641, -1), (key2646, -2), (key2648, 1), (key2653, 1), (key2667, -1), (key2673, 1), (key2735, 1), (key2737, -1), (key2782, -1), (key2795, 1), (key2893, 1), (key2897, -1), (key2936, 2), (key2938, -1), (key2943, -1), (key2948, -1), (key2950, 1), (key2972, -1), (key2976, 1)]

def row6498 : Integer.Sparse Key := [(key1296, -2), (key1303, 2), (key1316, -2), (key1330, 2), (key1337, 4), (key1340, -2), (key1346, -2), (key1391, 2), (key1398, -2), (key1455, -2), (key1458, 2), (key1546, 2), (key1560, -2), (key1655, -2), (key1660, 2), (key1772, -4), (key1775, 2), (key1781, 2), (key1788, 2), (key1791, -2), (key1813, 2), (key1818, -2)]

def row6499 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, 1), (key1330, -1), (key1337, -2), (key1340, 1), (key1346, 1), (key1391, -1), (key1398, 1), (key1455, 1), (key1458, -1), (key1546, -1), (key1560, 1), (key1655, 1), (key1660, -1), (key1772, 2), (key1775, -1), (key1781, -1), (key1788, -1), (key1791, 1), (key1813, -1), (key1818, 1)]

def row6500 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, 1), (key1330, -1), (key1337, -2), (key1340, 1), (key1346, 1), (key1391, -1), (key1398, 1), (key1455, 1), (key1458, -1), (key1546, -1), (key1560, 1), (key1655, 1), (key1660, -1), (key1772, 2), (key1775, -1), (key1781, -1), (key1788, -1), (key1791, 1), (key1813, -1), (key1818, 1)]

def row6501 : Integer.Sparse Key := [(key1296, -2), (key1303, 2), (key1316, -2), (key1330, 2), (key1337, 4), (key1340, -2), (key1346, -2), (key1391, 2), (key1398, -2), (key1455, -2), (key1458, 2), (key1546, 2), (key1560, -2), (key1655, -2), (key1660, 2), (key1772, -4), (key1775, 2), (key1781, 2), (key1788, 2), (key1791, -2), (key1813, 2), (key1818, -2)]

def row6502 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, 1), (key1330, -1), (key1337, -2), (key1340, 1), (key1346, 1), (key1391, -1), (key1398, 1), (key1455, 1), (key1458, -1), (key1546, -1), (key1560, 1), (key1655, 1), (key1660, -1), (key1772, 2), (key1775, -1), (key1781, -1), (key1788, -1), (key1791, 1), (key1813, -1), (key1818, 1)]

def row6503 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, 1), (key1330, -1), (key1337, -2), (key1340, 1), (key1346, 1), (key1391, -1), (key1398, 1), (key1455, 1), (key1458, -1), (key1546, -1), (key1560, 1), (key1655, 1), (key1660, -1), (key1772, 2), (key1775, -1), (key1781, -1), (key1788, -1), (key1791, 1), (key1813, -1), (key1818, 1)]

def row6504 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, 1), (key1330, -1), (key1337, -2), (key1340, 1), (key1346, 1), (key1391, -1), (key1398, 1), (key1455, 1), (key1458, -1), (key1546, -1), (key1560, 1), (key1655, 1), (key1660, -1), (key1772, 2), (key1775, -1), (key1781, -1), (key1788, -1), (key1791, 1), (key1813, -1), (key1818, 1)]

def row6505 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, 1), (key1330, -1), (key1337, -2), (key1340, 1), (key1346, 1), (key1391, -1), (key1398, 1), (key1455, 1), (key1458, -1), (key1546, -1), (key1560, 1), (key1655, 1), (key1660, -1), (key1772, 2), (key1775, -1), (key1781, -1), (key1788, -1), (key1791, 1), (key1813, -1), (key1818, 1)]

def row6506 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, 1), (key1330, -1), (key1337, -2), (key1340, 1), (key1346, 1), (key1391, -1), (key1398, 1), (key1455, 1), (key1458, -1), (key1546, -1), (key1560, 1), (key1655, 1), (key1660, -1), (key1772, 2), (key1775, -1), (key1781, -1), (key1788, -1), (key1791, 1), (key1813, -1), (key1818, 1)]

def row6507 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, 1), (key1330, -1), (key1337, -2), (key1340, 1), (key1346, 1), (key1391, -1), (key1398, 1), (key1455, 1), (key1458, -1), (key1546, -1), (key1560, 1), (key1655, 1), (key1660, -1), (key1772, 2), (key1775, -1), (key1781, -1), (key1788, -1), (key1791, 1), (key1813, -1), (key1818, 1)]

def row6508 : Integer.Sparse Key := [(key1296, -2), (key1303, 2), (key1316, -2), (key1330, 2), (key1337, 4), (key1340, -2), (key1346, -2), (key1391, 2), (key1398, -2), (key1455, -2), (key1458, 2), (key1546, 2), (key1560, -2), (key1655, -2), (key1660, 2), (key1772, -4), (key1775, 2), (key1781, 2), (key1788, 2), (key1791, -2), (key1813, 2), (key1818, -2)]

def row6509 : Integer.Sparse Key := [(key1296, -2), (key1303, 2), (key1316, -2), (key1330, 2), (key1337, 4), (key1340, -2), (key1346, -2), (key1391, 2), (key1398, -2), (key1455, -2), (key1458, 2), (key1546, 2), (key1560, -2), (key1655, -2), (key1660, 2), (key1772, -4), (key1775, 2), (key1781, 2), (key1788, 2), (key1791, -2), (key1813, 2), (key1818, -2)]

def row6510 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, 1), (key1330, -1), (key1337, -2), (key1340, 1), (key1346, 1), (key1391, -1), (key1398, 1), (key1455, 1), (key1458, -1), (key1546, -1), (key1560, 1), (key1655, 1), (key1660, -1), (key1772, 2), (key1775, -1), (key1781, -1), (key1788, -1), (key1791, 1), (key1813, -1), (key1818, 1)]

def row6511 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, 1), (key1330, -1), (key1337, -2), (key1340, 1), (key1346, 1), (key1391, -1), (key1398, 1), (key1455, 1), (key1458, -1), (key1546, -1), (key1560, 1), (key1655, 1), (key1660, -1), (key1772, 2), (key1775, -1), (key1781, -1), (key1788, -1), (key1791, 1), (key1813, -1), (key1818, 1)]

def row6512 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, 1), (key1330, -1), (key1337, -2), (key1340, 1), (key1346, 1), (key1391, -1), (key1398, 1), (key1455, 1), (key1458, -1), (key1546, -1), (key1560, 1), (key1655, 1), (key1660, -1), (key1772, 2), (key1775, -1), (key1781, -1), (key1788, -1), (key1791, 1), (key1813, -1), (key1818, 1)]

def row6513 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, 1), (key1330, -1), (key1337, -2), (key1340, 1), (key1346, 1), (key1391, -1), (key1398, 1), (key1455, 1), (key1458, -1), (key1546, -1), (key1560, 1), (key1655, 1), (key1660, -1), (key1772, 2), (key1775, -1), (key1781, -1), (key1788, -1), (key1791, 1), (key1813, -1), (key1818, 1)]

def row6514 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, 1), (key1330, -1), (key1337, -2), (key1340, 1), (key1346, 1), (key1391, -1), (key1398, 1), (key1455, 1), (key1458, -1), (key1546, -1), (key1560, 1), (key1655, 1), (key1660, -1), (key1772, 2), (key1775, -1), (key1781, -1), (key1788, -1), (key1791, 1), (key1813, -1), (key1818, 1)]

def row6515 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, 1), (key1330, -1), (key1337, -2), (key1340, 1), (key1346, 1), (key1391, -1), (key1398, 1), (key1455, 1), (key1458, -1), (key1546, -1), (key1560, 1), (key1655, 1), (key1660, -1), (key1772, 2), (key1775, -1), (key1781, -1), (key1788, -1), (key1791, 1), (key1813, -1), (key1818, 1)]

def row6516 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, 1), (key1330, -1), (key1337, -2), (key1340, 1), (key1346, 1), (key1391, -1), (key1398, 1), (key1455, 1), (key1458, -1), (key1546, -1), (key1560, 1), (key1655, 1), (key1660, -1), (key1772, 2), (key1775, -1), (key1781, -1), (key1788, -1), (key1791, 1), (key1813, -1), (key1818, 1)]

def row6517 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, 1), (key1330, -1), (key1337, -2), (key1340, 1), (key1346, 1), (key1391, -1), (key1398, 1), (key1455, 1), (key1458, -1), (key1546, -1), (key1560, 1), (key1655, 1), (key1660, -1), (key1772, 2), (key1775, -1), (key1781, -1), (key1788, -1), (key1791, 1), (key1813, -1), (key1818, 1)]

def row6518 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, -2), (key2640, 4), (key2642, -2), (key2649, 2), (key2654, -2), (key2671, 2), (key2674, -2), (key2706, 2), (key2726, -4), (key2729, 2), (key2738, -2), (key2748, 2), (key2794, -2), (key2796, 2), (key2829, 2), (key2832, -2), (key2860, -2), (key2870, 2), (key2898, 2), (key2905, -2)]

def row6519 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, -1), (key2726, 2), (key2729, -1), (key2738, 1), (key2748, -1), (key2794, 1), (key2796, -1), (key2829, -1), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -1), (key2905, 1)]

def row6520 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, -1), (key2726, 2), (key2729, -1), (key2738, 1), (key2748, -1), (key2794, 1), (key2796, -1), (key2829, -1), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -1), (key2905, 1)]

def row6521 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, -2), (key2640, 4), (key2642, -2), (key2649, 2), (key2654, -2), (key2671, 2), (key2674, -2), (key2706, 2), (key2726, -4), (key2729, 2), (key2738, -2), (key2748, 2), (key2794, -2), (key2796, 2), (key2829, 2), (key2832, -2), (key2860, -2), (key2870, 2), (key2898, 2), (key2905, -2)]

def row6522 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, -1), (key2726, 2), (key2729, -1), (key2738, 1), (key2748, -1), (key2794, 1), (key2796, -1), (key2829, -1), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -1), (key2905, 1)]

def row6523 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, -1), (key2726, 2), (key2729, -1), (key2738, 1), (key2748, -1), (key2794, 1), (key2796, -1), (key2829, -1), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -1), (key2905, 1)]

def row6524 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, -1), (key2726, 2), (key2729, -1), (key2738, 1), (key2748, -1), (key2794, 1), (key2796, -1), (key2829, -1), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -1), (key2905, 1)]

def row6525 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, -1), (key2726, 2), (key2729, -1), (key2738, 1), (key2748, -1), (key2794, 1), (key2796, -1), (key2829, -1), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -1), (key2905, 1)]

def row6526 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, -1), (key2726, 2), (key2729, -1), (key2738, 1), (key2748, -1), (key2794, 1), (key2796, -1), (key2829, -1), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -1), (key2905, 1)]

def row6527 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, -1), (key2726, 2), (key2729, -1), (key2738, 1), (key2748, -1), (key2794, 1), (key2796, -1), (key2829, -1), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -1), (key2905, 1)]

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

def row6528 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, -2), (key2640, 4), (key2642, -2), (key2649, 2), (key2654, -2), (key2671, 2), (key2674, -2), (key2706, 2), (key2726, -4), (key2729, 2), (key2738, -2), (key2748, 2), (key2794, -2), (key2796, 2), (key2829, 2), (key2832, -2), (key2860, -2), (key2870, 2), (key2898, 2), (key2905, -2)]

def row6529 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, -2), (key2640, 4), (key2642, -2), (key2649, 2), (key2654, -2), (key2671, 2), (key2674, -2), (key2706, 2), (key2726, -4), (key2729, 2), (key2738, -2), (key2748, 2), (key2794, -2), (key2796, 2), (key2829, 2), (key2832, -2), (key2860, -2), (key2870, 2), (key2898, 2), (key2905, -2)]

def row6530 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, -1), (key2726, 2), (key2729, -1), (key2738, 1), (key2748, -1), (key2794, 1), (key2796, -1), (key2829, -1), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -1), (key2905, 1)]

def row6531 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, -1), (key2726, 2), (key2729, -1), (key2738, 1), (key2748, -1), (key2794, 1), (key2796, -1), (key2829, -1), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -1), (key2905, 1)]

def row6532 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, -1), (key2726, 2), (key2729, -1), (key2738, 1), (key2748, -1), (key2794, 1), (key2796, -1), (key2829, -1), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -1), (key2905, 1)]

def row6533 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, -1), (key2726, 2), (key2729, -1), (key2738, 1), (key2748, -1), (key2794, 1), (key2796, -1), (key2829, -1), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -1), (key2905, 1)]

def row6534 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, -1), (key2726, 2), (key2729, -1), (key2738, 1), (key2748, -1), (key2794, 1), (key2796, -1), (key2829, -1), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -1), (key2905, 1)]

def row6535 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, -1), (key2726, 2), (key2729, -1), (key2738, 1), (key2748, -1), (key2794, 1), (key2796, -1), (key2829, -1), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -1), (key2905, 1)]

def row6536 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, -1), (key2726, 2), (key2729, -1), (key2738, 1), (key2748, -1), (key2794, 1), (key2796, -1), (key2829, -1), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -1), (key2905, 1)]

def row6537 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, -1), (key2726, 2), (key2729, -1), (key2738, 1), (key2748, -1), (key2794, 1), (key2796, -1), (key2829, -1), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -1), (key2905, 1)]

def row6538 : Integer.Sparse Key := [(key1004, -4), (key1008, 4), (key1021, 4), (key1023, -4), (key1039, 2), (key1043, -2), (key1078, -2), (key1081, 2), (key1117, 2), (key1129, -2), (key1157, -2), (key1176, 2), (key1195, -2), (key1201, -2), (key1202, 4), (key1214, 4), (key1216, -2), (key1225, -2)]

def row6539 : Integer.Sparse Key := [(key1004, 2), (key1008, -2), (key1021, -2), (key1023, 2), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, 1), (key1202, -2), (key1214, -2), (key1216, 1), (key1225, 1)]

def row6540 : Integer.Sparse Key := [(key1004, 2), (key1008, -2), (key1021, -2), (key1023, 2), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, 1), (key1202, -2), (key1214, -2), (key1216, 1), (key1225, 1)]

def row6541 : Integer.Sparse Key := [(key1004, -4), (key1008, 4), (key1021, 4), (key1023, -4), (key1039, 2), (key1043, -2), (key1078, -2), (key1081, 2), (key1117, 2), (key1129, -2), (key1157, -2), (key1176, 2), (key1195, -2), (key1201, -2), (key1202, 4), (key1214, 4), (key1216, -2), (key1225, -2)]

def row6542 : Integer.Sparse Key := [(key1004, 2), (key1008, -2), (key1021, -2), (key1023, 2), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, 1), (key1202, -2), (key1214, -2), (key1216, 1), (key1225, 1)]

def row6543 : Integer.Sparse Key := [(key1004, 2), (key1008, -2), (key1021, -2), (key1023, 2), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, 1), (key1202, -2), (key1214, -2), (key1216, 1), (key1225, 1)]

def row6544 : Integer.Sparse Key := [(key1004, 2), (key1008, -2), (key1021, -2), (key1023, 2), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, 1), (key1202, -2), (key1214, -2), (key1216, 1), (key1225, 1)]

def row6545 : Integer.Sparse Key := [(key1004, 2), (key1008, -2), (key1021, -2), (key1023, 2), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, 1), (key1202, -2), (key1214, -2), (key1216, 1), (key1225, 1)]

def row6546 : Integer.Sparse Key := [(key1004, 2), (key1008, -2), (key1021, -2), (key1023, 2), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, 1), (key1202, -2), (key1214, -2), (key1216, 1), (key1225, 1)]

def row6547 : Integer.Sparse Key := [(key1004, 2), (key1008, -2), (key1021, -2), (key1023, 2), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, 1), (key1202, -2), (key1214, -2), (key1216, 1), (key1225, 1)]

def row6548 : Integer.Sparse Key := [(key1004, -4), (key1008, 4), (key1021, 4), (key1023, -4), (key1039, 2), (key1043, -2), (key1078, -2), (key1081, 2), (key1117, 2), (key1129, -2), (key1157, -2), (key1176, 2), (key1195, -2), (key1201, -2), (key1202, 4), (key1214, 4), (key1216, -2), (key1225, -2)]

def row6549 : Integer.Sparse Key := [(key1004, -4), (key1008, 4), (key1021, 4), (key1023, -4), (key1039, 2), (key1043, -2), (key1078, -2), (key1081, 2), (key1117, 2), (key1129, -2), (key1157, -2), (key1176, 2), (key1195, -2), (key1201, -2), (key1202, 4), (key1214, 4), (key1216, -2), (key1225, -2)]

def row6550 : Integer.Sparse Key := [(key1004, 2), (key1008, -2), (key1021, -2), (key1023, 2), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, 1), (key1202, -2), (key1214, -2), (key1216, 1), (key1225, 1)]

def row6551 : Integer.Sparse Key := [(key1004, 2), (key1008, -2), (key1021, -2), (key1023, 2), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, 1), (key1202, -2), (key1214, -2), (key1216, 1), (key1225, 1)]

def row6552 : Integer.Sparse Key := [(key1004, 2), (key1008, -2), (key1021, -2), (key1023, 2), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, 1), (key1202, -2), (key1214, -2), (key1216, 1), (key1225, 1)]

def row6553 : Integer.Sparse Key := [(key1004, 2), (key1008, -2), (key1021, -2), (key1023, 2), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, 1), (key1202, -2), (key1214, -2), (key1216, 1), (key1225, 1)]

def row6554 : Integer.Sparse Key := [(key1004, 2), (key1008, -2), (key1021, -2), (key1023, 2), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, 1), (key1202, -2), (key1214, -2), (key1216, 1), (key1225, 1)]

def row6555 : Integer.Sparse Key := [(key1004, 2), (key1008, -2), (key1021, -2), (key1023, 2), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, 1), (key1202, -2), (key1214, -2), (key1216, 1), (key1225, 1)]

def row6556 : Integer.Sparse Key := [(key1004, 2), (key1008, -2), (key1021, -2), (key1023, 2), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, 1), (key1202, -2), (key1214, -2), (key1216, 1), (key1225, 1)]

def row6557 : Integer.Sparse Key := [(key1004, 2), (key1008, -2), (key1021, -2), (key1023, 2), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, 1), (key1202, -2), (key1214, -2), (key1216, 1), (key1225, 1)]

def row6558 : Integer.Sparse Key := [(key2379, -4), (key2382, 4), (key2393, 4), (key2395, -4), (key2771, 2), (key2774, -2), (key2848, 2), (key2882, -2), (key2891, -2), (key2912, -2), (key2914, 4), (key2933, -2), (key2934, 2), (key2970, -2), (key2991, 4), (key2993, -2), (key2996, 2), (key3003, -2)]

def row6559 : Integer.Sparse Key := [(key2379, 2), (key2382, -2), (key2393, -2), (key2395, 2), (key2771, -1), (key2774, 1), (key2848, -1), (key2882, 1), (key2891, 1), (key2912, 1), (key2914, -2), (key2933, 1), (key2934, -1), (key2970, 1), (key2991, -2), (key2993, 1), (key2996, -1), (key3003, 1)]

def row6560 : Integer.Sparse Key := [(key2379, 2), (key2382, -2), (key2393, -2), (key2395, 2), (key2771, -1), (key2774, 1), (key2848, -1), (key2882, 1), (key2891, 1), (key2912, 1), (key2914, -2), (key2933, 1), (key2934, -1), (key2970, 1), (key2991, -2), (key2993, 1), (key2996, -1), (key3003, 1)]

def row6561 : Integer.Sparse Key := [(key2379, -4), (key2382, 4), (key2393, 4), (key2395, -4), (key2771, 2), (key2774, -2), (key2848, 2), (key2882, -2), (key2891, -2), (key2912, -2), (key2914, 4), (key2933, -2), (key2934, 2), (key2970, -2), (key2991, 4), (key2993, -2), (key2996, 2), (key3003, -2)]

def row6562 : Integer.Sparse Key := [(key2379, 2), (key2382, -2), (key2393, -2), (key2395, 2), (key2771, -1), (key2774, 1), (key2848, -1), (key2882, 1), (key2891, 1), (key2912, 1), (key2914, -2), (key2933, 1), (key2934, -1), (key2970, 1), (key2991, -2), (key2993, 1), (key2996, -1), (key3003, 1)]

def row6563 : Integer.Sparse Key := [(key2379, 2), (key2382, -2), (key2393, -2), (key2395, 2), (key2771, -1), (key2774, 1), (key2848, -1), (key2882, 1), (key2891, 1), (key2912, 1), (key2914, -2), (key2933, 1), (key2934, -1), (key2970, 1), (key2991, -2), (key2993, 1), (key2996, -1), (key3003, 1)]

def row6564 : Integer.Sparse Key := [(key2379, 2), (key2382, -2), (key2393, -2), (key2395, 2), (key2771, -1), (key2774, 1), (key2848, -1), (key2882, 1), (key2891, 1), (key2912, 1), (key2914, -2), (key2933, 1), (key2934, -1), (key2970, 1), (key2991, -2), (key2993, 1), (key2996, -1), (key3003, 1)]

def row6565 : Integer.Sparse Key := [(key2379, 2), (key2382, -2), (key2393, -2), (key2395, 2), (key2771, -1), (key2774, 1), (key2848, -1), (key2882, 1), (key2891, 1), (key2912, 1), (key2914, -2), (key2933, 1), (key2934, -1), (key2970, 1), (key2991, -2), (key2993, 1), (key2996, -1), (key3003, 1)]

def row6566 : Integer.Sparse Key := [(key2379, 2), (key2382, -2), (key2393, -2), (key2395, 2), (key2771, -1), (key2774, 1), (key2848, -1), (key2882, 1), (key2891, 1), (key2912, 1), (key2914, -2), (key2933, 1), (key2934, -1), (key2970, 1), (key2991, -2), (key2993, 1), (key2996, -1), (key3003, 1)]

def row6567 : Integer.Sparse Key := [(key2379, 2), (key2382, -2), (key2393, -2), (key2395, 2), (key2771, -1), (key2774, 1), (key2848, -1), (key2882, 1), (key2891, 1), (key2912, 1), (key2914, -2), (key2933, 1), (key2934, -1), (key2970, 1), (key2991, -2), (key2993, 1), (key2996, -1), (key3003, 1)]

def row6568 : Integer.Sparse Key := [(key2379, -4), (key2382, 4), (key2393, 4), (key2395, -4), (key2771, 2), (key2774, -2), (key2848, 2), (key2882, -2), (key2891, -2), (key2912, -2), (key2914, 4), (key2933, -2), (key2934, 2), (key2970, -2), (key2991, 4), (key2993, -2), (key2996, 2), (key3003, -2)]

def row6569 : Integer.Sparse Key := [(key2379, -4), (key2382, 4), (key2393, 4), (key2395, -4), (key2771, 2), (key2774, -2), (key2848, 2), (key2882, -2), (key2891, -2), (key2912, -2), (key2914, 4), (key2933, -2), (key2934, 2), (key2970, -2), (key2991, 4), (key2993, -2), (key2996, 2), (key3003, -2)]

def row6570 : Integer.Sparse Key := [(key2379, 2), (key2382, -2), (key2393, -2), (key2395, 2), (key2410, -1), (key2441, 2), (key2445, -1), (key2483, -1), (key2507, 2), (key2526, -1), (key2539, 2), (key2544, 2), (key2545, -2), (key2555, -4), (key2557, 1), (key2565, 1), (key2771, -1), (key2774, 2), (key2848, -1), (key2882, -1), (key2891, 2), (key2912, -1), (key2933, -1), (key2970, -1), (key2991, 2)]

def row6571 : Integer.Sparse Key := [(key2379, 2), (key2382, -2), (key2393, -2), (key2395, 2), (key2410, -1), (key2441, 2), (key2445, -1), (key2483, -1), (key2507, 2), (key2526, -1), (key2539, 2), (key2544, 2), (key2545, -2), (key2555, -4), (key2557, 1), (key2565, 1), (key2771, -1), (key2774, 2), (key2848, -1), (key2882, -1), (key2891, 2), (key2912, -1), (key2933, -1), (key2970, -1), (key2991, 2)]

def row6572 : Integer.Sparse Key := [(key2382, -1), (key2393, -1), (key2395, 2), (key2407, -1), (key2410, 1), (key2441, 1), (key2445, -1), (key2483, -1), (key2507, 2), (key2526, -1), (key2539, 2), (key2544, 2), (key2545, -2), (key2555, -4), (key2557, 1), (key2565, 1), (key2592, 2), (key2595, -1), (key2602, -1), (key2848, -1), (key2882, -1), (key2891, 2), (key2912, -1), (key2970, -1), (key2991, 2)]

def row6573 : Integer.Sparse Key := [(key2382, -1), (key2393, -1), (key2395, 2), (key2407, -1), (key2410, 1), (key2441, 1), (key2445, -1), (key2483, -1), (key2507, 2), (key2526, -1), (key2539, 2), (key2544, 2), (key2545, -2), (key2555, -4), (key2557, 1), (key2565, 1), (key2592, 2), (key2595, -1), (key2602, -1), (key2848, -1), (key2882, -1), (key2891, 2), (key2912, -1), (key2970, -1), (key2991, 2)]

def row6574 : Integer.Sparse Key := [(key2382, -1), (key2393, -1), (key2395, 2), (key2407, -1), (key2410, -1), (key2441, 1), (key2445, -1), (key2473, -1), (key2483, 1), (key2507, 1), (key2526, -1), (key2539, 2), (key2544, 2), (key2545, -2), (key2555, -4), (key2557, 1), (key2565, 1), (key2592, 2), (key2595, -1), (key2602, -1), (key2774, 2), (key2882, -1), (key2912, -1), (key2991, 2)]

def row6575 : Integer.Sparse Key := [(key2382, -1), (key2393, -1), (key2395, 2), (key2407, -1), (key2410, -1), (key2441, 1), (key2445, -1), (key2473, -1), (key2483, 1), (key2507, 1), (key2526, -1), (key2539, 2), (key2544, 2), (key2545, -2), (key2555, -4), (key2557, 1), (key2565, 1), (key2592, 2), (key2595, -1), (key2602, -1), (key2774, 2), (key2882, -1), (key2912, -1), (key2991, 2)]

def row6576 : Integer.Sparse Key := [(key2379, 2), (key2382, -2), (key2393, -2), (key2395, 2), (key2410, 1), (key2441, 1), (key2445, -1), (key2483, 1), (key2507, 1), (key2526, -1), (key2539, 1), (key2544, 1), (key2545, -2), (key2555, -2), (key2557, 1), (key2565, 1), (key2771, -1), (key2848, -1)]

def row6577 : Integer.Sparse Key := [(key2379, 2), (key2382, -2), (key2393, -2), (key2395, 2), (key2410, 1), (key2441, 1), (key2445, -1), (key2483, 1), (key2507, 1), (key2526, -1), (key2539, 1), (key2544, 1), (key2545, -2), (key2555, -2), (key2557, 1), (key2565, 1), (key2771, -1), (key2848, -1)]

def row6578 : Integer.Sparse Key := [(key2672, -2), (key2675, 2), (key2707, -2), (key2730, 2), (key2739, 2), (key2749, 2), (key2751, -4), (key2787, 2), (key2797, -2), (key2810, 2), (key2833, -2), (key2899, -2), (key2906, -2), (key2915, 4), (key2940, -2), (key2945, 2), (key2952, -2), (key2964, 2), (key2978, 2), (key2994, -2), (key3001, 2), (key3004, -2)]

def row6579 : Integer.Sparse Key := [(key2672, 1), (key2675, -1), (key2707, 1), (key2730, -1), (key2739, -1), (key2749, -1), (key2751, 2), (key2787, -1), (key2797, 1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, 1), (key2915, -2), (key2940, 1), (key2945, -1), (key2952, 1), (key2964, -1), (key2978, -1), (key2994, 1), (key3001, -1), (key3004, 1)]

def row6580 : Integer.Sparse Key := [(key2672, 1), (key2675, -1), (key2707, 1), (key2730, -1), (key2739, -1), (key2749, -1), (key2751, 2), (key2787, -1), (key2797, 1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, 1), (key2915, -2), (key2940, 1), (key2945, -1), (key2952, 1), (key2964, -1), (key2978, -1), (key2994, 1), (key3001, -1), (key3004, 1)]

def row6581 : Integer.Sparse Key := [(key2672, -2), (key2675, 2), (key2707, -2), (key2730, 2), (key2739, 2), (key2749, 2), (key2751, -4), (key2787, 2), (key2797, -2), (key2810, 2), (key2833, -2), (key2899, -2), (key2906, -2), (key2915, 4), (key2940, -2), (key2945, 2), (key2952, -2), (key2964, 2), (key2978, 2), (key2994, -2), (key3001, 2), (key3004, -2)]

def row6582 : Integer.Sparse Key := [(key2672, 1), (key2675, -1), (key2707, 1), (key2730, -1), (key2739, -1), (key2749, -1), (key2751, 2), (key2787, -1), (key2797, 1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, 1), (key2915, -2), (key2940, 1), (key2945, -1), (key2952, 1), (key2964, -1), (key2978, -1), (key2994, 1), (key3001, -1), (key3004, 1)]

def row6583 : Integer.Sparse Key := [(key2672, 1), (key2675, -1), (key2707, 1), (key2730, -1), (key2739, -1), (key2749, -1), (key2751, 2), (key2787, -1), (key2797, 1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, 1), (key2915, -2), (key2940, 1), (key2945, -1), (key2952, 1), (key2964, -1), (key2978, -1), (key2994, 1), (key3001, -1), (key3004, 1)]

def row6584 : Integer.Sparse Key := [(key2672, 1), (key2675, -1), (key2707, 1), (key2730, -1), (key2739, -1), (key2749, -1), (key2751, 2), (key2787, -1), (key2797, 1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, 1), (key2915, -2), (key2940, 1), (key2945, -1), (key2952, 1), (key2964, -1), (key2978, -1), (key2994, 1), (key3001, -1), (key3004, 1)]

def row6585 : Integer.Sparse Key := [(key2672, 1), (key2675, -1), (key2707, 1), (key2730, -1), (key2739, -1), (key2749, -1), (key2751, 2), (key2787, -1), (key2797, 1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, 1), (key2915, -2), (key2940, 1), (key2945, -1), (key2952, 1), (key2964, -1), (key2978, -1), (key2994, 1), (key3001, -1), (key3004, 1)]

def row6586 : Integer.Sparse Key := [(key2672, 1), (key2675, -1), (key2707, 1), (key2730, -1), (key2739, -1), (key2749, -1), (key2751, 2), (key2787, -1), (key2797, 1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, 1), (key2915, -2), (key2940, 1), (key2945, -1), (key2952, 1), (key2964, -1), (key2978, -1), (key2994, 1), (key3001, -1), (key3004, 1)]

def row6587 : Integer.Sparse Key := [(key2672, 1), (key2675, -1), (key2707, 1), (key2730, -1), (key2739, -1), (key2749, -1), (key2751, 2), (key2787, -1), (key2797, 1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, 1), (key2915, -2), (key2940, 1), (key2945, -1), (key2952, 1), (key2964, -1), (key2978, -1), (key2994, 1), (key3001, -1), (key3004, 1)]

def row6588 : Integer.Sparse Key := [(key2672, -2), (key2675, 2), (key2707, -2), (key2730, 2), (key2739, 2), (key2749, 2), (key2751, -4), (key2787, 2), (key2797, -2), (key2810, 2), (key2833, -2), (key2899, -2), (key2906, -2), (key2915, 4), (key2940, -2), (key2945, 2), (key2952, -2), (key2964, 2), (key2978, 2), (key2994, -2), (key3001, 2), (key3004, -2)]

def row6589 : Integer.Sparse Key := [(key2672, -2), (key2675, 2), (key2707, -2), (key2730, 2), (key2739, 2), (key2749, 2), (key2751, -4), (key2787, 2), (key2797, -2), (key2810, 2), (key2833, -2), (key2899, -2), (key2906, -2), (key2915, 4), (key2940, -2), (key2945, 2), (key2952, -2), (key2964, 2), (key2978, 2), (key2994, -2), (key3001, 2), (key3004, -2)]

def row6590 : Integer.Sparse Key := [(key2672, 1), (key2675, -1), (key2707, 1), (key2730, 1), (key2739, 1), (key2749, -3), (key2787, -1), (key2797, -1), (key2810, -1), (key2833, 3), (key2899, 1), (key2906, -1), (key2940, -1), (key2945, 1), (key2946, 2), (key2952, -1), (key2964, -1), (key2978, 1), (key2994, -1), (key2999, -2), (key3001, 1), (key3004, 1)]

def row6591 : Integer.Sparse Key := [(key2672, 1), (key2675, -1), (key2707, 1), (key2730, 1), (key2739, 1), (key2749, -3), (key2787, -1), (key2797, -1), (key2810, -1), (key2833, 3), (key2899, 1), (key2906, -1), (key2940, -1), (key2945, 1), (key2946, 2), (key2952, -1), (key2964, -1), (key2978, 1), (key2994, -1), (key2999, -2), (key3001, 1), (key3004, 1)]

def row6592 : Integer.Sparse Key := [(key2643, -2), (key2650, 2), (key2672, 1), (key2675, -1), (key2739, 1), (key2749, -2), (key2797, -1), (key2810, -1), (key2833, 2), (key2899, 1), (key2906, -1), (key2946, 2), (key2964, -1), (key2978, 1), (key2994, -1), (key2999, -2), (key3001, 1), (key3004, 1)]

def row6593 : Integer.Sparse Key := [(key2643, -2), (key2650, 2), (key2672, 1), (key2675, -1), (key2739, 1), (key2749, -2), (key2797, -1), (key2810, -1), (key2833, 2), (key2899, 1), (key2906, -1), (key2946, 2), (key2964, -1), (key2978, 1), (key2994, -1), (key2999, -2), (key3001, 1), (key3004, 1)]

def row6594 : Integer.Sparse Key := [(key2643, -1), (key2650, 1), (key2672, 1), (key2675, -1), (key2707, -1), (key2739, 1), (key2749, -2), (key2787, 1), (key2797, -1), (key2810, -1), (key2833, 2), (key2899, 1), (key2906, -1), (key2946, 2), (key2964, -1), (key2978, 1), (key2994, -1), (key2999, -2), (key3001, 1), (key3004, 1)]

def row6595 : Integer.Sparse Key := [(key2643, -1), (key2650, 1), (key2672, 1), (key2675, -1), (key2707, -1), (key2739, 1), (key2749, -2), (key2787, 1), (key2797, -1), (key2810, -1), (key2833, 2), (key2899, 1), (key2906, -1), (key2946, 2), (key2964, -1), (key2978, 1), (key2994, -1), (key2999, -2), (key3001, 1), (key3004, 1)]

def row6596 : Integer.Sparse Key := [(key2672, 1), (key2675, -1), (key2707, 1), (key2730, 1), (key2739, 1), (key2749, -1), (key2787, -1), (key2797, -1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, -1), (key2940, -1), (key2945, -1), (key2946, 2), (key2952, 1), (key2964, -1), (key2978, 1), (key2994, -1), (key2999, -2), (key3001, 1), (key3004, 1)]

def row6597 : Integer.Sparse Key := [(key2672, 1), (key2675, -1), (key2707, 1), (key2730, 1), (key2739, 1), (key2749, -1), (key2787, -1), (key2797, -1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, -1), (key2940, -1), (key2945, -1), (key2946, 2), (key2952, 1), (key2964, -1), (key2978, 1), (key2994, -1), (key2999, -2), (key3001, 1), (key3004, 1)]

def row6598 : Integer.Sparse Key := [(key1296, -2), (key1302, 2), (key1316, -2), (key1329, 2), (key1337, 4), (key1339, -2), (key1345, -2), (key1391, 2), (key1397, -2), (key1455, -2), (key1457, 2), (key1546, 2), (key1559, -2), (key1655, -2), (key1659, 2), (key1772, -4), (key1774, 2), (key1780, 2), (key1788, 2), (key1790, -2), (key1813, 2), (key1817, -2)]

def row6599 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, 1), (key1329, -1), (key1337, -2), (key1339, 1), (key1345, 1), (key1391, -1), (key1397, 1), (key1455, 1), (key1457, -1), (key1546, -1), (key1559, 1), (key1655, 1), (key1659, -1), (key1772, 2), (key1774, -1), (key1780, -1), (key1788, -1), (key1790, 1), (key1813, -1), (key1817, 1)]

def row6600 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, 1), (key1329, -1), (key1337, -2), (key1339, 1), (key1345, 1), (key1391, -1), (key1397, 1), (key1455, 1), (key1457, -1), (key1546, -1), (key1559, 1), (key1655, 1), (key1659, -1), (key1772, 2), (key1774, -1), (key1780, -1), (key1788, -1), (key1790, 1), (key1813, -1), (key1817, 1)]

def row6601 : Integer.Sparse Key := [(key1296, -2), (key1302, 2), (key1316, -2), (key1329, 2), (key1337, 4), (key1339, -2), (key1345, -2), (key1391, 2), (key1397, -2), (key1455, -2), (key1457, 2), (key1546, 2), (key1559, -2), (key1655, -2), (key1659, 2), (key1772, -4), (key1774, 2), (key1780, 2), (key1788, 2), (key1790, -2), (key1813, 2), (key1817, -2)]

def row6602 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, 1), (key1329, -1), (key1337, -2), (key1339, 1), (key1345, 1), (key1391, -1), (key1397, 1), (key1455, 1), (key1457, -1), (key1546, -1), (key1559, 1), (key1655, 1), (key1659, -1), (key1772, 2), (key1774, -1), (key1780, -1), (key1788, -1), (key1790, 1), (key1813, -1), (key1817, 1)]

def row6603 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, 1), (key1329, -1), (key1337, -2), (key1339, 1), (key1345, 1), (key1391, -1), (key1397, 1), (key1455, 1), (key1457, -1), (key1546, -1), (key1559, 1), (key1655, 1), (key1659, -1), (key1772, 2), (key1774, -1), (key1780, -1), (key1788, -1), (key1790, 1), (key1813, -1), (key1817, 1)]

def row6604 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, 1), (key1329, -1), (key1337, -2), (key1339, 1), (key1345, 1), (key1391, -1), (key1397, 1), (key1455, 1), (key1457, -1), (key1546, -1), (key1559, 1), (key1655, 1), (key1659, -1), (key1772, 2), (key1774, -1), (key1780, -1), (key1788, -1), (key1790, 1), (key1813, -1), (key1817, 1)]

def row6605 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, 1), (key1329, -1), (key1337, -2), (key1339, 1), (key1345, 1), (key1391, -1), (key1397, 1), (key1455, 1), (key1457, -1), (key1546, -1), (key1559, 1), (key1655, 1), (key1659, -1), (key1772, 2), (key1774, -1), (key1780, -1), (key1788, -1), (key1790, 1), (key1813, -1), (key1817, 1)]

def row6606 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, 1), (key1329, -1), (key1337, -2), (key1339, 1), (key1345, 1), (key1391, -1), (key1397, 1), (key1455, 1), (key1457, -1), (key1546, -1), (key1559, 1), (key1655, 1), (key1659, -1), (key1772, 2), (key1774, -1), (key1780, -1), (key1788, -1), (key1790, 1), (key1813, -1), (key1817, 1)]

def row6607 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, 1), (key1329, -1), (key1337, -2), (key1339, 1), (key1345, 1), (key1391, -1), (key1397, 1), (key1455, 1), (key1457, -1), (key1546, -1), (key1559, 1), (key1655, 1), (key1659, -1), (key1772, 2), (key1774, -1), (key1780, -1), (key1788, -1), (key1790, 1), (key1813, -1), (key1817, 1)]

def row6608 : Integer.Sparse Key := [(key1296, -2), (key1302, 2), (key1316, -2), (key1329, 2), (key1337, 4), (key1339, -2), (key1345, -2), (key1391, 2), (key1397, -2), (key1455, -2), (key1457, 2), (key1546, 2), (key1559, -2), (key1655, -2), (key1659, 2), (key1772, -4), (key1774, 2), (key1780, 2), (key1788, 2), (key1790, -2), (key1813, 2), (key1817, -2)]

def row6609 : Integer.Sparse Key := [(key1296, -2), (key1302, 2), (key1316, -2), (key1329, 2), (key1337, 4), (key1339, -2), (key1345, -2), (key1391, 2), (key1397, -2), (key1455, -2), (key1457, 2), (key1546, 2), (key1559, -2), (key1655, -2), (key1659, 2), (key1772, -4), (key1774, 2), (key1780, 2), (key1788, 2), (key1790, -2), (key1813, 2), (key1817, -2)]

def row6610 : Integer.Sparse Key := [(key1316, 2), (key1329, -2), (key1337, -2), (key1345, 2), (key1424, 2), (key1447, -2), (key1455, -2), (key1466, 2), (key1546, -2), (key1559, 2), (key1573, -2), (key1596, 2), (key1655, 4), (key1659, -2), (key1667, -2), (key1772, 2), (key1780, -2), (key1788, 2), (key1798, -2), (key1813, -4), (key1817, 2), (key1825, 2)]

def row6611 : Integer.Sparse Key := [(key1316, -1), (key1329, 1), (key1337, 1), (key1345, -1), (key1424, -1), (key1447, 1), (key1455, 1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1772, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 2), (key1817, -1), (key1825, -1)]

def row6612 : Integer.Sparse Key := [(key1316, -1), (key1329, 1), (key1337, 1), (key1345, -1), (key1424, -1), (key1447, 1), (key1455, 1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1772, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 2), (key1817, -1), (key1825, -1)]

def row6613 : Integer.Sparse Key := [(key1316, 2), (key1329, -2), (key1337, -2), (key1345, 2), (key1424, 2), (key1447, -2), (key1455, -2), (key1466, 2), (key1546, -2), (key1559, 2), (key1573, -2), (key1596, 2), (key1655, 4), (key1659, -2), (key1667, -2), (key1772, 2), (key1780, -2), (key1788, 2), (key1798, -2), (key1813, -4), (key1817, 2), (key1825, 2)]

def row6614 : Integer.Sparse Key := [(key1316, -1), (key1329, 1), (key1337, 1), (key1345, -1), (key1424, -1), (key1447, 1), (key1455, 1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1772, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 2), (key1817, -1), (key1825, -1)]

def row6615 : Integer.Sparse Key := [(key1316, -1), (key1329, 1), (key1337, 1), (key1345, -1), (key1424, -1), (key1447, 1), (key1455, 1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1772, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 2), (key1817, -1), (key1825, -1)]

def row6616 : Integer.Sparse Key := [(key1316, -1), (key1329, 1), (key1337, 1), (key1345, -1), (key1424, -1), (key1447, 1), (key1455, 1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1772, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 2), (key1817, -1), (key1825, -1)]

def row6617 : Integer.Sparse Key := [(key1316, -1), (key1329, 1), (key1337, 1), (key1345, -1), (key1424, -1), (key1447, 1), (key1455, 1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1772, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 2), (key1817, -1), (key1825, -1)]

def row6618 : Integer.Sparse Key := [(key1316, -1), (key1329, 1), (key1337, 1), (key1345, -1), (key1424, -1), (key1447, 1), (key1455, 1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1772, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 2), (key1817, -1), (key1825, -1)]

def row6619 : Integer.Sparse Key := [(key1316, -1), (key1329, 1), (key1337, 1), (key1345, -1), (key1424, -1), (key1447, 1), (key1455, 1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1772, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 2), (key1817, -1), (key1825, -1)]

def row6620 : Integer.Sparse Key := [(key1316, 2), (key1329, -2), (key1337, -2), (key1345, 2), (key1424, 2), (key1447, -2), (key1455, -2), (key1466, 2), (key1546, -2), (key1559, 2), (key1573, -2), (key1596, 2), (key1655, 4), (key1659, -2), (key1667, -2), (key1772, 2), (key1780, -2), (key1788, 2), (key1798, -2), (key1813, -4), (key1817, 2), (key1825, 2)]

def row6621 : Integer.Sparse Key := [(key1316, 2), (key1329, -2), (key1337, -2), (key1345, 2), (key1424, 2), (key1447, -2), (key1455, -2), (key1466, 2), (key1546, -2), (key1559, 2), (key1573, -2), (key1596, 2), (key1655, 4), (key1659, -2), (key1667, -2), (key1772, 2), (key1780, -2), (key1788, 2), (key1798, -2), (key1813, -4), (key1817, 2), (key1825, 2)]

def row6622 : Integer.Sparse Key := [(key1316, -1), (key1329, 1), (key1337, 1), (key1345, -1), (key1424, -1), (key1447, 1), (key1455, 1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1772, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 2), (key1817, -1), (key1825, -1)]

def row6623 : Integer.Sparse Key := [(key1316, -1), (key1329, 1), (key1337, 1), (key1345, -1), (key1424, -1), (key1447, 1), (key1455, 1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1772, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 2), (key1817, -1), (key1825, -1)]

def row6624 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, 1), (key1329, -1), (key1337, -2), (key1339, 1), (key1345, 1), (key1391, -1), (key1397, 1), (key1455, 1), (key1457, -1), (key1546, -1), (key1559, 1), (key1655, 1), (key1659, -1), (key1772, 2), (key1774, -1), (key1780, -1), (key1788, -1), (key1790, 1), (key1813, -1), (key1817, 1)]

def row6625 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, 1), (key1329, -1), (key1337, -2), (key1339, 1), (key1345, 1), (key1391, -1), (key1397, 1), (key1455, 1), (key1457, -1), (key1546, -1), (key1559, 1), (key1655, 1), (key1659, -1), (key1772, 2), (key1774, -1), (key1780, -1), (key1788, -1), (key1790, 1), (key1813, -1), (key1817, 1)]

def row6626 : Integer.Sparse Key := [(key1316, -1), (key1329, 1), (key1337, 1), (key1345, -1), (key1424, -1), (key1447, 1), (key1455, 1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1772, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 2), (key1817, -1), (key1825, -1)]

def row6627 : Integer.Sparse Key := [(key1316, -1), (key1329, 1), (key1337, 1), (key1345, -1), (key1424, -1), (key1447, 1), (key1455, 1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1772, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 2), (key1817, -1), (key1825, -1)]

def row6628 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, 1), (key1329, -1), (key1337, -2), (key1339, 1), (key1345, 1), (key1391, -1), (key1397, 1), (key1455, 1), (key1457, -1), (key1546, -1), (key1559, 1), (key1655, 1), (key1659, -1), (key1772, 2), (key1774, -1), (key1780, -1), (key1788, -1), (key1790, 1), (key1813, -1), (key1817, 1)]

def row6629 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, 1), (key1329, -1), (key1337, -2), (key1339, 1), (key1345, 1), (key1391, -1), (key1397, 1), (key1455, 1), (key1457, -1), (key1546, -1), (key1559, 1), (key1655, 1), (key1659, -1), (key1772, 2), (key1774, -1), (key1780, -1), (key1788, -1), (key1790, 1), (key1813, -1), (key1817, 1)]

def row6630 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, 1), (key1329, -1), (key1337, -2), (key1339, 1), (key1345, 1), (key1391, -1), (key1397, 1), (key1455, 1), (key1457, -1), (key1546, -1), (key1559, 1), (key1655, 1), (key1659, -1), (key1772, 2), (key1774, -1), (key1780, -1), (key1788, -1), (key1790, 1), (key1813, -1), (key1817, 1)]

def row6631 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, 1), (key1329, -1), (key1337, -2), (key1339, 1), (key1345, 1), (key1391, -1), (key1397, 1), (key1455, 1), (key1457, -1), (key1546, -1), (key1559, 1), (key1655, 1), (key1659, -1), (key1772, 2), (key1774, -1), (key1780, -1), (key1788, -1), (key1790, 1), (key1813, -1), (key1817, 1)]

def row6632 : Integer.Sparse Key := [(key1316, -1), (key1329, 1), (key1337, 1), (key1345, -1), (key1424, -1), (key1447, 1), (key1455, 1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1772, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 2), (key1817, -1), (key1825, -1)]

def row6633 : Integer.Sparse Key := [(key1316, -1), (key1329, 1), (key1337, 1), (key1345, -1), (key1424, -1), (key1447, 1), (key1455, 1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1772, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 2), (key1817, -1), (key1825, -1)]

def row6634 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, 1), (key1329, -1), (key1337, -2), (key1339, 1), (key1345, 1), (key1391, -1), (key1397, 1), (key1455, 1), (key1457, -1), (key1546, -1), (key1559, 1), (key1655, 1), (key1659, -1), (key1772, 2), (key1774, -1), (key1780, -1), (key1788, -1), (key1790, 1), (key1813, -1), (key1817, 1)]

def row6635 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, 1), (key1329, -1), (key1337, -2), (key1339, 1), (key1345, 1), (key1391, -1), (key1397, 1), (key1455, 1), (key1457, -1), (key1546, -1), (key1559, 1), (key1655, 1), (key1659, -1), (key1772, 2), (key1774, -1), (key1780, -1), (key1788, -1), (key1790, 1), (key1813, -1), (key1817, 1)]

def row6636 : Integer.Sparse Key := [(key1316, -1), (key1329, 1), (key1337, 1), (key1345, -1), (key1424, -1), (key1447, 1), (key1455, 1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1772, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 2), (key1817, -1), (key1825, -1)]

def row6637 : Integer.Sparse Key := [(key1316, -1), (key1329, 1), (key1337, 1), (key1345, -1), (key1424, -1), (key1447, 1), (key1455, 1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1772, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 2), (key1817, -1), (key1825, -1)]

def row6638 : Integer.Sparse Key := [(key2671, 2), (key2676, -2), (key2706, 2), (key2726, -4), (key2732, 2), (key2753, -2), (key2758, 2), (key2786, -2), (key2798, 2), (key2809, -2), (key2829, 2), (key2870, 2), (key2885, -2), (key2920, 2), (key2927, -2), (key3008, 2), (key3010, -2), (key3012, 2), (key3017, -2), (key3023, -2), (key3026, -2), (key3030, 4)]

def row6639 : Integer.Sparse Key := [(key2671, -1), (key2676, 1), (key2706, -1), (key2726, 2), (key2732, -1), (key2753, 1), (key2758, -1), (key2786, 1), (key2798, -1), (key2809, 1), (key2829, -1), (key2870, -1), (key2885, 1), (key2920, -1), (key2927, 1), (key3008, -1), (key3010, 1), (key3012, -1), (key3017, 1), (key3023, 1), (key3026, 1), (key3030, -2)]

def row6640 : Integer.Sparse Key := [(key2671, -1), (key2676, 1), (key2706, -1), (key2726, 2), (key2732, -1), (key2753, 1), (key2758, -1), (key2786, 1), (key2798, -1), (key2809, 1), (key2829, -1), (key2870, -1), (key2885, 1), (key2920, -1), (key2927, 1), (key3008, -1), (key3010, 1), (key3012, -1), (key3017, 1), (key3023, 1), (key3026, 1), (key3030, -2)]

def row6641 : Integer.Sparse Key := [(key2671, 2), (key2676, -2), (key2706, 2), (key2726, -4), (key2732, 2), (key2753, -2), (key2758, 2), (key2786, -2), (key2798, 2), (key2809, -2), (key2829, 2), (key2870, 2), (key2885, -2), (key2920, 2), (key2927, -2), (key3008, 2), (key3010, -2), (key3012, 2), (key3017, -2), (key3023, -2), (key3026, -2), (key3030, 4)]

def row6642 : Integer.Sparse Key := [(key2671, -1), (key2676, 1), (key2706, -1), (key2726, 2), (key2732, -1), (key2753, 1), (key2758, -1), (key2786, 1), (key2798, -1), (key2809, 1), (key2829, -1), (key2870, -1), (key2885, 1), (key2920, -1), (key2927, 1), (key3008, -1), (key3010, 1), (key3012, -1), (key3017, 1), (key3023, 1), (key3026, 1), (key3030, -2)]

def row6643 : Integer.Sparse Key := [(key2671, -1), (key2676, 1), (key2706, -1), (key2726, 2), (key2732, -1), (key2753, 1), (key2758, -1), (key2786, 1), (key2798, -1), (key2809, 1), (key2829, -1), (key2870, -1), (key2885, 1), (key2920, -1), (key2927, 1), (key3008, -1), (key3010, 1), (key3012, -1), (key3017, 1), (key3023, 1), (key3026, 1), (key3030, -2)]

def row6644 : Integer.Sparse Key := [(key2671, -1), (key2676, 1), (key2706, -1), (key2726, 2), (key2732, -1), (key2753, 1), (key2758, -1), (key2786, 1), (key2798, -1), (key2809, 1), (key2829, -1), (key2870, -1), (key2885, 1), (key2920, -1), (key2927, 1), (key3008, -1), (key3010, 1), (key3012, -1), (key3017, 1), (key3023, 1), (key3026, 1), (key3030, -2)]

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

def row6678 : Integer.Sparse Key := [(key2617, -2), (key2620, 2), (key2633, -2), (key2643, 2), (key2650, 2), (key2655, 2), (key2656, -4), (key2787, 2), (key2797, -2), (key2810, 2), (key2833, -2), (key2899, -2), (key2906, -2), (key2915, 4), (key2940, -2), (key2946, 2), (key2952, -2), (key2962, 2), (key2985, 2), (key2994, -2), (key2999, 2), (key3004, -2)]

def row6679 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, 1), (key2643, -1), (key2650, -1), (key2655, -1), (key2656, 2), (key2787, -1), (key2797, 1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, 1), (key2915, -2), (key2940, 1), (key2946, -1), (key2952, 1), (key2962, -1), (key2985, -1), (key2994, 1), (key2999, -1), (key3004, 1)]

def row6680 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, 1), (key2643, -1), (key2650, -1), (key2655, -1), (key2656, 2), (key2787, -1), (key2797, 1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, 1), (key2915, -2), (key2940, 1), (key2946, -1), (key2952, 1), (key2962, -1), (key2985, -1), (key2994, 1), (key2999, -1), (key3004, 1)]

def row6681 : Integer.Sparse Key := [(key2617, -2), (key2620, 2), (key2633, -2), (key2643, 4), (key2655, 2), (key2656, -4), (key2787, 2), (key2797, -2), (key2810, 2), (key2833, -2), (key2899, -2), (key2906, -2), (key2915, 4), (key2940, -2), (key2946, 2), (key2952, -2), (key2962, 2), (key2985, 2), (key2994, -2), (key2999, 2), (key3004, -2)]

def row6682 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, 1), (key2643, -2), (key2655, -1), (key2656, 2), (key2787, -1), (key2797, 1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, 1), (key2915, -2), (key2940, 1), (key2946, -1), (key2952, 1), (key2962, -1), (key2985, -1), (key2994, 1), (key2999, -1), (key3004, 1)]

def row6683 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, 1), (key2643, -2), (key2655, -1), (key2656, 2), (key2787, -1), (key2797, 1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, 1), (key2915, -2), (key2940, 1), (key2946, -1), (key2952, 1), (key2962, -1), (key2985, -1), (key2994, 1), (key2999, -1), (key3004, 1)]

def row6684 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, 1), (key2643, 2), (key2650, -4), (key2655, -1), (key2656, 2), (key2787, -1), (key2797, 1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, 1), (key2915, -2), (key2940, 1), (key2946, -1), (key2952, 1), (key2962, -1), (key2985, -1), (key2994, 1), (key2999, -1), (key3004, 1)]

def row6685 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, 1), (key2643, 2), (key2650, -4), (key2655, -1), (key2656, 2), (key2787, -1), (key2797, 1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, 1), (key2915, -2), (key2940, 1), (key2946, -1), (key2952, 1), (key2962, -1), (key2985, -1), (key2994, 1), (key2999, -1), (key3004, 1)]

def row6686 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, 1), (key2643, -3), (key2650, 1), (key2655, -1), (key2656, 2), (key2787, -1), (key2797, 1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, 1), (key2915, -2), (key2940, 1), (key2946, -1), (key2952, 1), (key2962, -1), (key2985, -1), (key2994, 1), (key2999, -1), (key3004, 1)]

def row6687 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, 1), (key2643, -3), (key2650, 1), (key2655, -1), (key2656, 2), (key2787, -1), (key2797, 1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, 1), (key2915, -2), (key2940, 1), (key2946, -1), (key2952, 1), (key2962, -1), (key2985, -1), (key2994, 1), (key2999, -1), (key3004, 1)]

def row6688 : Integer.Sparse Key := [(key2617, -2), (key2620, 2), (key2633, -2), (key2643, 2), (key2650, 2), (key2655, 2), (key2656, -4), (key2787, 2), (key2797, -2), (key2810, 2), (key2833, -2), (key2899, -2), (key2906, -2), (key2915, 4), (key2940, -2), (key2946, 2), (key2952, -2), (key2962, 2), (key2985, 2), (key2994, -2), (key2999, 2), (key3004, -2)]

def row6689 : Integer.Sparse Key := [(key2617, -2), (key2620, 2), (key2633, -2), (key2643, 2), (key2650, 2), (key2655, 2), (key2656, -4), (key2787, 2), (key2797, -2), (key2810, 2), (key2833, -2), (key2899, -2), (key2906, -2), (key2915, 4), (key2940, -2), (key2946, 2), (key2952, -2), (key2962, 2), (key2985, 2), (key2994, -2), (key2999, 2), (key3004, -2)]

def row6690 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2655, -2), (key2656, 2), (key2672, 2), (key2675, -2), (key2730, 2), (key2749, -2), (key2787, -2), (key2797, 2), (key2810, -2), (key2833, 4), (key2899, 2), (key2906, 2), (key2915, -6), (key2945, -2), (key2946, 2), (key2962, -2), (key2994, -2), (key3004, 4)]

def row6691 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2655, 1), (key2656, -1), (key2672, -1), (key2675, 1), (key2730, -1), (key2749, 1), (key2787, 1), (key2797, -1), (key2810, 1), (key2833, -2), (key2899, -1), (key2906, -1), (key2915, 3), (key2945, 1), (key2946, -1), (key2962, 1), (key2994, 1), (key3004, -2)]

def row6692 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2655, 1), (key2656, -1), (key2672, -1), (key2675, 1), (key2730, -1), (key2749, 1), (key2787, 1), (key2797, -1), (key2810, 1), (key2833, -2), (key2899, -1), (key2906, -1), (key2915, 3), (key2945, 1), (key2946, -1), (key2962, 1), (key2994, 1), (key3004, -2)]

def row6693 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2655, -2), (key2656, 2), (key2672, 2), (key2675, -2), (key2730, 2), (key2749, -4), (key2787, -2), (key2797, 2), (key2810, -2), (key2833, 4), (key2899, 2), (key2906, 2), (key2915, -6), (key2946, 2), (key2962, -2), (key2994, -2), (key3004, 4)]

def row6694 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2655, 1), (key2656, -1), (key2672, -1), (key2675, 1), (key2730, -1), (key2749, 2), (key2787, 1), (key2797, -1), (key2810, 1), (key2833, -2), (key2899, -1), (key2906, -1), (key2915, 3), (key2946, -1), (key2962, 1), (key2994, 1), (key3004, -2)]

def row6695 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2655, 1), (key2656, -1), (key2672, -1), (key2675, 1), (key2730, -1), (key2749, 2), (key2787, 1), (key2797, -1), (key2810, 1), (key2833, -2), (key2899, -1), (key2906, -1), (key2915, 3), (key2946, -1), (key2962, 1), (key2994, 1), (key3004, -2)]

def row6696 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2655, 1), (key2656, -1), (key2672, -1), (key2675, 1), (key2730, -1), (key2749, -2), (key2787, 1), (key2797, -1), (key2810, 1), (key2833, -2), (key2899, -1), (key2906, -1), (key2915, 3), (key2945, 4), (key2946, -1), (key2962, 1), (key2994, 1), (key3004, -2)]

def row6697 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2655, 1), (key2656, -1), (key2672, -1), (key2675, 1), (key2730, -1), (key2749, -2), (key2787, 1), (key2797, -1), (key2810, 1), (key2833, -2), (key2899, -1), (key2906, -1), (key2915, 3), (key2945, 4), (key2946, -1), (key2962, 1), (key2994, 1), (key3004, -2)]

def row6698 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2655, 1), (key2656, -1), (key2672, -1), (key2675, 1), (key2730, -1), (key2749, 3), (key2787, 1), (key2797, -1), (key2810, 1), (key2833, -2), (key2899, -1), (key2906, -1), (key2915, 3), (key2945, -1), (key2946, -1), (key2962, 1), (key2994, 1), (key3004, -2)]

def row6699 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2655, 1), (key2656, -1), (key2672, -1), (key2675, 1), (key2730, -1), (key2749, 3), (key2787, 1), (key2797, -1), (key2810, 1), (key2833, -2), (key2899, -1), (key2906, -1), (key2915, 3), (key2945, -1), (key2946, -1), (key2962, 1), (key2994, 1), (key3004, -2)]

def row6700 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2655, -2), (key2656, 2), (key2672, 2), (key2675, -2), (key2730, 2), (key2749, -2), (key2787, -2), (key2797, 2), (key2810, -2), (key2833, 4), (key2899, 2), (key2906, 2), (key2915, -6), (key2945, -2), (key2946, 2), (key2962, -2), (key2994, -2), (key3004, 4)]

def row6701 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2655, -2), (key2656, 2), (key2672, 2), (key2675, -2), (key2730, 2), (key2749, -2), (key2787, -2), (key2797, 2), (key2810, -2), (key2833, 4), (key2899, 2), (key2906, 2), (key2915, -6), (key2945, -2), (key2946, 2), (key2962, -2), (key2994, -2), (key3004, 4)]

def row6702 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2643, -1), (key2650, 1), (key2655, 1), (key2656, -1), (key2672, -1), (key2675, 1), (key2707, 1), (key2751, -1), (key2797, -1), (key2810, 1), (key2899, -1), (key2906, -1), (key2915, 2), (key2940, -1), (key2945, 2), (key2952, -2), (key2962, 1), (key2999, 1), (key3001, 1), (key3004, -2)]

def row6703 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2643, -1), (key2650, 1), (key2655, 1), (key2656, -1), (key2672, -1), (key2675, 1), (key2707, 1), (key2751, -1), (key2797, -1), (key2810, 1), (key2899, -1), (key2906, -1), (key2915, 2), (key2940, -1), (key2945, 2), (key2952, -2), (key2962, 1), (key2999, 1), (key3001, 1), (key3004, -2)]

def row6704 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, 1), (key2643, -1), (key2650, -1), (key2655, -1), (key2656, 2), (key2730, 1), (key2739, 1), (key2749, -1), (key2751, -1), (key2787, -1), (key2810, -1), (key2833, 2), (key2899, 1), (key2915, -1), (key2945, 1), (key2962, -1), (key2978, 1), (key2985, -1), (key2999, -2), (key3001, 1), (key3004, 1)]

def row6705 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, 1), (key2643, -1), (key2650, -1), (key2655, -1), (key2656, 2), (key2730, 1), (key2739, 1), (key2749, -1), (key2751, -1), (key2787, -1), (key2810, -1), (key2833, 2), (key2899, 1), (key2915, -1), (key2945, 1), (key2962, -1), (key2978, 1), (key2985, -1), (key2999, -2), (key3001, 1), (key3004, 1)]

def row6706 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2643, -1), (key2650, 1), (key2655, 1), (key2656, -1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, 1), (key2749, 1), (key2751, -1), (key2797, -1), (key2810, 1), (key2899, -1), (key2906, -1), (key2915, 2), (key2940, -2), (key2945, 1), (key2952, -2), (key2962, 1), (key2999, 1), (key3001, 1), (key3004, -2)]

def row6707 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2643, -1), (key2650, 1), (key2655, 1), (key2656, -1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, 1), (key2749, 1), (key2751, -1), (key2797, -1), (key2810, 1), (key2899, -1), (key2906, -1), (key2915, 2), (key2940, -2), (key2945, 1), (key2952, -2), (key2962, 1), (key2999, 1), (key3001, 1), (key3004, -2)]

def row6708 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, 1), (key2643, -2), (key2655, -1), (key2656, 2), (key2707, -1), (key2739, 2), (key2749, -1), (key2751, -1), (key2797, -1), (key2810, -1), (key2833, 1), (key2899, 1), (key2915, -1), (key2940, 1), (key2945, 1), (key2952, 1), (key2962, -1), (key2978, 1), (key2985, -1), (key2999, -2), (key3001, 1), (key3004, 1)]

def row6709 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, 1), (key2643, -2), (key2655, -1), (key2656, 2), (key2707, -1), (key2739, 2), (key2749, -1), (key2751, -1), (key2797, -1), (key2810, -1), (key2833, 1), (key2899, 1), (key2915, -1), (key2940, 1), (key2945, 1), (key2952, 1), (key2962, -1), (key2978, 1), (key2985, -1), (key2999, -2), (key3001, 1), (key3004, 1)]

def row6710 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, 1), (key2643, -2), (key2655, -1), (key2656, 2), (key2707, -1), (key2749, -1), (key2751, -1), (key2797, 1), (key2810, -1), (key2833, 1), (key2899, 1), (key2915, -1), (key2940, 1), (key2945, 1), (key2952, 1), (key2962, -1), (key2978, 1), (key2985, -1), (key2999, -2), (key3001, 1), (key3004, 1)]

def row6711 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, 1), (key2643, -2), (key2655, -1), (key2656, 2), (key2707, -1), (key2749, -1), (key2751, -1), (key2797, 1), (key2810, -1), (key2833, 1), (key2899, 1), (key2915, -1), (key2940, 1), (key2945, 1), (key2952, 1), (key2962, -1), (key2978, 1), (key2985, -1), (key2999, -2), (key3001, 1), (key3004, 1)]

def row6712 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2655, 1), (key2656, -1), (key2672, -1), (key2675, 1), (key2730, 1), (key2749, 1), (key2751, -1), (key2787, 1), (key2797, -1), (key2810, 1), (key2899, -1), (key2906, -1), (key2915, 2), (key2940, -2), (key2945, 1), (key2952, -2), (key2962, 1), (key2999, 1), (key3001, 1), (key3004, -2)]

def row6713 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2655, 1), (key2656, -1), (key2672, -1), (key2675, 1), (key2730, 1), (key2749, 1), (key2751, -1), (key2787, 1), (key2797, -1), (key2810, 1), (key2899, -1), (key2906, -1), (key2915, 2), (key2940, -2), (key2945, 1), (key2952, -2), (key2962, 1), (key2999, 1), (key3001, 1), (key3004, -2)]

def row6714 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, 1), (key2643, -1), (key2650, -1), (key2655, -1), (key2656, 2), (key2730, 1), (key2739, 1), (key2751, -1), (key2787, -1), (key2810, -1), (key2833, 1), (key2899, 1), (key2915, -1), (key2952, 1), (key2962, -1), (key2978, 1), (key2985, -1), (key2999, -2), (key3001, 1), (key3004, 1)]

def row6715 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, 1), (key2643, -1), (key2650, -1), (key2655, -1), (key2656, 2), (key2730, 1), (key2739, 1), (key2751, -1), (key2787, -1), (key2810, -1), (key2833, 1), (key2899, 1), (key2915, -1), (key2952, 1), (key2962, -1), (key2978, 1), (key2985, -1), (key2999, -2), (key3001, 1), (key3004, 1)]

def row6716 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2655, 1), (key2656, -1), (key2672, -1), (key2675, 1), (key2749, 1), (key2751, -1), (key2787, 1), (key2797, -1), (key2810, 1), (key2833, -1), (key2899, -1), (key2906, -1), (key2915, 2), (key2940, -1), (key2945, 1), (key2952, -1), (key2962, 1), (key2999, 1), (key3001, 1), (key3004, -2)]

def row6717 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2655, 1), (key2656, -1), (key2672, -1), (key2675, 1), (key2749, 1), (key2751, -1), (key2787, 1), (key2797, -1), (key2810, 1), (key2833, -1), (key2899, -1), (key2906, -1), (key2915, 2), (key2940, -1), (key2945, 1), (key2952, -1), (key2962, 1), (key2999, 1), (key3001, 1), (key3004, -2)]

def row6718 : Integer.Sparse Key := [(key2066, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2155, 1), (key2168, -1), (key2195, -1), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

def row6719 : Integer.Sparse Key := [(key2066, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2155, 1), (key2168, -1), (key2195, -1), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

def row6720 : Integer.Sparse Key := [(key2066, 2), (key2071, -2), (key2093, -2), (key2096, 2), (key2155, -2), (key2168, 2), (key2195, 2), (key2201, -2), (key2248, 2), (key2255, -2), (key2306, -2), (key2311, 2)]

def row6721 : Integer.Sparse Key := [(key2066, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2155, 1), (key2168, -1), (key2195, -1), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

def row6722 : Integer.Sparse Key := [(key2066, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2155, 1), (key2168, -1), (key2195, -1), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

def row6723 : Integer.Sparse Key := [(key2066, 2), (key2071, -2), (key2093, -2), (key2096, 2), (key2155, -2), (key2168, 2), (key2195, 2), (key2201, -2), (key2248, 2), (key2255, -2), (key2306, -2), (key2311, 2)]

def row6724 : Integer.Sparse Key := [(key2066, 2), (key2071, -2), (key2093, -2), (key2096, 2), (key2155, -2), (key2168, 2), (key2195, 2), (key2201, -2), (key2248, 2), (key2255, -2), (key2306, -2), (key2311, 2)]

def row6725 : Integer.Sparse Key := [(key2066, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2155, 1), (key2168, -1), (key2195, -1), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

def row6726 : Integer.Sparse Key := [(key2066, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2155, 1), (key2168, -1), (key2195, -1), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

def row6727 : Integer.Sparse Key := [(key2066, 2), (key2071, -2), (key2093, -2), (key2096, 2), (key2155, -2), (key2168, 2), (key2195, 2), (key2201, -2), (key2248, 2), (key2255, -2), (key2306, -2), (key2311, 2)]

def row6728 : Integer.Sparse Key := [(key2066, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2155, 1), (key2168, -1), (key2195, -1), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

def row6729 : Integer.Sparse Key := [(key2066, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2155, 1), (key2168, -1), (key2195, -1), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

def row6730 : Integer.Sparse Key := [(key2066, 2), (key2071, -2), (key2093, -2), (key2096, 2), (key2155, -2), (key2168, 2), (key2195, 2), (key2201, -2), (key2248, 2), (key2255, -2), (key2306, -2), (key2311, 2)]

def row6731 : Integer.Sparse Key := [(key2066, 2), (key2071, -2), (key2093, -2), (key2096, 2), (key2155, -2), (key2168, 2), (key2195, 2), (key2201, -2), (key2248, 2), (key2255, -2), (key2306, -2), (key2311, 2)]

def row6732 : Integer.Sparse Key := [(key2066, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2155, 1), (key2168, -1), (key2195, -1), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

def row6733 : Integer.Sparse Key := [(key2066, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2155, 1), (key2168, -1), (key2195, -1), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

def row6734 : Integer.Sparse Key := [(key2066, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2155, 1), (key2168, -1), (key2195, -1), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

def row6735 : Integer.Sparse Key := [(key2066, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2155, 1), (key2168, -1), (key2195, -1), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

def row6736 : Integer.Sparse Key := [(key2066, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2155, 1), (key2168, -1), (key2195, -1), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

def row6737 : Integer.Sparse Key := [(key2066, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2155, 1), (key2168, -1), (key2195, -1), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

def row6738 : Integer.Sparse Key := [(key2066, 2), (key2071, -2), (key2093, -2), (key2096, 2), (key2155, -2), (key2168, 2), (key2195, 2), (key2201, -2), (key2248, 2), (key2255, -2), (key2306, -2), (key2311, 2)]

def row6739 : Integer.Sparse Key := [(key2066, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2155, 1), (key2168, -1), (key2195, -1), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

def row6740 : Integer.Sparse Key := [(key2066, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2155, 1), (key2168, -1), (key2195, -1), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

def row6741 : Integer.Sparse Key := [(key2066, 2), (key2071, -2), (key2093, -2), (key2096, 2), (key2155, -2), (key2168, 2), (key2195, 2), (key2201, -2), (key2248, 2), (key2255, -2), (key2306, -2), (key2311, 2)]

def row6742 : Integer.Sparse Key := [(key2066, -4), (key2071, 4), (key2093, 4), (key2096, -4), (key2155, 4), (key2168, -4), (key2195, -4), (key2201, 4), (key2248, -4), (key2255, 4), (key2306, 4), (key2311, -4)]

def row6743 : Integer.Sparse Key := [(key2066, 2), (key2071, -2), (key2093, -2), (key2096, 2), (key2155, -2), (key2168, 2), (key2195, 2), (key2201, -2), (key2248, 2), (key2255, -2), (key2306, -2), (key2311, 2)]

def row6744 : Integer.Sparse Key := [(key2066, 2), (key2071, -2), (key2093, -2), (key2096, 2), (key2155, -2), (key2168, 2), (key2195, 2), (key2201, -2), (key2248, 2), (key2255, -2), (key2306, -2), (key2311, 2)]

def row6745 : Integer.Sparse Key := [(key2066, 2), (key2071, -2), (key2093, -2), (key2096, 2), (key2155, -2), (key2168, 2), (key2195, 2), (key2201, -2), (key2248, 2), (key2255, -2), (key2306, -2), (key2311, 2)]

def row6746 : Integer.Sparse Key := [(key2066, 2), (key2071, -2), (key2093, -2), (key2096, 2), (key2155, -2), (key2168, 2), (key2195, 2), (key2201, -2), (key2248, 2), (key2255, -2), (key2306, -2), (key2311, 2)]

def row6747 : Integer.Sparse Key := [(key2066, -4), (key2071, 4), (key2093, 4), (key2096, -4), (key2155, 4), (key2168, -4), (key2195, -4), (key2201, 4), (key2248, -4), (key2255, 4), (key2306, 4), (key2311, -4)]

def row6748 : Integer.Sparse Key := [(key324, 1), (key325, -2), (key329, 1), (key339, 1), (key341, -1), (key728, -1), (key730, 1), (key796, 1), (key815, -1), (key832, -1), (key841, 1), (key870, -1), (key880, 1), (key929, 1), (key936, -1)]

def row6749 : Integer.Sparse Key := [(key324, 1), (key325, -2), (key329, 1), (key339, 1), (key341, -1), (key728, -1), (key730, 1), (key796, 1), (key815, -1), (key832, -1), (key841, 1), (key870, -1), (key880, 1), (key929, 1), (key936, -1)]

def row6750 : Integer.Sparse Key := [(key324, -2), (key325, 4), (key329, -2), (key339, -2), (key341, 2), (key728, 2), (key730, -2), (key796, -2), (key815, 2), (key832, 2), (key841, -2), (key870, 2), (key880, -2), (key929, -2), (key936, 2)]

def row6751 : Integer.Sparse Key := [(key313, 2), (key324, 1), (key325, -2), (key329, 1), (key339, 1), (key341, -1), (key414, 1), (key415, 1), (key419, -2), (key727, -2), (key728, -1), (key730, 1), (key794, -1), (key815, -1), (key832, 1), (key841, 1), (key870, -1), (key880, 1), (key929, 1), (key936, -1)]

def row6752 : Integer.Sparse Key := [(key313, 2), (key324, 1), (key325, -2), (key329, 1), (key339, 1), (key341, -1), (key414, 1), (key415, 1), (key419, -2), (key727, -2), (key728, -1), (key730, 1), (key794, -1), (key815, -1), (key832, 1), (key841, 1), (key870, -1), (key880, 1), (key929, 1), (key936, -1)]

def row6753 : Integer.Sparse Key := [(key313, -2), (key324, -2), (key325, 4), (key329, -2), (key339, -2), (key341, 2), (key414, 2), (key415, -2), (key419, 2), (key727, 2), (key728, 2), (key730, -2), (key794, -2), (key815, 2), (key841, -2), (key870, 2), (key880, -2), (key929, -2), (key936, 2)]

def row6754 : Integer.Sparse Key := [(key312, 2), (key313, -2), (key324, -2), (key325, 4), (key329, -2), (key339, -2), (key341, 2), (key414, 2), (key415, -2), (key419, 2), (key584, -2), (key725, -2), (key727, 2), (key728, 2), (key730, -2), (key794, -2), (key815, 2), (key870, 2), (key880, -2), (key929, -2), (key936, 2)]

def row6755 : Integer.Sparse Key := [(key312, -1), (key313, -1), (key324, 1), (key325, -2), (key329, 1), (key339, 1), (key341, -1), (key414, -2), (key415, 1), (key419, -1), (key582, 1), (key584, 1), (key725, 1), (key727, 1), (key728, -1), (key730, 1), (key794, 2), (key815, -2), (key870, -1), (key880, 1), (key929, 1), (key936, -1)]

def row6756 : Integer.Sparse Key := [(key312, -1), (key313, -1), (key324, 1), (key325, -2), (key329, 1), (key339, 1), (key341, -1), (key414, -2), (key415, 1), (key419, -1), (key582, 1), (key584, 1), (key725, 1), (key727, 1), (key728, -1), (key730, 1), (key794, 2), (key815, -2), (key870, -1), (key880, 1), (key929, 1), (key936, -1)]

def row6757 : Integer.Sparse Key := [(key312, 2), (key324, -2), (key325, 4), (key329, -2), (key339, -2), (key341, 2), (key415, -4), (key419, 2), (key582, 2), (key584, -2), (key725, -2), (key728, 2), (key730, -2), (key796, 2), (key870, 2), (key880, -2), (key929, -2), (key936, 2)]

def row6758 : Integer.Sparse Key := [(key312, -1), (key324, 1), (key325, -2), (key329, 1), (key339, 1), (key341, -1), (key415, 2), (key419, -1), (key582, -1), (key584, 1), (key725, 1), (key728, -1), (key730, 1), (key796, -1), (key870, -1), (key880, 1), (key929, 1), (key936, -1)]

def row6759 : Integer.Sparse Key := [(key312, -1), (key324, 1), (key325, -2), (key329, 1), (key339, 1), (key341, -1), (key415, 2), (key419, -1), (key582, -1), (key584, 1), (key725, 1), (key728, -1), (key730, 1), (key796, -1), (key870, -1), (key880, 1), (key929, 1), (key936, -1)]

def row6760 : Integer.Sparse Key := [(key324, 1), (key325, 2), (key329, -3), (key339, -1), (key341, 1), (key414, -2), (key415, -2), (key419, 4), (key474, 2), (key476, -2), (key600, -2), (key602, 2), (key728, -1), (key736, -1), (key748, 1), (key752, 1), (key794, 2), (key815, 2), (key832, -2), (key841, -2)]

def row6761 : Integer.Sparse Key := [(key324, 1), (key325, 2), (key329, -3), (key339, -1), (key341, 1), (key414, -2), (key415, -2), (key419, 4), (key474, 2), (key476, -2), (key600, -2), (key602, 2), (key728, -1), (key736, -1), (key748, 1), (key752, 1), (key794, 2), (key815, 2), (key832, -2), (key841, -2)]

def row6762 : Integer.Sparse Key := [(key313, 1), (key324, -1), (key325, -1), (key329, 2), (key339, 1), (key341, -1), (key414, 1), (key415, 1), (key419, -2), (key474, -1), (key476, 1), (key600, 1), (key602, -1), (key727, -1), (key728, 1), (key748, -1), (key794, -1), (key815, -1), (key832, 1), (key841, 1)]

def row6763 : Integer.Sparse Key := [(key312, -1), (key313, 1), (key324, -1), (key325, -1), (key329, 2), (key339, 1), (key341, -1), (key414, 1), (key415, 1), (key419, -2), (key474, -1), (key476, 1), (key584, 1), (key600, 1), (key602, -1), (key725, 1), (key727, -1), (key728, 1), (key748, -1), (key794, -1), (key815, -1), (key832, 1)]

def row6764 : Integer.Sparse Key := [(key312, 1), (key325, -1), (key329, 1), (key414, 1), (key415, 1), (key419, -1), (key474, -1), (key476, 1), (key600, 1), (key602, -1), (key725, -1), (key736, 1), (key752, -1), (key794, -1), (key815, -1), (key841, 1)]

def row6765 : Integer.Sparse Key := [(key312, 1), (key325, -1), (key329, 1), (key414, 1), (key415, 1), (key419, -1), (key474, -1), (key476, 1), (key600, 1), (key602, -1), (key725, -1), (key736, 1), (key752, -1), (key794, -1), (key815, -1), (key841, 1)]

def row6766 : Integer.Sparse Key := [(key325, -1), (key329, 1), (key341, -1), (key415, 1), (key419, -1), (key474, -1), (key476, 1), (key600, 1), (key602, -1), (key736, 1), (key815, -1), (key841, 1)]

def row6767 : Integer.Sparse Key := [(key312, -1), (key325, -1), (key329, 1), (key341, -1), (key415, 1), (key419, -1), (key474, -1), (key476, 1), (key584, 1), (key600, 1), (key602, -1), (key725, 1), (key736, 1), (key815, -1)]

def row6768 : Integer.Sparse Key := [(key325, 2), (key329, -2), (key341, 2), (key415, -2), (key419, 2), (key474, 2), (key476, -2), (key584, -2), (key600, -2), (key602, 2), (key736, -2), (key815, 2)]

def row6769 : Integer.Sparse Key := [(key324, -1), (key325, -1), (key329, 1), (key339, 1), (key341, -1), (key414, 1), (key415, 1), (key419, -1), (key474, -1), (key476, 1), (key582, -1), (key584, 1), (key600, 1), (key602, -1), (key728, 1), (key794, -1)]

def row6770 : Integer.Sparse Key := [(key324, -1), (key325, -1), (key329, 1), (key339, 1), (key341, -1), (key414, 1), (key415, 1), (key419, -1), (key474, -1), (key476, 1), (key582, -1), (key584, 1), (key600, 1), (key602, -1), (key728, 1), (key794, -1)]

def row6771 : Integer.Sparse Key := [(key324, 2), (key325, 2), (key329, -2), (key339, -2), (key341, 2), (key414, -2), (key415, -2), (key419, 2), (key474, 2), (key476, -2), (key582, 2), (key584, -2), (key600, -2), (key602, 2), (key728, -2), (key794, 2)]

def row6772 : Integer.Sparse Key := [(key325, -4), (key329, 4), (key339, 4), (key341, -4), (key415, 4), (key419, -4), (key474, -4), (key476, 4), (key582, -4), (key584, 4), (key600, 4), (key602, -4)]

def row6773 : Integer.Sparse Key := [(key325, 2), (key329, -2), (key339, -2), (key341, 2), (key415, -2), (key419, 2), (key474, 2), (key476, -2), (key582, 2), (key584, -2), (key600, -2), (key602, 2)]

def row6774 : Integer.Sparse Key := [(key325, 2), (key329, -2), (key339, -2), (key341, 2), (key415, -2), (key419, 2), (key474, 2), (key476, -2), (key582, 2), (key584, -2), (key600, -2), (key602, 2)]

def row6775 : Integer.Sparse Key := [(key325, 2), (key329, -2), (key339, -2), (key341, 2), (key415, -2), (key419, 2), (key474, 2), (key476, -2), (key582, 2), (key584, -2), (key600, -2), (key602, 2)]

def row6776 : Integer.Sparse Key := [(key325, 2), (key329, -2), (key339, -2), (key341, 2), (key415, -2), (key419, 2), (key474, 2), (key476, -2), (key582, 2), (key584, -2), (key600, -2), (key602, 2)]

def row6777 : Integer.Sparse Key := [(key325, -4), (key329, 4), (key339, 4), (key341, -4), (key415, 4), (key419, -4), (key474, -4), (key476, 4), (key582, -4), (key584, 4), (key600, 4), (key602, -4)]

def row6778 : Integer.Sparse Key := [(key2064, -1), (key2070, 1), (key2080, 1), (key2086, -1), (key2153, 1), (key2167, -1), (key2177, -1), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

def row6779 : Integer.Sparse Key := [(key2064, -1), (key2070, 1), (key2080, 1), (key2086, -1), (key2153, 1), (key2167, -1), (key2177, -1), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

def row6780 : Integer.Sparse Key := [(key2064, 2), (key2070, -2), (key2080, -2), (key2086, 2), (key2153, -2), (key2167, 2), (key2177, 2), (key2188, -2), (key2247, 2), (key2254, -2), (key2280, -2), (key2288, 2)]

def row6781 : Integer.Sparse Key := [(key2064, -1), (key2070, 1), (key2080, 1), (key2086, -1), (key2153, 1), (key2167, -1), (key2177, -1), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

def row6782 : Integer.Sparse Key := [(key2064, -1), (key2070, 1), (key2080, 1), (key2086, -1), (key2153, 1), (key2167, -1), (key2177, -1), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

def row6783 : Integer.Sparse Key := [(key2064, 2), (key2070, -2), (key2080, -2), (key2086, 2), (key2153, -2), (key2167, 2), (key2177, 2), (key2188, -2), (key2247, 2), (key2254, -2), (key2280, -2), (key2288, 2)]

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

def row6784 : Integer.Sparse Key := [(key2064, 2), (key2070, -2), (key2080, -2), (key2086, 2), (key2153, -2), (key2167, 2), (key2177, 2), (key2188, -2), (key2247, 2), (key2254, -2), (key2280, -2), (key2288, 2)]

def row6785 : Integer.Sparse Key := [(key2064, -1), (key2070, 1), (key2080, 1), (key2086, -1), (key2153, 1), (key2167, -1), (key2177, -1), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

def row6786 : Integer.Sparse Key := [(key2064, -1), (key2070, 1), (key2080, 1), (key2086, -1), (key2153, 1), (key2167, -1), (key2177, -1), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

def row6787 : Integer.Sparse Key := [(key2064, 2), (key2070, -2), (key2080, -2), (key2086, 2), (key2153, -2), (key2167, 2), (key2177, 2), (key2188, -2), (key2247, 2), (key2254, -2), (key2280, -2), (key2288, 2)]

def row6788 : Integer.Sparse Key := [(key2064, -1), (key2070, 1), (key2080, 1), (key2086, -1), (key2153, 1), (key2167, -1), (key2177, -1), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

def row6789 : Integer.Sparse Key := [(key2064, -1), (key2070, 1), (key2080, 1), (key2086, -1), (key2153, 1), (key2167, -1), (key2177, -1), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

def row6790 : Integer.Sparse Key := [(key2064, 2), (key2070, -2), (key2080, -2), (key2086, 2), (key2153, -2), (key2167, 2), (key2177, 2), (key2188, -2), (key2247, 2), (key2254, -2), (key2280, -2), (key2288, 2)]

def row6791 : Integer.Sparse Key := [(key2064, 2), (key2070, -2), (key2080, -2), (key2086, 2), (key2153, -2), (key2167, 2), (key2177, 2), (key2188, -2), (key2247, 2), (key2254, -2), (key2280, -2), (key2288, 2)]

def row6792 : Integer.Sparse Key := [(key2064, -1), (key2070, 1), (key2080, 1), (key2086, -1), (key2153, 1), (key2167, -1), (key2177, -1), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

def row6793 : Integer.Sparse Key := [(key2064, -1), (key2070, 1), (key2080, 1), (key2086, -1), (key2153, 1), (key2167, -1), (key2177, -1), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

def row6794 : Integer.Sparse Key := [(key2064, -1), (key2070, 1), (key2080, 1), (key2086, -1), (key2153, 1), (key2167, -1), (key2177, -1), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

def row6795 : Integer.Sparse Key := [(key2064, -1), (key2070, 1), (key2080, 1), (key2086, -1), (key2153, 1), (key2167, -1), (key2177, -1), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

def row6796 : Integer.Sparse Key := [(key2064, -1), (key2070, 1), (key2080, 1), (key2086, -1), (key2153, 1), (key2167, -1), (key2177, -1), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

def row6797 : Integer.Sparse Key := [(key2064, -1), (key2070, 1), (key2080, 1), (key2086, -1), (key2153, 1), (key2167, -1), (key2177, -1), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

def row6798 : Integer.Sparse Key := [(key2064, 2), (key2070, -2), (key2080, -2), (key2086, 2), (key2153, -2), (key2167, 2), (key2177, 2), (key2188, -2), (key2247, 2), (key2254, -2), (key2280, -2), (key2288, 2)]

def row6799 : Integer.Sparse Key := [(key2064, -1), (key2070, 1), (key2080, 1), (key2086, -1), (key2153, 1), (key2167, -1), (key2177, -1), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

def row6800 : Integer.Sparse Key := [(key2064, -1), (key2070, 1), (key2080, 1), (key2086, -1), (key2153, 1), (key2167, -1), (key2177, -1), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

def row6801 : Integer.Sparse Key := [(key2064, 2), (key2070, -2), (key2080, -2), (key2086, 2), (key2153, -2), (key2167, 2), (key2177, 2), (key2188, -2), (key2247, 2), (key2254, -2), (key2280, -2), (key2288, 2)]

def row6802 : Integer.Sparse Key := [(key2064, -4), (key2070, 4), (key2080, 4), (key2086, -4), (key2153, 4), (key2167, -4), (key2177, -4), (key2188, 4), (key2247, -4), (key2254, 4), (key2280, 4), (key2288, -4)]

def row6803 : Integer.Sparse Key := [(key2064, 2), (key2070, -2), (key2080, -2), (key2086, 2), (key2153, -2), (key2167, 2), (key2177, 2), (key2188, -2), (key2247, 2), (key2254, -2), (key2280, -2), (key2288, 2)]

def row6804 : Integer.Sparse Key := [(key2064, 2), (key2070, -2), (key2080, -2), (key2086, 2), (key2153, -2), (key2167, 2), (key2177, 2), (key2188, -2), (key2247, 2), (key2254, -2), (key2280, -2), (key2288, 2)]

def row6805 : Integer.Sparse Key := [(key2064, 2), (key2070, -2), (key2080, -2), (key2086, 2), (key2153, -2), (key2167, 2), (key2177, 2), (key2188, -2), (key2247, 2), (key2254, -2), (key2280, -2), (key2288, 2)]

def row6806 : Integer.Sparse Key := [(key2064, 2), (key2070, -2), (key2080, -2), (key2086, 2), (key2153, -2), (key2167, 2), (key2177, 2), (key2188, -2), (key2247, 2), (key2254, -2), (key2280, -2), (key2288, 2)]

def row6807 : Integer.Sparse Key := [(key2064, -4), (key2070, 4), (key2080, 4), (key2086, -4), (key2153, 4), (key2167, -4), (key2177, -4), (key2188, 4), (key2247, -4), (key2254, 4), (key2280, 4), (key2288, -4)]

def row6808 : Integer.Sparse Key := [(key66, -2), (key67, 2), (key78, 2), (key80, -2), (key708, 1), (key711, -1), (key717, -1), (key719, 1), (key862, 1), (key887, -1), (key894, -1), (key896, -1), (key917, 2), (key949, 1), (key956, -1)]

def row6809 : Integer.Sparse Key := [(key66, -2), (key67, 2), (key78, 2), (key80, -2), (key708, 1), (key711, -1), (key717, -1), (key719, 1), (key862, 1), (key887, -1), (key894, -1), (key896, -1), (key917, 2), (key949, 1), (key956, -1)]

def row6810 : Integer.Sparse Key := [(key66, 4), (key67, -4), (key78, -4), (key80, 4), (key708, -2), (key711, 2), (key717, 2), (key719, -2), (key862, -2), (key887, 2), (key894, 2), (key896, 2), (key917, -4), (key949, -2), (key956, 2)]

def row6811 : Integer.Sparse Key := [(key66, -2), (key67, 2), (key78, 2), (key80, -2), (key708, 1), (key711, -1), (key717, -1), (key719, 1), (key862, 1), (key887, -1), (key894, -1), (key896, -1), (key917, 2), (key949, 1), (key956, -1)]

def row6812 : Integer.Sparse Key := [(key66, -2), (key67, 2), (key78, 2), (key80, -2), (key708, 1), (key711, -1), (key717, -1), (key719, 1), (key862, 1), (key887, -1), (key894, -1), (key896, -1), (key917, 2), (key949, 1), (key956, -1)]

def row6813 : Integer.Sparse Key := [(key66, 4), (key67, -4), (key78, -4), (key80, 4), (key708, -2), (key711, 2), (key717, 2), (key719, -2), (key862, -2), (key887, 2), (key894, 2), (key896, 2), (key917, -4), (key949, -2), (key956, 2)]

def row6814 : Integer.Sparse Key := [(key66, 4), (key67, -4), (key78, -4), (key80, 4), (key708, -2), (key711, 2), (key717, 2), (key719, -2), (key862, -2), (key887, 2), (key894, 2), (key896, 2), (key917, -4), (key949, -2), (key956, 2)]

def row6815 : Integer.Sparse Key := [(key66, -2), (key67, 2), (key78, 2), (key80, -2), (key708, 1), (key711, -1), (key717, -1), (key719, 1), (key862, 1), (key887, -1), (key894, -1), (key896, -1), (key917, 2), (key949, 1), (key956, -1)]

def row6816 : Integer.Sparse Key := [(key66, -2), (key67, 2), (key78, 2), (key80, -2), (key708, 1), (key711, -1), (key717, -1), (key719, 1), (key862, 1), (key887, -1), (key894, -1), (key896, -1), (key917, 2), (key949, 1), (key956, -1)]

def row6817 : Integer.Sparse Key := [(key66, 4), (key67, -4), (key78, -4), (key80, 4), (key708, -2), (key711, 2), (key717, 2), (key719, -2), (key862, -2), (key887, 2), (key894, 2), (key896, 2), (key917, -4), (key949, -2), (key956, 2)]

def row6818 : Integer.Sparse Key := [(key66, -2), (key67, 2), (key78, 2), (key80, -2), (key708, 1), (key711, -1), (key717, -1), (key719, 1), (key862, 1), (key887, -1), (key894, -1), (key896, -1), (key917, 2), (key949, 1), (key956, -1)]

def row6819 : Integer.Sparse Key := [(key66, -2), (key67, 2), (key78, 2), (key80, -2), (key708, 1), (key711, -1), (key717, -1), (key719, 1), (key862, 1), (key887, -1), (key894, -1), (key896, -1), (key917, 2), (key949, 1), (key956, -1)]

def row6820 : Integer.Sparse Key := [(key66, 2), (key78, -1), (key80, -1), (key131, -4), (key141, 4), (key143, 4), (key160, -4), (key711, -2), (key717, -1), (key719, 3), (key862, 2), (key887, 2), (key894, -2), (key896, -2), (key917, -4), (key949, 2), (key956, 2)]

def row6821 : Integer.Sparse Key := [(key66, 2), (key78, -1), (key80, -1), (key131, -4), (key141, 4), (key143, 4), (key160, -4), (key711, -2), (key717, -1), (key719, 3), (key862, 2), (key887, 2), (key894, -2), (key896, -2), (key917, -4), (key949, 2), (key956, 2)]

def row6822 : Integer.Sparse Key := [(key66, -1), (key78, 2), (key80, -1), (key131, 2), (key141, -2), (key143, -2), (key160, 2), (key711, 1), (key717, -1), (key862, -1), (key887, -1), (key894, 1), (key896, 1), (key917, 2), (key949, -1), (key956, -1)]

def row6823 : Integer.Sparse Key := [(key66, -1), (key78, 2), (key80, -1), (key131, 2), (key141, -2), (key143, -2), (key160, 2), (key711, 1), (key717, -1), (key862, -1), (key887, -1), (key894, 1), (key896, 1), (key917, 2), (key949, -1), (key956, -1)]

def row6824 : Integer.Sparse Key := [(key66, -1), (key78, -1), (key80, 2), (key131, 2), (key141, -2), (key143, -2), (key160, 2), (key711, 1), (key717, 2), (key719, -3), (key862, -1), (key887, -1), (key894, 1), (key896, 1), (key917, 2), (key949, -1), (key956, -1)]

def row6825 : Integer.Sparse Key := [(key66, -1), (key78, -1), (key80, 2), (key131, 2), (key141, -2), (key143, -2), (key160, 2), (key711, 1), (key717, 2), (key719, -3), (key862, -1), (key887, -1), (key894, 1), (key896, 1), (key917, 2), (key949, -1), (key956, -1)]

def row6826 : Integer.Sparse Key := [(key78, 2), (key131, 2), (key141, -1), (key143, -2), (key160, 1), (key708, -1), (key711, 1), (key717, -1), (key719, -1), (key862, -1), (key887, -1), (key896, 1), (key917, 2), (key956, -1)]

def row6827 : Integer.Sparse Key := [(key78, 2), (key131, 2), (key141, -1), (key143, -2), (key160, 1), (key708, -1), (key711, 1), (key717, -1), (key719, -1), (key862, -1), (key887, -1), (key896, 1), (key917, 2), (key956, -1)]

def row6828 : Integer.Sparse Key := [(key78, -1), (key131, -4), (key141, 2), (key143, 4), (key160, -2), (key191, 2), (key708, 2), (key711, -2), (key717, -1), (key719, 2), (key862, 2), (key887, 2), (key896, -2), (key917, -4)]

def row6829 : Integer.Sparse Key := [(key66, -1), (key78, -1), (key80, 1), (key131, 2), (key141, -2), (key143, -2), (key160, 1), (key183, 1), (key191, -1), (key711, 1), (key717, 2), (key719, -2), (key862, -1), (key887, -1), (key894, 1), (key896, 1), (key917, 1)]

def row6830 : Integer.Sparse Key := [(key66, -1), (key78, -1), (key80, 1), (key131, 2), (key141, -2), (key143, -2), (key160, 1), (key183, 1), (key191, -1), (key711, 1), (key717, 2), (key719, -2), (key862, -1), (key887, -1), (key894, 1), (key896, 1), (key917, 1)]

def row6831 : Integer.Sparse Key := [(key78, -1), (key80, -2), (key131, -4), (key141, 2), (key143, 4), (key160, -2), (key183, -2), (key191, 2), (key708, 2), (key711, -2), (key717, -1), (key719, 4), (key862, 2), (key887, 2), (key896, -2), (key917, -2)]

def row6832 : Integer.Sparse Key := [(key66, -2), (key67, 4), (key78, 2), (key80, -4), (key143, -4), (key160, 4), (key178, -4), (key183, 8), (key191, -4), (key708, -2), (key717, 2), (key862, 4), (key894, -4)]

def row6833 : Integer.Sparse Key := [(key66, 1), (key67, -2), (key78, -1), (key80, 2), (key143, 2), (key160, -2), (key178, 2), (key183, -4), (key191, 2), (key708, 1), (key717, -1), (key862, -2), (key894, 2)]

def row6834 : Integer.Sparse Key := [(key66, 1), (key67, -2), (key78, -1), (key80, 2), (key143, 2), (key160, -2), (key178, 2), (key183, -4), (key191, 2), (key708, 1), (key717, -1), (key862, -2), (key894, 2)]

def row6835 : Integer.Sparse Key := [(key66, -1), (key67, -2), (key78, -1), (key80, 2), (key131, -1), (key141, 1), (key143, 2), (key160, -2), (key178, 2), (key183, -4), (key191, 2), (key708, 3), (key717, -1), (key862, -1), (key894, 1)]

def row6836 : Integer.Sparse Key := [(key66, -1), (key67, -2), (key78, -1), (key80, 2), (key131, -1), (key141, 1), (key143, 2), (key160, -2), (key178, 2), (key183, -4), (key191, 2), (key708, 3), (key717, -1), (key862, -1), (key894, 1)]

def row6837 : Integer.Sparse Key := [(key67, 4), (key78, 2), (key80, -4), (key131, 2), (key141, -4), (key143, -4), (key160, 4), (key178, -4), (key183, 8), (key191, -4), (key708, -4), (key717, 2), (key862, 2)]

def row6838 : Integer.Sparse Key := [(key1992, -1), (key1995, 1), (key2002, 1), (key2004, -1), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, -1), (key2295, 2), (key2325, 1), (key2337, -1)]

def row6839 : Integer.Sparse Key := [(key1992, -1), (key1995, 1), (key2002, 1), (key2004, -1), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, -1), (key2295, 2), (key2325, 1), (key2337, -1)]

def row6840 : Integer.Sparse Key := [(key1992, 2), (key1995, -2), (key2002, -2), (key2004, 2), (key2237, -2), (key2260, 2), (key2271, 2), (key2273, 2), (key2295, -4), (key2325, -2), (key2337, 2)]

def row6841 : Integer.Sparse Key := [(key1992, -1), (key1995, 1), (key2002, 1), (key2004, -1), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, -1), (key2295, 2), (key2325, 1), (key2337, -1)]

def row6842 : Integer.Sparse Key := [(key1992, -1), (key1995, 1), (key2002, 1), (key2004, -1), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, -1), (key2295, 2), (key2325, 1), (key2337, -1)]

def row6843 : Integer.Sparse Key := [(key1992, 2), (key1995, -2), (key2002, -2), (key2004, 2), (key2237, -2), (key2260, 2), (key2271, 2), (key2273, 2), (key2295, -4), (key2325, -2), (key2337, 2)]

def row6844 : Integer.Sparse Key := [(key1992, 2), (key1995, -2), (key2002, -2), (key2004, 2), (key2237, -2), (key2260, 2), (key2271, 2), (key2273, 2), (key2295, -4), (key2325, -2), (key2337, 2)]

def row6845 : Integer.Sparse Key := [(key1992, -1), (key1995, 1), (key2002, 1), (key2004, -1), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, -1), (key2295, 2), (key2325, 1), (key2337, -1)]

def row6846 : Integer.Sparse Key := [(key1992, -1), (key1995, 1), (key2002, 1), (key2004, -1), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, -1), (key2295, 2), (key2325, 1), (key2337, -1)]

def row6847 : Integer.Sparse Key := [(key1992, 2), (key1995, -2), (key2002, -2), (key2004, 2), (key2237, -2), (key2260, 2), (key2271, 2), (key2273, 2), (key2295, -4), (key2325, -2), (key2337, 2)]

def row6848 : Integer.Sparse Key := [(key1992, -1), (key1995, 1), (key2002, 1), (key2004, -1), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, -1), (key2295, 2), (key2325, 1), (key2337, -1)]

def row6849 : Integer.Sparse Key := [(key1992, -1), (key1995, 1), (key2002, 1), (key2004, -1), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, -1), (key2295, 2), (key2325, 1), (key2337, -1)]

def row6850 : Integer.Sparse Key := [(key1992, 2), (key1995, -2), (key2002, -2), (key2004, 2), (key2237, -2), (key2260, 2), (key2271, 2), (key2273, 2), (key2295, -4), (key2325, -2), (key2337, 2)]

def row6851 : Integer.Sparse Key := [(key1992, 2), (key1995, -2), (key2002, -2), (key2004, 2), (key2237, -2), (key2260, 2), (key2271, 2), (key2273, 2), (key2295, -4), (key2325, -2), (key2337, 2)]

def row6852 : Integer.Sparse Key := [(key1992, -1), (key1995, 1), (key2002, 1), (key2004, -1), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, -1), (key2295, 2), (key2325, 1), (key2337, -1)]

def row6853 : Integer.Sparse Key := [(key1992, -1), (key1995, 1), (key2002, 1), (key2004, -1), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, -1), (key2295, 2), (key2325, 1), (key2337, -1)]

def row6854 : Integer.Sparse Key := [(key1992, -1), (key1995, 1), (key2002, 1), (key2004, -1), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, -1), (key2295, 2), (key2325, 1), (key2337, -1)]

def row6855 : Integer.Sparse Key := [(key1992, -1), (key1995, 1), (key2002, 1), (key2004, -1), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, -1), (key2295, 2), (key2325, 1), (key2337, -1)]

def row6856 : Integer.Sparse Key := [(key1992, -1), (key1995, 1), (key2002, 1), (key2004, -1), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, -1), (key2295, 2), (key2325, 1), (key2337, -1)]

def row6857 : Integer.Sparse Key := [(key1992, -1), (key1995, 1), (key2002, 1), (key2004, -1), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, -1), (key2295, 2), (key2325, 1), (key2337, -1)]

def row6858 : Integer.Sparse Key := [(key1992, 2), (key1995, -2), (key2002, -2), (key2004, 2), (key2237, -2), (key2260, 2), (key2271, 2), (key2273, 2), (key2295, -4), (key2325, -2), (key2337, 2)]

def row6859 : Integer.Sparse Key := [(key1992, -1), (key1995, 1), (key2002, 1), (key2004, -1), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, -1), (key2295, 2), (key2325, 1), (key2337, -1)]

def row6860 : Integer.Sparse Key := [(key1992, -1), (key1995, 1), (key2002, 1), (key2004, -1), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, -1), (key2295, 2), (key2325, 1), (key2337, -1)]

def row6861 : Integer.Sparse Key := [(key1992, 2), (key1995, -2), (key2002, -2), (key2004, 2), (key2237, -2), (key2260, 2), (key2271, 2), (key2273, 2), (key2295, -4), (key2325, -2), (key2337, 2)]

def row6862 : Integer.Sparse Key := [(key1992, -4), (key1995, 4), (key2002, 4), (key2004, -4), (key2237, 4), (key2260, -4), (key2271, -4), (key2273, -4), (key2295, 8), (key2325, 4), (key2337, -4)]

def row6863 : Integer.Sparse Key := [(key1992, 2), (key1995, -2), (key2002, -2), (key2004, 2), (key2237, -2), (key2260, 2), (key2271, 2), (key2273, 2), (key2295, -4), (key2325, -2), (key2337, 2)]

def row6864 : Integer.Sparse Key := [(key1992, 2), (key1995, -2), (key2002, -2), (key2004, 2), (key2237, -2), (key2260, 2), (key2271, 2), (key2273, 2), (key2295, -4), (key2325, -2), (key2337, 2)]

def row6865 : Integer.Sparse Key := [(key1992, 2), (key1995, -2), (key2002, -2), (key2004, 2), (key2237, -2), (key2260, 2), (key2271, 2), (key2273, 2), (key2295, -4), (key2325, -2), (key2337, 2)]

def row6866 : Integer.Sparse Key := [(key1992, 2), (key1995, -2), (key2002, -2), (key2004, 2), (key2237, -2), (key2260, 2), (key2271, 2), (key2273, 2), (key2295, -4), (key2325, -2), (key2337, 2)]

def row6867 : Integer.Sparse Key := [(key1992, -4), (key1995, 4), (key2002, 4), (key2004, -4), (key2237, 4), (key2260, -4), (key2271, -4), (key2273, -4), (key2295, 8), (key2325, 4), (key2337, -4)]

def row6868 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2065, 1), (key2073, -1), (key2083, -1), (key2088, 1), (key2178, 1), (key2180, -1), (key2278, -1), (key2282, 1), (key2329, 1), (key2331, -1)]

def row6869 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2065, 1), (key2073, -1), (key2083, -1), (key2088, 1), (key2178, 1), (key2180, -1), (key2278, -1), (key2282, 1), (key2329, 1), (key2331, -1)]

def row6870 : Integer.Sparse Key := [(key2035, 2), (key2038, -2), (key2065, -2), (key2073, 2), (key2083, 2), (key2088, -2), (key2178, -2), (key2180, 2), (key2278, 2), (key2282, -2), (key2329, -2), (key2331, 2)]

def row6871 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2065, 1), (key2073, -1), (key2083, -1), (key2088, 1), (key2178, 1), (key2180, -1), (key2278, -1), (key2282, 1), (key2329, 1), (key2331, -1)]

def row6872 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2065, 1), (key2073, -1), (key2083, -1), (key2088, 1), (key2178, 1), (key2180, -1), (key2278, -1), (key2282, 1), (key2329, 1), (key2331, -1)]

def row6873 : Integer.Sparse Key := [(key2035, 2), (key2038, -2), (key2065, -2), (key2073, 2), (key2083, 2), (key2088, -2), (key2178, -2), (key2180, 2), (key2278, 2), (key2282, -2), (key2329, -2), (key2331, 2)]

def row6874 : Integer.Sparse Key := [(key2035, 2), (key2038, -2), (key2065, -2), (key2073, 2), (key2083, 2), (key2088, -2), (key2178, -2), (key2180, 2), (key2278, 2), (key2282, -2), (key2329, -2), (key2331, 2)]

def row6875 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2065, 1), (key2073, -1), (key2083, -1), (key2088, 1), (key2178, 1), (key2180, -1), (key2278, -1), (key2282, 1), (key2329, 1), (key2331, -1)]

def row6876 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2065, 1), (key2073, -1), (key2083, -1), (key2088, 1), (key2178, 1), (key2180, -1), (key2278, -1), (key2282, 1), (key2329, 1), (key2331, -1)]

def row6877 : Integer.Sparse Key := [(key2035, 2), (key2038, -2), (key2065, -2), (key2073, 2), (key2083, 2), (key2088, -2), (key2178, -2), (key2180, 2), (key2278, 2), (key2282, -2), (key2329, -2), (key2331, 2)]

def row6878 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2065, 1), (key2073, -1), (key2083, -1), (key2088, 1), (key2178, 1), (key2180, -1), (key2278, -1), (key2282, 1), (key2329, 1), (key2331, -1)]

def row6879 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2065, 1), (key2073, -1), (key2083, -1), (key2088, 1), (key2178, 1), (key2180, -1), (key2278, -1), (key2282, 1), (key2329, 1), (key2331, -1)]

def row6880 : Integer.Sparse Key := [(key2035, 2), (key2038, -2), (key2065, -2), (key2073, 2), (key2083, 2), (key2088, -2), (key2178, -2), (key2180, 2), (key2278, 2), (key2282, -2), (key2329, -2), (key2331, 2)]

def row6881 : Integer.Sparse Key := [(key2035, 2), (key2038, -2), (key2065, -2), (key2073, 2), (key2083, 2), (key2088, -2), (key2178, -2), (key2180, 2), (key2278, 2), (key2282, -2), (key2329, -2), (key2331, 2)]

def row6882 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2065, 1), (key2073, -1), (key2083, -1), (key2088, 1), (key2178, 1), (key2180, -1), (key2278, -1), (key2282, 1), (key2329, 1), (key2331, -1)]

def row6883 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2065, 1), (key2073, -1), (key2083, -1), (key2088, 1), (key2178, 1), (key2180, -1), (key2278, -1), (key2282, 1), (key2329, 1), (key2331, -1)]

def row6884 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2065, 1), (key2073, -1), (key2083, -1), (key2088, 1), (key2178, 1), (key2180, -1), (key2278, -1), (key2282, 1), (key2329, 1), (key2331, -1)]

def row6885 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2065, 1), (key2073, -1), (key2083, -1), (key2088, 1), (key2178, 1), (key2180, -1), (key2278, -1), (key2282, 1), (key2329, 1), (key2331, -1)]

def row6886 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2065, 1), (key2073, -1), (key2083, -1), (key2088, 1), (key2178, 1), (key2180, -1), (key2278, -1), (key2282, 1), (key2329, 1), (key2331, -1)]

def row6887 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2065, 1), (key2073, -1), (key2083, -1), (key2088, 1), (key2178, 1), (key2180, -1), (key2278, -1), (key2282, 1), (key2329, 1), (key2331, -1)]

def row6888 : Integer.Sparse Key := [(key2035, 2), (key2038, -2), (key2065, -2), (key2073, 2), (key2083, 2), (key2088, -2), (key2178, -2), (key2180, 2), (key2278, 2), (key2282, -2), (key2329, -2), (key2331, 2)]

def row6889 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2065, 1), (key2073, -1), (key2083, -1), (key2088, 1), (key2178, 1), (key2180, -1), (key2278, -1), (key2282, 1), (key2329, 1), (key2331, -1)]

def row6890 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2065, 1), (key2073, -1), (key2083, -1), (key2088, 1), (key2178, 1), (key2180, -1), (key2278, -1), (key2282, 1), (key2329, 1), (key2331, -1)]

def row6891 : Integer.Sparse Key := [(key2035, 2), (key2038, -2), (key2065, -2), (key2073, 2), (key2083, 2), (key2088, -2), (key2178, -2), (key2180, 2), (key2278, 2), (key2282, -2), (key2329, -2), (key2331, 2)]

def row6892 : Integer.Sparse Key := [(key2035, -4), (key2038, 4), (key2065, 4), (key2073, -4), (key2083, -4), (key2088, 4), (key2178, 4), (key2180, -4), (key2278, -4), (key2282, 4), (key2329, 4), (key2331, -4)]

def row6893 : Integer.Sparse Key := [(key2035, 2), (key2038, -2), (key2065, -2), (key2073, 2), (key2083, 2), (key2088, -2), (key2178, -2), (key2180, 2), (key2278, 2), (key2282, -2), (key2329, -2), (key2331, 2)]

def row6894 : Integer.Sparse Key := [(key2035, 2), (key2038, -2), (key2065, -2), (key2073, 2), (key2083, 2), (key2088, -2), (key2178, -2), (key2180, 2), (key2278, 2), (key2282, -2), (key2329, -2), (key2331, 2)]

def row6895 : Integer.Sparse Key := [(key2035, 2), (key2038, -2), (key2065, -2), (key2073, 2), (key2083, 2), (key2088, -2), (key2178, -2), (key2180, 2), (key2278, 2), (key2282, -2), (key2329, -2), (key2331, 2)]

def row6896 : Integer.Sparse Key := [(key2035, 2), (key2038, -2), (key2065, -2), (key2073, 2), (key2083, 2), (key2088, -2), (key2178, -2), (key2180, 2), (key2278, 2), (key2282, -2), (key2329, -2), (key2331, 2)]

def row6897 : Integer.Sparse Key := [(key2035, -4), (key2038, 4), (key2065, 4), (key2073, -4), (key2083, -4), (key2088, 4), (key2178, 4), (key2180, -4), (key2278, -4), (key2282, 4), (key2329, 4), (key2331, -4)]

def row6898 : Integer.Sparse Key := [(key729, -1), (key735, 1), (key739, 1), (key744, -1), (key795, 1), (key813, -1), (key819, -1), (key826, 1), (key869, -1), (key878, 1), (key903, 1), (key909, -1)]

def row6899 : Integer.Sparse Key := [(key729, -1), (key735, 1), (key739, 1), (key744, -1), (key795, 1), (key813, -1), (key819, -1), (key826, 1), (key869, -1), (key878, 1), (key903, 1), (key909, -1)]

def row6900 : Integer.Sparse Key := [(key729, 2), (key735, -2), (key739, -2), (key744, 2), (key795, -2), (key813, 2), (key819, 2), (key826, -2), (key869, 2), (key878, -2), (key903, -2), (key909, 2)]

def row6901 : Integer.Sparse Key := [(key729, -1), (key735, 1), (key739, 1), (key744, -1), (key795, 1), (key813, -1), (key819, -1), (key826, 1), (key869, -1), (key878, 1), (key903, 1), (key909, -1)]

def row6902 : Integer.Sparse Key := [(key729, -1), (key735, 1), (key739, 1), (key744, -1), (key795, 1), (key813, -1), (key819, -1), (key826, 1), (key869, -1), (key878, 1), (key903, 1), (key909, -1)]

def row6903 : Integer.Sparse Key := [(key729, 2), (key735, -2), (key739, -2), (key744, 2), (key795, -2), (key813, 2), (key819, 2), (key826, -2), (key869, 2), (key878, -2), (key903, -2), (key909, 2)]

def row6904 : Integer.Sparse Key := [(key729, 2), (key735, -2), (key739, -2), (key744, 2), (key795, -2), (key813, 2), (key819, 2), (key826, -2), (key869, 2), (key878, -2), (key903, -2), (key909, 2)]

def row6905 : Integer.Sparse Key := [(key729, -1), (key735, 1), (key739, 1), (key744, -1), (key795, 1), (key813, -1), (key819, -1), (key826, 1), (key869, -1), (key878, 1), (key903, 1), (key909, -1)]

def row6906 : Integer.Sparse Key := [(key729, -1), (key735, 1), (key739, 1), (key744, -1), (key795, 1), (key813, -1), (key819, -1), (key826, 1), (key869, -1), (key878, 1), (key903, 1), (key909, -1)]

def row6907 : Integer.Sparse Key := [(key729, 2), (key735, -2), (key739, -2), (key744, 2), (key795, -2), (key813, 2), (key819, 2), (key826, -2), (key869, 2), (key878, -2), (key903, -2), (key909, 2)]

def row6908 : Integer.Sparse Key := [(key729, -1), (key735, 1), (key739, 1), (key744, -1), (key795, 1), (key813, -1), (key819, -1), (key826, 1), (key869, -1), (key878, 1), (key903, 1), (key909, -1)]

def row6909 : Integer.Sparse Key := [(key729, -1), (key735, 1), (key739, 1), (key744, -1), (key795, 1), (key813, -1), (key819, -1), (key826, 1), (key869, -1), (key878, 1), (key903, 1), (key909, -1)]

def row6910 : Integer.Sparse Key := [(key729, 2), (key735, -2), (key739, -2), (key744, 2), (key795, -2), (key813, 2), (key819, 2), (key826, -2), (key869, 2), (key878, -2), (key903, -2), (key909, 2)]

def row6911 : Integer.Sparse Key := [(key729, 2), (key735, -2), (key739, -2), (key744, 2), (key795, -2), (key813, 2), (key819, 2), (key826, -2), (key869, 2), (key878, -2), (key903, -2), (key909, 2)]

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

def row6912 : Integer.Sparse Key := [(key729, -1), (key735, 1), (key739, 1), (key744, -1), (key795, 1), (key813, -1), (key819, -1), (key826, 1), (key869, -1), (key878, 1), (key903, 1), (key909, -1)]

def row6913 : Integer.Sparse Key := [(key729, -1), (key735, 1), (key739, 1), (key744, -1), (key795, 1), (key813, -1), (key819, -1), (key826, 1), (key869, -1), (key878, 1), (key903, 1), (key909, -1)]

def row6914 : Integer.Sparse Key := [(key729, -1), (key735, 1), (key739, 1), (key744, -1), (key795, 1), (key813, -1), (key819, -1), (key826, 1), (key869, -1), (key878, 1), (key903, 1), (key909, -1)]

def row6915 : Integer.Sparse Key := [(key729, -1), (key735, 1), (key739, 1), (key744, -1), (key795, 1), (key813, -1), (key819, -1), (key826, 1), (key869, -1), (key878, 1), (key903, 1), (key909, -1)]

def row6916 : Integer.Sparse Key := [(key729, -1), (key735, 1), (key739, 1), (key744, -1), (key795, 1), (key813, -1), (key819, -1), (key826, 1), (key869, -1), (key878, 1), (key903, 1), (key909, -1)]

def row6917 : Integer.Sparse Key := [(key729, -1), (key735, 1), (key739, 1), (key744, -1), (key795, 1), (key813, -1), (key819, -1), (key826, 1), (key869, -1), (key878, 1), (key903, 1), (key909, -1)]

def row6918 : Integer.Sparse Key := [(key729, 2), (key735, -2), (key739, -2), (key744, 2), (key795, -2), (key813, 2), (key819, 2), (key826, -2), (key869, 2), (key878, -2), (key903, -2), (key909, 2)]

def row6919 : Integer.Sparse Key := [(key729, -1), (key735, 1), (key739, 1), (key744, -1), (key795, 1), (key813, -1), (key819, -1), (key826, 1), (key869, -1), (key878, 1), (key903, 1), (key909, -1)]

def row6920 : Integer.Sparse Key := [(key729, -1), (key735, 1), (key739, 1), (key744, -1), (key795, 1), (key813, -1), (key819, -1), (key826, 1), (key869, -1), (key878, 1), (key903, 1), (key909, -1)]

def row6921 : Integer.Sparse Key := [(key729, 2), (key735, -2), (key739, -2), (key744, 2), (key795, -2), (key813, 2), (key819, 2), (key826, -2), (key869, 2), (key878, -2), (key903, -2), (key909, 2)]

def row6922 : Integer.Sparse Key := [(key729, -4), (key735, 4), (key739, 4), (key744, -4), (key795, 4), (key813, -4), (key819, -4), (key826, 4), (key869, -4), (key878, 4), (key903, 4), (key909, -4)]

def row6923 : Integer.Sparse Key := [(key729, 2), (key735, -2), (key739, -2), (key744, 2), (key795, -2), (key813, 2), (key819, 2), (key826, -2), (key869, 2), (key878, -2), (key903, -2), (key909, 2)]

def row6924 : Integer.Sparse Key := [(key729, 2), (key735, -2), (key739, -2), (key744, 2), (key795, -2), (key813, 2), (key819, 2), (key826, -2), (key869, 2), (key878, -2), (key903, -2), (key909, 2)]

def row6925 : Integer.Sparse Key := [(key729, 2), (key735, -2), (key739, -2), (key744, 2), (key795, -2), (key813, 2), (key819, 2), (key826, -2), (key869, 2), (key878, -2), (key903, -2), (key909, 2)]

def row6926 : Integer.Sparse Key := [(key729, 2), (key735, -2), (key739, -2), (key744, 2), (key795, -2), (key813, 2), (key819, 2), (key826, -2), (key869, 2), (key878, -2), (key903, -2), (key909, 2)]

def row6927 : Integer.Sparse Key := [(key729, -4), (key735, 4), (key739, 4), (key744, -4), (key795, 4), (key813, -4), (key819, -4), (key826, 4), (key869, -4), (key878, 4), (key903, 4), (key909, -4)]

def row6928 : Integer.Sparse Key := [(key2031, 1), (key2036, -1), (key2061, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, -1), (key2155, 1), (key2243, 1), (key2248, -1), (key2304, -1), (key2306, 1)]

def row6929 : Integer.Sparse Key := [(key2031, 1), (key2036, -1), (key2061, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, -1), (key2155, 1), (key2243, 1), (key2248, -1), (key2304, -1), (key2306, 1)]

def row6930 : Integer.Sparse Key := [(key2031, -2), (key2036, 2), (key2061, 2), (key2071, -2), (key2093, -2), (key2096, 2), (key2150, 2), (key2155, -2), (key2243, -2), (key2248, 2), (key2304, 2), (key2306, -2)]

def row6931 : Integer.Sparse Key := [(key2031, 1), (key2036, -1), (key2061, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, -1), (key2155, 1), (key2243, 1), (key2248, -1), (key2304, -1), (key2306, 1)]

def row6932 : Integer.Sparse Key := [(key2031, 1), (key2036, -1), (key2061, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, -1), (key2155, 1), (key2243, 1), (key2248, -1), (key2304, -1), (key2306, 1)]

def row6933 : Integer.Sparse Key := [(key2031, -2), (key2036, 2), (key2061, 2), (key2071, -2), (key2093, -2), (key2096, 2), (key2150, 2), (key2155, -2), (key2243, -2), (key2248, 2), (key2304, 2), (key2306, -2)]

def row6934 : Integer.Sparse Key := [(key2031, -2), (key2036, 2), (key2061, 2), (key2071, -2), (key2093, -2), (key2096, 2), (key2150, 2), (key2155, -2), (key2243, -2), (key2248, 2), (key2304, 2), (key2306, -2)]

def row6935 : Integer.Sparse Key := [(key2031, 1), (key2036, -1), (key2061, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, -1), (key2155, 1), (key2243, 1), (key2248, -1), (key2304, -1), (key2306, 1)]

def row6936 : Integer.Sparse Key := [(key2031, 1), (key2036, -1), (key2061, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, -1), (key2155, 1), (key2243, 1), (key2248, -1), (key2304, -1), (key2306, 1)]

def row6937 : Integer.Sparse Key := [(key2031, -2), (key2036, 2), (key2061, 2), (key2071, -2), (key2093, -2), (key2096, 2), (key2150, 2), (key2155, -2), (key2243, -2), (key2248, 2), (key2304, 2), (key2306, -2)]

def row6938 : Integer.Sparse Key := [(key2031, 1), (key2036, -1), (key2061, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, -1), (key2155, 1), (key2243, 1), (key2248, -1), (key2304, -1), (key2306, 1)]

def row6939 : Integer.Sparse Key := [(key2031, 1), (key2036, -1), (key2061, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, -1), (key2155, 1), (key2243, 1), (key2248, -1), (key2304, -1), (key2306, 1)]

def row6940 : Integer.Sparse Key := [(key2031, -2), (key2036, 2), (key2061, 2), (key2071, -2), (key2093, -2), (key2096, 2), (key2150, 2), (key2155, -2), (key2243, -2), (key2248, 2), (key2304, 2), (key2306, -2)]

def row6941 : Integer.Sparse Key := [(key2031, -2), (key2036, 2), (key2061, 2), (key2071, -2), (key2093, -2), (key2096, 2), (key2150, 2), (key2155, -2), (key2243, -2), (key2248, 2), (key2304, 2), (key2306, -2)]

def row6942 : Integer.Sparse Key := [(key2031, 1), (key2036, -1), (key2061, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, -1), (key2155, 1), (key2243, 1), (key2248, -1), (key2304, -1), (key2306, 1)]

def row6943 : Integer.Sparse Key := [(key2031, 1), (key2036, -1), (key2061, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, -1), (key2155, 1), (key2243, 1), (key2248, -1), (key2304, -1), (key2306, 1)]

def row6944 : Integer.Sparse Key := [(key2031, 1), (key2036, -1), (key2061, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, -1), (key2155, 1), (key2243, 1), (key2248, -1), (key2304, -1), (key2306, 1)]

def row6945 : Integer.Sparse Key := [(key2031, 1), (key2036, -1), (key2061, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, -1), (key2155, 1), (key2243, 1), (key2248, -1), (key2304, -1), (key2306, 1)]

def row6946 : Integer.Sparse Key := [(key2031, 1), (key2036, -1), (key2061, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, -1), (key2155, 1), (key2243, 1), (key2248, -1), (key2304, -1), (key2306, 1)]

def row6947 : Integer.Sparse Key := [(key2031, 1), (key2036, -1), (key2061, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, -1), (key2155, 1), (key2243, 1), (key2248, -1), (key2304, -1), (key2306, 1)]

def row6948 : Integer.Sparse Key := [(key2031, -2), (key2036, 2), (key2061, 2), (key2071, -2), (key2093, -2), (key2096, 2), (key2150, 2), (key2155, -2), (key2243, -2), (key2248, 2), (key2304, 2), (key2306, -2)]

def row6949 : Integer.Sparse Key := [(key2031, 1), (key2036, -1), (key2061, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, -1), (key2155, 1), (key2243, 1), (key2248, -1), (key2304, -1), (key2306, 1)]

def row6950 : Integer.Sparse Key := [(key2031, 1), (key2036, -1), (key2061, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, -1), (key2155, 1), (key2243, 1), (key2248, -1), (key2304, -1), (key2306, 1)]

def row6951 : Integer.Sparse Key := [(key2031, -2), (key2036, 2), (key2061, 2), (key2071, -2), (key2093, -2), (key2096, 2), (key2150, 2), (key2155, -2), (key2243, -2), (key2248, 2), (key2304, 2), (key2306, -2)]

def row6952 : Integer.Sparse Key := [(key2031, 4), (key2036, -4), (key2061, -4), (key2071, 4), (key2093, 4), (key2096, -4), (key2150, -4), (key2155, 4), (key2243, 4), (key2248, -4), (key2304, -4), (key2306, 4)]

def row6953 : Integer.Sparse Key := [(key2031, -2), (key2036, 2), (key2061, 2), (key2071, -2), (key2093, -2), (key2096, 2), (key2150, 2), (key2155, -2), (key2243, -2), (key2248, 2), (key2304, 2), (key2306, -2)]

def row6954 : Integer.Sparse Key := [(key2031, -2), (key2036, 2), (key2061, 2), (key2071, -2), (key2093, -2), (key2096, 2), (key2150, 2), (key2155, -2), (key2243, -2), (key2248, 2), (key2304, 2), (key2306, -2)]

def row6955 : Integer.Sparse Key := [(key2031, -2), (key2036, 2), (key2061, 2), (key2071, -2), (key2093, -2), (key2096, 2), (key2150, 2), (key2155, -2), (key2243, -2), (key2248, 2), (key2304, 2), (key2306, -2)]

def row6956 : Integer.Sparse Key := [(key2031, -2), (key2036, 2), (key2061, 2), (key2071, -2), (key2093, -2), (key2096, 2), (key2150, 2), (key2155, -2), (key2243, -2), (key2248, 2), (key2304, 2), (key2306, -2)]

def row6957 : Integer.Sparse Key := [(key2031, 4), (key2036, -4), (key2061, -4), (key2071, 4), (key2093, 4), (key2096, -4), (key2150, -4), (key2155, 4), (key2243, 4), (key2248, -4), (key2304, -4), (key2306, 4)]

def row6958 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2081, 1), (key2083, -1), (key2154, 1), (key2170, -1), (key2180, -1), (key2190, 1), (key2278, -1), (key2290, 1), (key2329, 1), (key2334, -1)]

def row6959 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2081, 1), (key2083, -1), (key2154, 1), (key2170, -1), (key2180, -1), (key2190, 1), (key2278, -1), (key2290, 1), (key2329, 1), (key2334, -1)]

def row6960 : Integer.Sparse Key := [(key2035, 2), (key2038, -2), (key2081, -2), (key2083, 2), (key2154, -2), (key2170, 2), (key2180, 2), (key2190, -2), (key2278, 2), (key2290, -2), (key2329, -2), (key2334, 2)]

def row6961 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2081, 1), (key2083, -1), (key2154, 1), (key2170, -1), (key2180, -1), (key2190, 1), (key2278, -1), (key2290, 1), (key2329, 1), (key2334, -1)]

def row6962 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2081, 1), (key2083, -1), (key2154, 1), (key2170, -1), (key2180, -1), (key2190, 1), (key2278, -1), (key2290, 1), (key2329, 1), (key2334, -1)]

def row6963 : Integer.Sparse Key := [(key2035, 2), (key2038, -2), (key2081, -2), (key2083, 2), (key2154, -2), (key2170, 2), (key2180, 2), (key2190, -2), (key2278, 2), (key2290, -2), (key2329, -2), (key2334, 2)]

def row6964 : Integer.Sparse Key := [(key2035, 2), (key2038, -2), (key2081, -2), (key2083, 2), (key2154, -2), (key2170, 2), (key2180, 2), (key2190, -2), (key2278, 2), (key2290, -2), (key2329, -2), (key2334, 2)]

def row6965 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2081, 1), (key2083, -1), (key2154, 1), (key2170, -1), (key2180, -1), (key2190, 1), (key2278, -1), (key2290, 1), (key2329, 1), (key2334, -1)]

def row6966 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2081, 1), (key2083, -1), (key2154, 1), (key2170, -1), (key2180, -1), (key2190, 1), (key2278, -1), (key2290, 1), (key2329, 1), (key2334, -1)]

def row6967 : Integer.Sparse Key := [(key2035, 2), (key2038, -2), (key2081, -2), (key2083, 2), (key2154, -2), (key2170, 2), (key2180, 2), (key2190, -2), (key2278, 2), (key2290, -2), (key2329, -2), (key2334, 2)]

def row6968 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2081, 1), (key2083, -1), (key2154, 1), (key2170, -1), (key2180, -1), (key2190, 1), (key2278, -1), (key2290, 1), (key2329, 1), (key2334, -1)]

def row6969 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2081, 1), (key2083, -1), (key2154, 1), (key2170, -1), (key2180, -1), (key2190, 1), (key2278, -1), (key2290, 1), (key2329, 1), (key2334, -1)]

def row6970 : Integer.Sparse Key := [(key2035, 2), (key2038, -2), (key2081, -2), (key2083, 2), (key2154, -2), (key2170, 2), (key2180, 2), (key2190, -2), (key2278, 2), (key2290, -2), (key2329, -2), (key2334, 2)]

def row6971 : Integer.Sparse Key := [(key2035, 2), (key2038, -2), (key2081, -2), (key2083, 2), (key2154, -2), (key2170, 2), (key2180, 2), (key2190, -2), (key2278, 2), (key2290, -2), (key2329, -2), (key2334, 2)]

def row6972 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2081, 1), (key2083, -1), (key2154, 1), (key2170, -1), (key2180, -1), (key2190, 1), (key2278, -1), (key2290, 1), (key2329, 1), (key2334, -1)]

def row6973 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2081, 1), (key2083, -1), (key2154, 1), (key2170, -1), (key2180, -1), (key2190, 1), (key2278, -1), (key2290, 1), (key2329, 1), (key2334, -1)]

def row6974 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2081, 1), (key2083, -1), (key2154, 1), (key2170, -1), (key2180, -1), (key2190, 1), (key2278, -1), (key2290, 1), (key2329, 1), (key2334, -1)]

def row6975 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2081, 1), (key2083, -1), (key2154, 1), (key2170, -1), (key2180, -1), (key2190, 1), (key2278, -1), (key2290, 1), (key2329, 1), (key2334, -1)]

def row6976 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2081, 1), (key2083, -1), (key2154, 1), (key2170, -1), (key2180, -1), (key2190, 1), (key2278, -1), (key2290, 1), (key2329, 1), (key2334, -1)]

def row6977 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2081, 1), (key2083, -1), (key2154, 1), (key2170, -1), (key2180, -1), (key2190, 1), (key2278, -1), (key2290, 1), (key2329, 1), (key2334, -1)]

def row6978 : Integer.Sparse Key := [(key2035, 2), (key2038, -2), (key2081, -2), (key2083, 2), (key2154, -2), (key2170, 2), (key2180, 2), (key2190, -2), (key2278, 2), (key2290, -2), (key2329, -2), (key2334, 2)]

def row6979 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2081, 1), (key2083, -1), (key2154, 1), (key2170, -1), (key2180, -1), (key2190, 1), (key2278, -1), (key2290, 1), (key2329, 1), (key2334, -1)]

def row6980 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2081, 1), (key2083, -1), (key2154, 1), (key2170, -1), (key2180, -1), (key2190, 1), (key2278, -1), (key2290, 1), (key2329, 1), (key2334, -1)]

def row6981 : Integer.Sparse Key := [(key2035, 2), (key2038, -2), (key2081, -2), (key2083, 2), (key2154, -2), (key2170, 2), (key2180, 2), (key2190, -2), (key2278, 2), (key2290, -2), (key2329, -2), (key2334, 2)]

def row6982 : Integer.Sparse Key := [(key2035, -4), (key2038, 4), (key2081, 4), (key2083, -4), (key2154, 4), (key2170, -4), (key2180, -4), (key2190, 4), (key2278, -4), (key2290, 4), (key2329, 4), (key2334, -4)]

def row6983 : Integer.Sparse Key := [(key2035, 2), (key2038, -2), (key2081, -2), (key2083, 2), (key2154, -2), (key2170, 2), (key2180, 2), (key2190, -2), (key2278, 2), (key2290, -2), (key2329, -2), (key2334, 2)]

def row6984 : Integer.Sparse Key := [(key2035, 2), (key2038, -2), (key2081, -2), (key2083, 2), (key2154, -2), (key2170, 2), (key2180, 2), (key2190, -2), (key2278, 2), (key2290, -2), (key2329, -2), (key2334, 2)]

def row6985 : Integer.Sparse Key := [(key2035, 2), (key2038, -2), (key2081, -2), (key2083, 2), (key2154, -2), (key2170, 2), (key2180, 2), (key2190, -2), (key2278, 2), (key2290, -2), (key2329, -2), (key2334, 2)]

def row6986 : Integer.Sparse Key := [(key2035, 2), (key2038, -2), (key2081, -2), (key2083, 2), (key2154, -2), (key2170, 2), (key2180, 2), (key2190, -2), (key2278, 2), (key2290, -2), (key2329, -2), (key2334, 2)]

def row6987 : Integer.Sparse Key := [(key2035, -4), (key2038, 4), (key2081, 4), (key2083, -4), (key2154, 4), (key2170, -4), (key2180, -4), (key2190, 4), (key2278, -4), (key2290, 4), (key2329, 4), (key2334, -4)]

def row6988 : Integer.Sparse Key := [(key781, 1), (key784, -1), (key806, -2), (key809, 1), (key814, 1), (key822, 1), (key827, -1), (key875, 1), (key879, -1), (key906, -1), (key910, 1)]

def row6989 : Integer.Sparse Key := [(key781, 1), (key784, -1), (key806, -2), (key809, 1), (key814, 1), (key822, 1), (key827, -1), (key875, 1), (key879, -1), (key906, -1), (key910, 1)]

def row6990 : Integer.Sparse Key := [(key781, -2), (key784, 2), (key806, 4), (key809, -2), (key814, -2), (key822, -2), (key827, 2), (key875, -2), (key879, 2), (key906, 2), (key910, -2)]

def row6991 : Integer.Sparse Key := [(key781, 1), (key784, -1), (key806, -2), (key809, 1), (key814, -1), (key822, 3), (key827, -1), (key875, 1), (key879, -1), (key906, -1), (key910, 1)]

def row6992 : Integer.Sparse Key := [(key781, 1), (key784, -1), (key806, -2), (key809, 1), (key814, -1), (key822, 3), (key827, -1), (key875, 1), (key879, -1), (key906, -1), (key910, 1)]

def row6993 : Integer.Sparse Key := [(key781, -2), (key784, 2), (key806, 4), (key809, -2), (key822, -4), (key827, 2), (key875, -2), (key879, 2), (key906, 2), (key910, -2)]

def row6994 : Integer.Sparse Key := [(key781, -2), (key784, 2), (key806, 4), (key809, -2), (key822, -4), (key827, 2), (key875, -2), (key879, 2), (key906, 2), (key910, -2)]

def row6995 : Integer.Sparse Key := [(key781, 1), (key784, -1), (key806, -2), (key809, 1), (key814, -1), (key822, 3), (key827, -1), (key875, 1), (key879, -1), (key906, -1), (key910, 1)]

def row6996 : Integer.Sparse Key := [(key781, 1), (key784, -1), (key806, -2), (key809, 1), (key814, -1), (key822, 3), (key827, -1), (key875, 1), (key879, -1), (key906, -1), (key910, 1)]

def row6997 : Integer.Sparse Key := [(key781, -2), (key784, 2), (key806, 4), (key809, -2), (key814, -2), (key822, -2), (key827, 2), (key875, -2), (key879, 2), (key906, 2), (key910, -2)]

def row6998 : Integer.Sparse Key := [(key781, 1), (key784, -1), (key806, -2), (key809, 1), (key814, 1), (key822, 1), (key827, -1), (key875, 1), (key879, -1), (key906, -1), (key910, 1)]

def row6999 : Integer.Sparse Key := [(key781, 1), (key784, -1), (key806, -2), (key809, 1), (key814, 1), (key822, 1), (key827, -1), (key875, 1), (key879, -1), (key906, -1), (key910, 1)]

def row7000 : Integer.Sparse Key := [(key781, -2), (key784, 2), (key806, 4), (key809, -2), (key814, -6), (key822, 2), (key827, 2), (key875, -2), (key879, 6), (key906, -2), (key910, -2)]

def row7001 : Integer.Sparse Key := [(key781, -2), (key784, 2), (key806, 4), (key809, -2), (key814, -6), (key822, 2), (key827, 2), (key875, -2), (key879, 6), (key906, -2), (key910, -2)]

def row7002 : Integer.Sparse Key := [(key781, 1), (key784, -1), (key806, -2), (key809, 1), (key814, 1), (key822, 1), (key827, -1), (key875, 1), (key879, -3), (key906, 1), (key910, 1)]

def row7003 : Integer.Sparse Key := [(key781, 1), (key784, -1), (key806, -2), (key809, 1), (key814, 1), (key822, 1), (key827, -1), (key875, 1), (key879, -3), (key906, 1), (key910, 1)]

def row7004 : Integer.Sparse Key := [(key781, 1), (key784, -1), (key806, -2), (key809, 1), (key814, 6), (key822, -4), (key827, -1), (key875, 1), (key879, -3), (key906, 1), (key910, 1)]

def row7005 : Integer.Sparse Key := [(key781, 1), (key784, -1), (key806, -2), (key809, 1), (key814, 6), (key822, -4), (key827, -1), (key875, 1), (key879, -3), (key906, 1), (key910, 1)]

def row7006 : Integer.Sparse Key := [(key781, 1), (key784, -1), (key806, -2), (key809, 1), (key814, 2), (key827, -1), (key875, 1), (key879, -3), (key906, 1), (key910, 1)]

def row7007 : Integer.Sparse Key := [(key781, 1), (key784, -1), (key806, -2), (key809, 1), (key814, 2), (key827, -1), (key875, 1), (key879, -3), (key906, 1), (key910, 1)]

def row7008 : Integer.Sparse Key := [(key781, -2), (key784, 2), (key806, 4), (key809, -2), (key814, -4), (key827, 2), (key875, -2), (key879, 6), (key906, -2), (key910, -2)]

def row7009 : Integer.Sparse Key := [(key781, 1), (key784, -1), (key806, -2), (key809, 1), (key814, 3), (key822, -1), (key827, -1), (key875, 1), (key879, -3), (key906, 1), (key910, 1)]

def row7010 : Integer.Sparse Key := [(key781, 1), (key784, -1), (key806, -2), (key809, 1), (key814, 3), (key822, -1), (key827, -1), (key875, 1), (key879, -3), (key906, 1), (key910, 1)]

def row7011 : Integer.Sparse Key := [(key781, -2), (key784, 2), (key806, 4), (key809, -2), (key814, -6), (key822, 2), (key827, 2), (key875, -2), (key879, 6), (key906, -2), (key910, -2)]

def row7012 : Integer.Sparse Key := [(key781, 4), (key784, -4), (key806, -8), (key809, 4), (key814, 4), (key822, 4), (key827, -4), (key875, 4), (key879, -4), (key906, -4), (key910, 4)]

def row7013 : Integer.Sparse Key := [(key781, -2), (key784, 2), (key806, 4), (key809, -2), (key814, -2), (key822, -2), (key827, 2), (key875, -2), (key879, 2), (key906, 2), (key910, -2)]

def row7014 : Integer.Sparse Key := [(key781, -2), (key784, 2), (key806, 4), (key809, -2), (key814, -2), (key822, -2), (key827, 2), (key875, -2), (key879, 2), (key906, 2), (key910, -2)]

def row7015 : Integer.Sparse Key := [(key781, -2), (key784, 2), (key806, 4), (key809, -2), (key814, -2), (key822, -2), (key827, 2), (key875, -2), (key879, 2), (key906, 2), (key910, -2)]

def row7016 : Integer.Sparse Key := [(key781, -2), (key784, 2), (key806, 4), (key809, -2), (key814, -2), (key822, -2), (key827, 2), (key875, -2), (key879, 2), (key906, 2), (key910, -2)]

def row7017 : Integer.Sparse Key := [(key781, 4), (key784, -4), (key806, -8), (key809, 4), (key814, 4), (key822, 4), (key827, -4), (key875, 4), (key879, -4), (key906, -4), (key910, 4)]

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

def row7494 : Integer.Sparse Key := [(key2452, 12), (key2458, 6), (key2519, 6), (key2528, -6), (key2530, -12), (key2560, -6)]

def row7495 : Integer.Sparse Key := [(key2452, 12), (key2458, 6), (key2519, 6), (key2528, -6), (key2530, -12), (key2560, -6)]

def row7496 : Integer.Sparse Key := [(key2452, 12), (key2458, 6), (key2519, 6), (key2528, -6), (key2530, -12), (key2560, -6)]

def row7497 : Integer.Sparse Key := [(key2452, 12), (key2458, 6), (key2519, 6), (key2528, -6), (key2530, -12), (key2560, -6)]

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

def row8485 : Integer.Sparse Key := [(key1254, 6), (key1263, -6), (key1607, 6), (key1646, -12), (key1804, 12), (key1835, -6)]

def row8486 : Integer.Sparse Key := [(key1254, 6), (key1263, -6), (key1607, 6), (key1646, -12), (key1804, 12), (key1835, -6)]

def row8487 : Integer.Sparse Key := [(key1254, 6), (key1263, -6), (key1607, 6), (key1646, -12), (key1804, 12), (key1835, -6)]

def row8488 : Integer.Sparse Key := [(key1254, 6), (key1263, -6), (key1607, 6), (key1646, -12), (key1804, 12), (key1835, -6)]

def row8489 : Integer.Sparse Key := [(key1254, -2), (key1263, 2), (key1529, -2), (key1607, -4), (key1763, 2), (key1835, 4)]

def row8490 : Integer.Sparse Key := [(key1254, -2), (key1263, 2), (key1529, -2), (key1607, -4), (key1763, 2), (key1835, 4)]

def row8491 : Integer.Sparse Key := [(key1254, -2), (key1263, 2), (key1529, -2), (key1607, -4), (key1763, 2), (key1835, 4)]

def row8492 : Integer.Sparse Key := [(key1254, -2), (key1263, 2), (key1529, -2), (key1607, -4), (key1763, 2), (key1835, 4)]

def row8493 : Integer.Sparse Key := [(key1254, -2), (key1263, 2), (key1529, -2), (key1607, -4), (key1763, 2), (key1835, 4)]

def row8494 : Integer.Sparse Key := [(key1254, -2), (key1263, 2), (key1529, -2), (key1607, -4), (key1763, 2), (key1835, 4)]

def row8495 : Integer.Sparse Key := [(key1254, -2), (key1263, 2), (key1529, -2), (key1607, -4), (key1763, 2), (key1835, 4)]

def row8496 : Integer.Sparse Key := [(key1254, -2), (key1263, 2), (key1529, -2), (key1607, -4), (key1763, 2), (key1835, 4)]

def row8497 : Integer.Sparse Key := [(key1254, -2), (key1263, 2), (key1529, -2), (key1607, -4), (key1763, 2), (key1835, 4)]

def row8498 : Integer.Sparse Key := [(key1254, -2), (key1263, 2), (key1529, -2), (key1607, -4), (key1763, 2), (key1835, 4)]

def row8499 : Integer.Sparse Key := [(key1254, -2), (key1263, 2), (key1529, -2), (key1607, -4), (key1763, 2), (key1835, 4)]

def row8500 : Integer.Sparse Key := [(key1254, -2), (key1263, 2), (key1529, -2), (key1607, -4), (key1763, 2), (key1835, 4)]

def row8501 : Integer.Sparse Key := [(key41, -24), (key205, 6), (key425, 18)]

def row8502 : Integer.Sparse Key := [(key41, -24), (key205, 6), (key425, 18)]

def row8503 : Integer.Sparse Key := [(key41, -24), (key205, 6), (key425, 18)]

def row8504 : Integer.Sparse Key := [(key41, -24), (key205, 6), (key425, 18)]

def row8505 : Integer.Sparse Key := [(key16, 6), (key98, -24), (key374, 6), (key425, 12)]

def row8506 : Integer.Sparse Key := [(key16, 6), (key98, -24), (key374, 6), (key425, 12)]

def row8507 : Integer.Sparse Key := [(key16, 6), (key98, -24), (key374, 6), (key425, 12)]

def row8508 : Integer.Sparse Key := [(key41, 6), (key98, -24), (key205, 6), (key425, 12)]

def row8509 : Integer.Sparse Key := [(key41, 6), (key98, -24), (key205, 6), (key425, 12)]

def row8510 : Integer.Sparse Key := [(key41, 6), (key98, -24), (key205, 6), (key425, 12)]

def row8511 : Integer.Sparse Key := [(key16, 6), (key98, -18), (key374, 6), (key425, 6)]

def row8512 : Integer.Sparse Key := [(key16, 6), (key98, -18), (key374, 6), (key425, 6)]

def row8513 : Integer.Sparse Key := [(key41, 6), (key98, -18), (key205, 6), (key425, 6)]

def row8514 : Integer.Sparse Key := [(key41, 6), (key98, -18), (key205, 6), (key425, 6)]

def row8515 : Integer.Sparse Key := [(key16, 6), (key98, -12), (key374, 6)]

def row8516 : Integer.Sparse Key := [(key41, 6), (key98, -12), (key205, 6)]

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

def row8597 : Integer.Sparse Key := [(key1289, 6), (key1384, -6), (key1539, -12), (key1566, 12), (key1895, -6), (key1902, 6)]

def row8598 : Integer.Sparse Key := [(key1289, 6), (key1384, -6), (key1539, -12), (key1566, 12), (key1895, -6), (key1902, 6)]

def row8599 : Integer.Sparse Key := [(key1289, 6), (key1384, -6), (key1539, -12), (key1566, 12), (key1895, -6), (key1902, 6)]

def row8600 : Integer.Sparse Key := [(key1289, 6), (key1384, -6), (key1539, -12), (key1566, 12), (key1895, -6), (key1902, 6)]

def row8601 : Integer.Sparse Key := [(key1309, 4), (key1350, 2), (key1417, -4), (key1471, -2), (key1539, 4), (key1566, -4), (key1895, 2), (key1902, -2)]

def row8602 : Integer.Sparse Key := [(key1309, 4), (key1350, 2), (key1417, -4), (key1471, -2), (key1539, 4), (key1566, -4), (key1895, 2), (key1902, -2)]

def row8603 : Integer.Sparse Key := [(key1309, 4), (key1350, 2), (key1417, -4), (key1471, -2), (key1539, 4), (key1566, -4), (key1895, 2), (key1902, -2)]

def row8604 : Integer.Sparse Key := [(key1309, 4), (key1350, 2), (key1417, -4), (key1471, -2), (key1539, 4), (key1566, -4), (key1895, 2), (key1902, -2)]

def row8605 : Integer.Sparse Key := [(key1309, 4), (key1350, 2), (key1417, -4), (key1471, -2), (key1539, 4), (key1566, -4), (key1895, 2), (key1902, -2)]

def row8606 : Integer.Sparse Key := [(key1309, 4), (key1350, 2), (key1417, -4), (key1471, -2), (key1539, 4), (key1566, -4), (key1895, 2), (key1902, -2)]

def row8607 : Integer.Sparse Key := [(key1309, 4), (key1350, 2), (key1417, -4), (key1471, -2), (key1539, 4), (key1566, -4), (key1895, 2), (key1902, -2)]

def row8608 : Integer.Sparse Key := [(key1309, 4), (key1350, 2), (key1417, -4), (key1471, -2), (key1539, 4), (key1566, -4), (key1895, 2), (key1902, -2)]

def row8609 : Integer.Sparse Key := [(key1309, 4), (key1350, 2), (key1417, -4), (key1471, -2), (key1539, 4), (key1566, -4), (key1895, 2), (key1902, -2)]

def row8610 : Integer.Sparse Key := [(key1309, 4), (key1350, 2), (key1417, -4), (key1471, -2), (key1539, 4), (key1566, -4), (key1895, 2), (key1902, -2)]

def row8611 : Integer.Sparse Key := [(key1309, 4), (key1350, 2), (key1417, -4), (key1471, -2), (key1539, 4), (key1566, -4), (key1895, 2), (key1902, -2)]

def row8612 : Integer.Sparse Key := [(key1309, 4), (key1350, 2), (key1417, -4), (key1471, -2), (key1539, 4), (key1566, -4), (key1895, 2), (key1902, -2)]

def row8613 : Integer.Sparse Key := [(key238, -6), (key250, 6), (key387, 6), (key408, -12), (key417, -6), (key437, 6), (key449, 6)]

def row8614 : Integer.Sparse Key := [(key238, -6), (key250, 6), (key387, 6), (key408, -12), (key417, -6), (key437, 6), (key449, 6)]

def row8615 : Integer.Sparse Key := [(key238, -6), (key250, 6), (key387, 6), (key408, -12), (key417, -6), (key437, 6), (key449, 6)]

def row8616 : Integer.Sparse Key := [(key238, -6), (key250, 6), (key387, 6), (key408, -12), (key417, -6), (key437, 6), (key449, 6)]

def row8617 : Integer.Sparse Key := [(key238, 2), (key250, -2), (key304, 2), (key318, -2), (key387, 2), (key396, 2), (key408, 2), (key417, 2), (key437, -4), (key441, -2), (key449, -2)]

def row8618 : Integer.Sparse Key := [(key238, 2), (key250, -2), (key304, 2), (key318, -2), (key387, 2), (key396, 2), (key408, 2), (key417, 2), (key437, -4), (key441, -2), (key449, -2)]

def row8619 : Integer.Sparse Key := [(key238, 2), (key250, -2), (key304, 2), (key318, -2), (key387, 2), (key396, 2), (key408, 2), (key417, 2), (key437, -4), (key441, -2), (key449, -2)]

def row8620 : Integer.Sparse Key := [(key238, 2), (key250, -2), (key304, 2), (key318, -2), (key387, 2), (key396, 2), (key408, 2), (key417, 2), (key437, -4), (key441, -2), (key449, -2)]

def row8621 : Integer.Sparse Key := [(key238, 2), (key250, -2), (key304, 2), (key318, -2), (key387, 2), (key396, 2), (key408, 2), (key417, 2), (key437, -4), (key441, -2), (key449, -2)]

def row8622 : Integer.Sparse Key := [(key238, 2), (key250, -2), (key304, 2), (key318, -2), (key387, 2), (key396, 2), (key408, 2), (key417, 2), (key437, -4), (key441, -2), (key449, -2)]

def row8623 : Integer.Sparse Key := [(key238, 2), (key250, -2), (key304, 2), (key318, -2), (key387, 2), (key396, 2), (key408, 2), (key417, 2), (key437, -4), (key441, -2), (key449, -2)]

def row8624 : Integer.Sparse Key := [(key238, 2), (key250, -2), (key304, 2), (key318, -2), (key387, 2), (key396, 2), (key408, 2), (key417, 2), (key437, -4), (key441, -2), (key449, -2)]

def row8625 : Integer.Sparse Key := [(key238, 2), (key250, -2), (key304, 2), (key318, -2), (key387, 2), (key396, 2), (key408, 2), (key417, 2), (key437, -4), (key441, -2), (key449, -2)]

def row8626 : Integer.Sparse Key := [(key238, 2), (key250, -2), (key304, 2), (key318, -2), (key387, 2), (key396, 2), (key408, 2), (key417, 2), (key437, -4), (key441, -2), (key449, -2)]

def row8627 : Integer.Sparse Key := [(key238, 2), (key250, -2), (key304, 2), (key318, -2), (key387, 2), (key396, 2), (key408, 2), (key417, 2), (key437, -4), (key441, -2), (key449, -2)]

def row8628 : Integer.Sparse Key := [(key238, 2), (key250, -2), (key304, 2), (key318, -2), (key387, 2), (key396, 2), (key408, 2), (key417, 2), (key437, -4), (key441, -2), (key449, -2)]

def row8629 : Integer.Sparse Key := [(key1309, 6), (key1350, -6), (key1417, 6), (key1471, -6), (key1615, 6), (key1680, -12), (key1917, 6)]

def row8630 : Integer.Sparse Key := [(key1309, 6), (key1350, -6), (key1417, 6), (key1471, -6), (key1615, 6), (key1680, -12), (key1917, 6)]

def row8631 : Integer.Sparse Key := [(key1309, 6), (key1350, -6), (key1417, 6), (key1471, -6), (key1615, 6), (key1680, -12), (key1917, 6)]

def row8632 : Integer.Sparse Key := [(key1309, 6), (key1350, -6), (key1417, 6), (key1471, -6), (key1615, 6), (key1680, -12), (key1917, 6)]

def row8633 : Integer.Sparse Key := [(key1309, -2), (key1350, 2), (key1417, -2), (key1471, 2), (key1539, -2), (key1566, -2), (key1615, -4), (key1680, 2), (key1895, 2), (key1902, 2), (key1917, 2)]

def row8634 : Integer.Sparse Key := [(key1309, -2), (key1350, 2), (key1417, -2), (key1471, 2), (key1539, -2), (key1566, -2), (key1615, -4), (key1680, 2), (key1895, 2), (key1902, 2), (key1917, 2)]

def row8635 : Integer.Sparse Key := [(key1309, -2), (key1350, 2), (key1417, -2), (key1471, 2), (key1539, -2), (key1566, -2), (key1615, -4), (key1680, 2), (key1895, 2), (key1902, 2), (key1917, 2)]

def row8636 : Integer.Sparse Key := [(key1309, -2), (key1350, 2), (key1417, -2), (key1471, 2), (key1539, -2), (key1566, -2), (key1615, -4), (key1680, 2), (key1895, 2), (key1902, 2), (key1917, 2)]

def row8637 : Integer.Sparse Key := [(key1309, -2), (key1350, 2), (key1417, -2), (key1471, 2), (key1539, -2), (key1566, -2), (key1615, -4), (key1680, 2), (key1895, 2), (key1902, 2), (key1917, 2)]

def row8638 : Integer.Sparse Key := [(key1309, -2), (key1350, 2), (key1417, -2), (key1471, 2), (key1539, -2), (key1566, -2), (key1615, -4), (key1680, 2), (key1895, 2), (key1902, 2), (key1917, 2)]

def row8639 : Integer.Sparse Key := [(key1309, -2), (key1350, 2), (key1417, -2), (key1471, 2), (key1539, -2), (key1566, -2), (key1615, -4), (key1680, 2), (key1895, 2), (key1902, 2), (key1917, 2)]

def row8640 : Integer.Sparse Key := [(key1309, -2), (key1350, 2), (key1417, -2), (key1471, 2), (key1539, -2), (key1566, -2), (key1615, -4), (key1680, 2), (key1895, 2), (key1902, 2), (key1917, 2)]

def row8641 : Integer.Sparse Key := [(key1309, -2), (key1350, 2), (key1417, -2), (key1471, 2), (key1539, -2), (key1566, -2), (key1615, -4), (key1680, 2), (key1895, 2), (key1902, 2), (key1917, 2)]

def row8642 : Integer.Sparse Key := [(key1309, -2), (key1350, 2), (key1417, -2), (key1471, 2), (key1539, -2), (key1566, -2), (key1615, -4), (key1680, 2), (key1895, 2), (key1902, 2), (key1917, 2)]

def row8643 : Integer.Sparse Key := [(key1309, -2), (key1350, 2), (key1417, -2), (key1471, 2), (key1539, -2), (key1566, -2), (key1615, -4), (key1680, 2), (key1895, 2), (key1902, 2), (key1917, 2)]

def row8644 : Integer.Sparse Key := [(key1309, -2), (key1350, 2), (key1417, -2), (key1471, 2), (key1539, -2), (key1566, -2), (key1615, -4), (key1680, 2), (key1895, 2), (key1902, 2), (key1917, 2)]

def row8645 : Integer.Sparse Key := [(key234, -6), (key246, 6), (key314, 6), (key404, -18), (key433, 12)]

def row8646 : Integer.Sparse Key := [(key234, -6), (key246, 6), (key314, 6), (key404, -18), (key433, 12)]

def row8647 : Integer.Sparse Key := [(key234, -6), (key246, 6), (key314, 6), (key404, -18), (key433, 12)]

def row8648 : Integer.Sparse Key := [(key234, -6), (key246, 6), (key314, 6), (key404, -18), (key433, 12)]

def row8649 : Integer.Sparse Key := [(key234, 2), (key246, -2), (key300, 2), (key314, -2), (key383, 4), (key404, 4), (key433, -8)]

def row8650 : Integer.Sparse Key := [(key234, 2), (key246, -2), (key300, 2), (key314, -2), (key383, 4), (key404, 4), (key433, -8)]

def row8651 : Integer.Sparse Key := [(key234, 2), (key246, -2), (key300, 2), (key314, -2), (key383, 4), (key404, 4), (key433, -8)]

def row8652 : Integer.Sparse Key := [(key234, 2), (key246, -2), (key300, 2), (key314, 2), (key404, 4), (key433, -8)]

def row8653 : Integer.Sparse Key := [(key234, 2), (key246, -2), (key300, 2), (key314, 2), (key404, 4), (key433, -8)]

def row8654 : Integer.Sparse Key := [(key234, 2), (key246, -2), (key300, 2), (key314, 2), (key404, 4), (key433, -8)]

def row8655 : Integer.Sparse Key := [(key234, 2), (key246, -2), (key300, 2), (key314, -2), (key383, 4), (key404, 4), (key433, -8)]

def row8656 : Integer.Sparse Key := [(key234, 2), (key246, -2), (key300, 2), (key314, -2), (key383, 4), (key404, 4), (key433, -8)]

def row8657 : Integer.Sparse Key := [(key234, 2), (key246, -2), (key300, 2), (key383, 2), (key404, 4), (key433, -8)]

def row8658 : Integer.Sparse Key := [(key234, 2), (key246, -2), (key300, 2), (key383, 2), (key404, 4), (key433, -8)]

def row8659 : Integer.Sparse Key := [(key234, 2), (key246, -2), (key300, 2), (key314, -2), (key383, 4), (key404, 4), (key433, -8)]

def row8660 : Integer.Sparse Key := [(key234, 2), (key246, -2), (key300, 2), (key314, -2), (key383, 4), (key404, 4), (key433, -8)]

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

def row8717 : Integer.Sparse Key := [(key2584, -6), (key2588, -12), (key2599, -6), (key2763, 6), (key2767, 12), (key2930, 6)]

def row8718 : Integer.Sparse Key := [(key2584, -6), (key2588, -12), (key2599, -6), (key2763, 6), (key2767, 12), (key2930, 6)]

def row8719 : Integer.Sparse Key := [(key2584, -6), (key2588, -12), (key2599, -6), (key2763, 6), (key2767, 12), (key2930, 6)]

def row8720 : Integer.Sparse Key := [(key2584, -6), (key2588, -12), (key2599, -6), (key2763, 6), (key2767, 12), (key2930, 6)]

def row8721 : Integer.Sparse Key := [(key2599, 6), (key2888, 12), (key2909, 6), (key2930, -6), (key2967, -12), (key2988, -6)]

def row8722 : Integer.Sparse Key := [(key2599, 6), (key2888, 12), (key2909, 6), (key2930, -6), (key2967, -12), (key2988, -6)]

def row8723 : Integer.Sparse Key := [(key2599, 6), (key2888, 12), (key2909, 6), (key2930, -6), (key2967, -12), (key2988, -6)]

def row8724 : Integer.Sparse Key := [(key2599, 6), (key2888, 12), (key2909, 6), (key2930, -6), (key2967, -12), (key2988, -6)]

def row8725 : Integer.Sparse Key := [(key1527, -6), (key1532, -12), (key1605, 6), (key1610, 6), (key1649, 6), (key1766, -6), (key1807, 6)]

def row8726 : Integer.Sparse Key := [(key1527, -6), (key1532, -12), (key1605, 6), (key1610, 6), (key1649, 6), (key1766, -6), (key1807, 6)]

def row8727 : Integer.Sparse Key := [(key1527, -6), (key1532, -12), (key1605, 6), (key1610, 6), (key1649, 6), (key1766, -6), (key1807, 6)]

def row8728 : Integer.Sparse Key := [(key1527, -6), (key1532, -12), (key1605, 6), (key1610, 6), (key1649, 6), (key1766, -6), (key1807, 6)]

def row8729 : Integer.Sparse Key := [(key1257, 6), (key1266, -6), (key1532, 6), (key1610, 6), (key1638, 6), (key1649, -12), (key1672, -6)]

def row8730 : Integer.Sparse Key := [(key1257, 6), (key1266, -6), (key1532, 6), (key1610, 6), (key1638, 6), (key1649, -12), (key1672, -6)]

def row8731 : Integer.Sparse Key := [(key1257, 6), (key1266, -6), (key1532, 6), (key1610, 6), (key1638, 6), (key1649, -12), (key1672, -6)]

def row8732 : Integer.Sparse Key := [(key1257, 6), (key1266, -6), (key1532, 6), (key1610, 6), (key1638, 6), (key1649, -12), (key1672, -6)]

def row8733 : Integer.Sparse Key := [(key2840, 6), (key2844, 6), (key2875, -12), (key2888, 6), (key2909, -6), (key2967, 6), (key2988, -6)]

def row8734 : Integer.Sparse Key := [(key2840, 6), (key2844, 6), (key2875, -12), (key2888, 6), (key2909, -6), (key2967, 6), (key2988, -6)]

def row8735 : Integer.Sparse Key := [(key2840, 6), (key2844, 6), (key2875, -12), (key2888, 6), (key2909, -6), (key2967, 6), (key2988, -6)]

def row8736 : Integer.Sparse Key := [(key2840, 6), (key2844, 6), (key2875, -12), (key2888, 6), (key2909, -6), (key2967, 6), (key2988, -6)]

def row8737 : Integer.Sparse Key := [(key2584, -6), (key2588, 6), (key2763, -6), (key2767, 6), (key2840, -12), (key2844, 6), (key2875, 6)]

def row8738 : Integer.Sparse Key := [(key2584, -6), (key2588, 6), (key2763, -6), (key2767, 6), (key2840, -12), (key2844, 6), (key2875, 6)]

def row8739 : Integer.Sparse Key := [(key2584, -6), (key2588, 6), (key2763, -6), (key2767, 6), (key2840, -12), (key2844, 6), (key2875, 6)]

def row8740 : Integer.Sparse Key := [(key2584, -6), (key2588, 6), (key2763, -6), (key2767, 6), (key2840, -12), (key2844, 6), (key2875, 6)]

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

def row8757 : Integer.Sparse Key := [(key2361, -6), (key2366, 6), (key2456, -12), (key2461, 6), (key2517, -6), (key2523, 12)]

def row8758 : Integer.Sparse Key := [(key2361, -6), (key2366, 6), (key2456, -12), (key2461, 6), (key2517, -6), (key2523, 12)]

def row8759 : Integer.Sparse Key := [(key2361, -6), (key2366, 6), (key2456, -12), (key2461, 6), (key2517, -6), (key2523, 12)]

def row8760 : Integer.Sparse Key := [(key2361, -6), (key2366, 6), (key2456, -12), (key2461, 6), (key2517, -6), (key2523, 12)]

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

def row8777 : Integer.Sparse Key := [(key2398, -6), (key2404, -12), (key2435, -6), (key2464, 6), (key2470, 6), (key2478, 6), (key2501, 6)]

def row8778 : Integer.Sparse Key := [(key2398, -6), (key2404, -12), (key2435, -6), (key2464, 6), (key2470, 6), (key2478, 6), (key2501, 6)]

def row8779 : Integer.Sparse Key := [(key2398, -6), (key2404, -12), (key2435, -6), (key2464, 6), (key2470, 6), (key2478, 6), (key2501, 6)]

def row8780 : Integer.Sparse Key := [(key2398, -6), (key2404, -12), (key2435, -6), (key2464, 6), (key2470, 6), (key2478, 6), (key2501, 6)]

def row8781 : Integer.Sparse Key := [(key2589, 6), (key2604, -6), (key2768, 6), (key2845, 6), (key2876, 6), (key2916, -12), (key2925, -6)]

def row8782 : Integer.Sparse Key := [(key2589, 6), (key2604, -6), (key2768, 6), (key2845, 6), (key2876, 6), (key2916, -12), (key2925, -6)]

def row8783 : Integer.Sparse Key := [(key2589, 6), (key2604, -6), (key2768, 6), (key2845, 6), (key2876, 6), (key2916, -12), (key2925, -6)]

def row8784 : Integer.Sparse Key := [(key2589, 6), (key2604, -6), (key2768, 6), (key2845, 6), (key2876, 6), (key2916, -12), (key2925, -6)]

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

def row8809 : Integer.Sparse Key := [(key2464, 6), (key2470, 6), (key2478, 6), (key2501, 6), (key2568, -12), (key2570, -6), (key2575, -6)]

def row8810 : Integer.Sparse Key := [(key2464, 6), (key2470, 6), (key2478, 6), (key2501, 6), (key2568, -12), (key2570, -6), (key2575, -6)]

def row8811 : Integer.Sparse Key := [(key2464, 6), (key2470, 6), (key2478, 6), (key2501, 6), (key2568, -12), (key2570, -6), (key2575, -6)]

def row8812 : Integer.Sparse Key := [(key2464, 6), (key2470, 6), (key2478, 6), (key2501, 6), (key2568, -12), (key2570, -6), (key2575, -6)]

def row8813 : Integer.Sparse Key := [(key2370, -6), (key2398, -6), (key2464, -12), (key2589, 6), (key2768, 6), (key2845, 6), (key2876, 6)]

def row8814 : Integer.Sparse Key := [(key2370, -4), (key2398, -4), (key2464, -4), (key2583, -2), (key2589, 6), (key2762, -2), (key2768, 6), (key2839, -8), (key2845, 6), (key2876, 6)]

def row8815 : Integer.Sparse Key := [(key2370, -2), (key2398, -2), (key2583, -4), (key2589, 6), (key2762, -4), (key2768, 6), (key2839, -12), (key2845, 6), (key2876, 6)]

def row8816 : Integer.Sparse Key := [(key2583, -6), (key2589, 6), (key2762, -6), (key2768, 6), (key2839, -12), (key2845, 6), (key2876, 6)]

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

def row8953 : Integer.Sparse Key := [(key2077, -6), (key2079, -12), (key2085, -6), (key2174, 6), (key2176, 12), (key2187, 6)]

def row8954 : Integer.Sparse Key := [(key2077, -6), (key2079, -12), (key2085, -6), (key2174, 6), (key2176, 12), (key2187, 6)]

def row8955 : Integer.Sparse Key := [(key2077, -6), (key2079, -12), (key2085, -6), (key2174, 6), (key2176, 12), (key2187, 6)]

def row8956 : Integer.Sparse Key := [(key2077, -6), (key2079, -12), (key2085, -6), (key2174, 6), (key2176, 12), (key2187, 6)]

def row8957 : Integer.Sparse Key := [(key2077, 2), (key2079, 4), (key2174, -2), (key2176, -4), (key2279, -4), (key2287, 4), (key2343, -2), (key2347, 2)]

def row8958 : Integer.Sparse Key := [(key2077, 2), (key2079, 4), (key2174, -2), (key2176, -4), (key2279, -4), (key2287, 4), (key2343, -2), (key2347, 2)]

def row8959 : Integer.Sparse Key := [(key2077, 2), (key2079, 4), (key2174, -2), (key2176, -4), (key2279, -4), (key2287, 4), (key2343, -2), (key2347, 2)]

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

def row8960 : Integer.Sparse Key := [(key2077, 2), (key2079, 4), (key2174, -2), (key2176, -4), (key2279, -4), (key2287, 4), (key2343, -2), (key2347, 2)]

def row8961 : Integer.Sparse Key := [(key2077, 2), (key2079, 4), (key2174, -2), (key2176, -4), (key2279, -4), (key2287, 4), (key2343, -2), (key2347, 2)]

def row8962 : Integer.Sparse Key := [(key2077, 2), (key2079, 4), (key2174, -2), (key2176, -4), (key2279, -4), (key2287, 4), (key2343, -2), (key2347, 2)]

def row8963 : Integer.Sparse Key := [(key2077, 2), (key2079, 4), (key2174, -2), (key2176, -4), (key2279, -4), (key2287, 4), (key2343, -2), (key2347, 2)]

def row8964 : Integer.Sparse Key := [(key2077, 2), (key2079, 4), (key2174, -2), (key2176, -4), (key2279, -4), (key2287, 4), (key2343, -2), (key2347, 2)]

def row8965 : Integer.Sparse Key := [(key2077, 2), (key2079, 4), (key2174, -2), (key2176, -4), (key2279, -4), (key2287, 4), (key2343, -2), (key2347, 2)]

def row8966 : Integer.Sparse Key := [(key2077, 2), (key2079, 4), (key2174, -2), (key2176, -4), (key2279, -4), (key2287, 4), (key2343, -2), (key2347, 2)]

def row8967 : Integer.Sparse Key := [(key2077, 2), (key2079, 4), (key2174, -2), (key2176, -4), (key2279, -4), (key2287, 4), (key2343, -2), (key2347, 2)]

def row8968 : Integer.Sparse Key := [(key2077, 2), (key2079, 4), (key2174, -2), (key2176, -4), (key2279, -4), (key2287, 4), (key2343, -2), (key2347, 2)]

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

def row8989 : Integer.Sparse Key := [(key2077, 2), (key2079, -2), (key2174, 2), (key2176, -2), (key2274, 2), (key2276, -4), (key2279, -2), (key2287, -2), (key2341, 2), (key2343, 2), (key2347, 2)]

def row8990 : Integer.Sparse Key := [(key2077, 2), (key2079, -2), (key2174, 2), (key2176, -2), (key2274, 2), (key2276, -4), (key2279, -2), (key2287, -2), (key2341, 2), (key2343, 2), (key2347, 2)]

def row8991 : Integer.Sparse Key := [(key2077, 2), (key2079, -2), (key2174, 2), (key2176, -2), (key2274, 2), (key2276, -4), (key2279, -2), (key2287, -2), (key2341, 2), (key2343, 2), (key2347, 2)]

def row8992 : Integer.Sparse Key := [(key2077, 2), (key2079, -2), (key2174, 2), (key2176, -2), (key2274, 2), (key2276, -4), (key2279, -2), (key2287, -2), (key2341, 2), (key2343, 2), (key2347, 2)]

def row8993 : Integer.Sparse Key := [(key2077, 2), (key2079, -2), (key2174, 2), (key2176, -2), (key2274, 2), (key2276, -4), (key2279, -2), (key2287, -2), (key2341, 2), (key2343, 2), (key2347, 2)]

def row8994 : Integer.Sparse Key := [(key2077, 2), (key2079, -2), (key2174, 2), (key2176, -2), (key2274, 2), (key2276, -4), (key2279, -2), (key2287, -2), (key2341, 2), (key2343, 2), (key2347, 2)]

def row8995 : Integer.Sparse Key := [(key2077, 2), (key2079, -2), (key2174, 2), (key2176, -2), (key2274, 2), (key2276, -4), (key2279, -2), (key2287, -2), (key2341, 2), (key2343, 2), (key2347, 2)]

def row8996 : Integer.Sparse Key := [(key2077, 2), (key2079, -2), (key2174, 2), (key2176, -2), (key2274, 2), (key2276, -4), (key2279, -2), (key2287, -2), (key2341, 2), (key2343, 2), (key2347, 2)]

def row8997 : Integer.Sparse Key := [(key2077, 2), (key2079, -2), (key2174, 2), (key2176, -2), (key2274, 2), (key2276, -4), (key2279, -2), (key2287, -2), (key2341, 2), (key2343, 2), (key2347, 2)]

def row8998 : Integer.Sparse Key := [(key2077, 2), (key2079, -2), (key2174, 2), (key2176, -2), (key2274, 2), (key2276, -4), (key2279, -2), (key2287, -2), (key2341, 2), (key2343, 2), (key2347, 2)]

def row8999 : Integer.Sparse Key := [(key2077, 2), (key2079, -2), (key2174, 2), (key2176, -2), (key2274, 2), (key2276, -4), (key2279, -2), (key2287, -2), (key2341, 2), (key2343, 2), (key2347, 2)]

def row9000 : Integer.Sparse Key := [(key2077, 2), (key2079, -2), (key2174, 2), (key2176, -2), (key2274, 2), (key2276, -4), (key2279, -2), (key2287, -2), (key2341, 2), (key2343, 2), (key2347, 2)]

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

def row9113 : Integer.Sparse Key := [(key1015, 6), (key1071, -6), (key1123, 12), (key1150, -12), (key1235, 6), (key1242, -6)]

def row9114 : Integer.Sparse Key := [(key1015, 6), (key1071, -6), (key1123, 12), (key1150, -12), (key1235, 6), (key1242, -6)]

def row9115 : Integer.Sparse Key := [(key1015, 6), (key1071, -6), (key1123, 12), (key1150, -12), (key1235, 6), (key1242, -6)]

def row9116 : Integer.Sparse Key := [(key1015, 6), (key1071, -6), (key1123, 12), (key1150, -12), (key1235, 6), (key1242, -6)]

def row9117 : Integer.Sparse Key := [(key43, -6), (key48, -12), (key74, -6), (key100, 6), (key105, 6), (key115, 6), (key137, 6)]

def row9118 : Integer.Sparse Key := [(key43, -6), (key48, -12), (key74, -6), (key100, 6), (key105, 6), (key115, 6), (key137, 6)]

def row9119 : Integer.Sparse Key := [(key43, -6), (key48, -12), (key74, -6), (key100, 6), (key105, 6), (key115, 6), (key137, 6)]

def row9120 : Integer.Sparse Key := [(key43, -6), (key48, -12), (key74, -6), (key100, 6), (key105, 6), (key115, 6), (key137, 6)]

def row9121 : Integer.Sparse Key := [(key212, 6), (key218, -6), (key381, 6), (key432, 6), (key460, 6), (key486, -12), (key490, -6)]

def row9122 : Integer.Sparse Key := [(key212, 6), (key218, -6), (key381, 6), (key432, 6), (key460, 6), (key486, -12), (key490, -6)]

def row9123 : Integer.Sparse Key := [(key212, 6), (key218, -6), (key381, 6), (key432, 6), (key460, 6), (key486, -12), (key490, -6)]

def row9124 : Integer.Sparse Key := [(key212, 6), (key218, -6), (key381, 6), (key432, 6), (key460, 6), (key486, -12), (key490, -6)]

def row9125 : Integer.Sparse Key := [(key1106, 6), (key1114, 6), (key1123, 6), (key1150, 6), (key1232, -12), (key1235, -6), (key1242, -6)]

def row9126 : Integer.Sparse Key := [(key1106, 6), (key1114, 6), (key1123, 6), (key1150, 6), (key1232, -12), (key1235, -6), (key1242, -6)]

def row9127 : Integer.Sparse Key := [(key1106, 6), (key1114, 6), (key1123, 6), (key1150, 6), (key1232, -12), (key1235, -6), (key1242, -6)]

def row9128 : Integer.Sparse Key := [(key1106, 6), (key1114, 6), (key1123, 6), (key1150, 6), (key1232, -12), (key1235, -6), (key1242, -6)]

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

def row9257 : Integer.Sparse Key := [(key2584, 2), (key2588, 4), (key2763, -2), (key2767, -4), (key2888, -4), (key2909, -2), (key2967, 4), (key2988, 2)]

def row9258 : Integer.Sparse Key := [(key2584, 2), (key2588, 4), (key2763, -2), (key2767, -4), (key2888, -4), (key2909, -2), (key2967, 4), (key2988, 2)]

def row9259 : Integer.Sparse Key := [(key2584, 2), (key2588, 4), (key2763, -2), (key2767, -4), (key2888, -4), (key2909, -2), (key2967, 4), (key2988, 2)]

def row9260 : Integer.Sparse Key := [(key2584, 2), (key2588, 4), (key2763, -2), (key2767, -4), (key2888, -4), (key2909, -2), (key2967, 4), (key2988, 2)]

def row9261 : Integer.Sparse Key := [(key2584, 2), (key2588, 4), (key2763, -2), (key2767, -4), (key2888, -4), (key2909, -2), (key2967, 4), (key2988, 2)]

def row9262 : Integer.Sparse Key := [(key2584, 2), (key2588, 4), (key2763, -2), (key2767, -4), (key2888, -4), (key2909, -2), (key2967, 4), (key2988, 2)]

def row9263 : Integer.Sparse Key := [(key2584, 2), (key2588, 4), (key2763, -2), (key2767, -4), (key2888, -4), (key2909, -2), (key2967, 4), (key2988, 2)]

def row9264 : Integer.Sparse Key := [(key2584, 2), (key2588, 4), (key2763, -2), (key2767, -4), (key2888, -4), (key2909, -2), (key2967, 4), (key2988, 2)]

def row9265 : Integer.Sparse Key := [(key2584, 2), (key2588, 4), (key2763, -2), (key2767, -4), (key2888, -4), (key2909, -2), (key2967, 4), (key2988, 2)]

def row9266 : Integer.Sparse Key := [(key2584, 2), (key2588, 4), (key2763, -2), (key2767, -4), (key2888, -4), (key2909, -2), (key2967, 4), (key2988, 2)]

def row9267 : Integer.Sparse Key := [(key2584, 2), (key2588, 4), (key2763, -2), (key2767, -4), (key2888, -4), (key2909, -2), (key2967, 4), (key2988, 2)]

def row9268 : Integer.Sparse Key := [(key2584, 2), (key2588, 4), (key2763, -2), (key2767, -4), (key2888, -4), (key2909, -2), (key2967, 4), (key2988, 2)]

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

def row9281 : Integer.Sparse Key := [(key2584, 2), (key2588, -2), (key2763, 2), (key2767, -2), (key2840, 2), (key2844, -4), (key2875, 2), (key2888, -2), (key2909, 2), (key2967, -2), (key2988, 2)]

def row9282 : Integer.Sparse Key := [(key2584, 2), (key2588, -2), (key2763, 2), (key2767, -2), (key2840, 2), (key2844, -4), (key2875, 2), (key2888, -2), (key2909, 2), (key2967, -2), (key2988, 2)]

def row9283 : Integer.Sparse Key := [(key2584, 2), (key2588, -2), (key2763, 2), (key2767, -2), (key2840, 2), (key2844, -4), (key2875, 2), (key2888, -2), (key2909, 2), (key2967, -2), (key2988, 2)]

def row9284 : Integer.Sparse Key := [(key2584, 2), (key2588, -2), (key2763, 2), (key2767, -2), (key2840, 2), (key2844, -4), (key2875, 2), (key2888, -2), (key2909, 2), (key2967, -2), (key2988, 2)]

def row9285 : Integer.Sparse Key := [(key2584, 2), (key2588, -2), (key2763, 2), (key2767, -2), (key2840, 2), (key2844, -4), (key2875, 2), (key2888, -2), (key2909, 2), (key2967, -2), (key2988, 2)]

def row9286 : Integer.Sparse Key := [(key2584, 2), (key2588, -2), (key2763, 2), (key2767, -2), (key2840, 2), (key2844, -4), (key2875, 2), (key2888, -2), (key2909, 2), (key2967, -2), (key2988, 2)]

def row9287 : Integer.Sparse Key := [(key2584, 2), (key2588, -2), (key2763, 2), (key2767, -2), (key2840, 2), (key2844, -4), (key2875, 2), (key2888, -2), (key2909, 2), (key2967, -2), (key2988, 2)]

def row9288 : Integer.Sparse Key := [(key2584, 2), (key2588, -2), (key2763, 2), (key2767, -2), (key2840, 2), (key2844, -4), (key2875, 2), (key2888, -2), (key2909, 2), (key2967, -2), (key2988, 2)]

def row9289 : Integer.Sparse Key := [(key2584, 2), (key2588, -2), (key2763, 2), (key2767, -2), (key2840, 2), (key2844, -4), (key2875, 2), (key2888, -2), (key2909, 2), (key2967, -2), (key2988, 2)]

def row9290 : Integer.Sparse Key := [(key2584, 2), (key2588, -2), (key2763, 2), (key2767, -2), (key2840, 2), (key2844, -4), (key2875, 2), (key2888, -2), (key2909, 2), (key2967, -2), (key2988, 2)]

def row9291 : Integer.Sparse Key := [(key2584, 2), (key2588, -2), (key2763, 2), (key2767, -2), (key2840, 2), (key2844, -4), (key2875, 2), (key2888, -2), (key2909, 2), (key2967, -2), (key2988, 2)]

def row9292 : Integer.Sparse Key := [(key2584, 2), (key2588, -2), (key2763, 2), (key2767, -2), (key2840, 2), (key2844, -4), (key2875, 2), (key2888, -2), (key2909, 2), (key2967, -2), (key2988, 2)]

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

def row9421 : Integer.Sparse Key := [(key2610, -6), (key2626, -12), (key2635, -6), (key2665, 6), (key2780, 12), (key2789, 6)]

def row9422 : Integer.Sparse Key := [(key2610, -6), (key2626, -12), (key2635, -6), (key2665, 6), (key2780, 12), (key2789, 6)]

def row9423 : Integer.Sparse Key := [(key2610, -6), (key2626, -12), (key2635, -6), (key2665, 6), (key2780, 12), (key2789, 6)]

def row9424 : Integer.Sparse Key := [(key2610, -6), (key2626, -12), (key2635, -6), (key2665, 6), (key2780, 12), (key2789, 6)]

def row9425 : Integer.Sparse Key := [(key2610, 6), (key2665, -6), (key2700, -12), (key2721, -6), (key2803, 12), (key2824, 6)]

def row9426 : Integer.Sparse Key := [(key2610, 6), (key2665, -6), (key2700, -12), (key2721, -6), (key2803, 12), (key2824, 6)]

def row9427 : Integer.Sparse Key := [(key2610, 6), (key2665, -6), (key2700, -12), (key2721, -6), (key2803, 12), (key2824, 6)]

def row9428 : Integer.Sparse Key := [(key2610, 6), (key2665, -6), (key2700, -12), (key2721, -6), (key2803, 12), (key2824, 6)]

def row9429 : Integer.Sparse Key := [(key1388, -6), (key1421, 6), (key1543, -12), (key1553, -6), (key1570, 6), (key1619, 6), (key1621, 6)]

def row9430 : Integer.Sparse Key := [(key1388, -6), (key1421, 6), (key1543, -12), (key1553, -6), (key1570, 6), (key1619, 6), (key1621, 6)]

def row9431 : Integer.Sparse Key := [(key1388, -6), (key1421, 6), (key1543, -12), (key1553, -6), (key1570, 6), (key1619, 6), (key1621, 6)]

def row9432 : Integer.Sparse Key := [(key1388, -6), (key1421, 6), (key1543, -12), (key1553, -6), (key1570, 6), (key1619, 6), (key1621, 6)]

def row9433 : Integer.Sparse Key := [(key1293, -6), (key1313, 6), (key1543, 6), (key1570, -12), (key1590, -6), (key1619, 6), (key1630, 6)]

def row9434 : Integer.Sparse Key := [(key1293, -6), (key1313, 6), (key1543, 6), (key1570, -12), (key1590, -6), (key1619, 6), (key1630, 6)]

def row9435 : Integer.Sparse Key := [(key1293, -6), (key1313, 6), (key1543, 6), (key1570, -12), (key1590, -6), (key1619, 6), (key1630, 6)]

def row9436 : Integer.Sparse Key := [(key1293, -6), (key1313, 6), (key1543, 6), (key1570, -12), (key1590, -6), (key1619, 6), (key1630, 6)]

def row9437 : Integer.Sparse Key := [(key2700, 6), (key2721, -6), (key2803, 6), (key2824, -6), (key2853, 6), (key2855, 6), (key2865, -12)]

def row9438 : Integer.Sparse Key := [(key2700, 6), (key2721, -6), (key2803, 6), (key2824, -6), (key2853, 6), (key2855, 6), (key2865, -12)]

def row9439 : Integer.Sparse Key := [(key2700, 6), (key2721, -6), (key2803, 6), (key2824, -6), (key2853, 6), (key2855, 6), (key2865, -12)]

def row9440 : Integer.Sparse Key := [(key2700, 6), (key2721, -6), (key2803, 6), (key2824, -6), (key2853, 6), (key2855, 6), (key2865, -12)]

def row9441 : Integer.Sparse Key := [(key2626, 6), (key2635, -6), (key2780, 6), (key2789, -6), (key2853, 6), (key2855, -12), (key2865, 6)]

def row9442 : Integer.Sparse Key := [(key2626, 6), (key2635, -6), (key2780, 6), (key2789, -6), (key2853, 6), (key2855, -12), (key2865, 6)]

def row9443 : Integer.Sparse Key := [(key2626, 6), (key2635, -6), (key2780, 6), (key2789, -6), (key2853, 6), (key2855, -12), (key2865, 6)]

def row9444 : Integer.Sparse Key := [(key2626, 6), (key2635, -6), (key2780, 6), (key2789, -6), (key2853, 6), (key2855, -12), (key2865, 6)]

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

def row9549 : Integer.Sparse Key := [(key998, 4), (key1006, 2), (key1033, -12), (key1041, -6), (key1076, -6), (key1111, 4), (key1155, 2), (key1190, 4), (key1193, 4), (key1212, 4)]

def row9550 : Integer.Sparse Key := [(key998, 4), (key1006, 2), (key1033, -12), (key1041, -6), (key1076, -6), (key1111, 4), (key1155, 2), (key1190, 4), (key1193, 4), (key1212, 4)]

def row9551 : Integer.Sparse Key := [(key998, 4), (key1006, 2), (key1033, -12), (key1041, -6), (key1076, -6), (key1111, 4), (key1155, 2), (key1190, 4), (key1193, 4), (key1212, 4)]

def row9552 : Integer.Sparse Key := [(key998, 4), (key1006, 2), (key1033, -12), (key1041, -6), (key1076, -6), (key1111, 4), (key1155, 2), (key1190, 4), (key1193, 4), (key1212, 4)]

def row9553 : Integer.Sparse Key := [(key998, 4), (key1006, 2), (key1033, -12), (key1041, -6), (key1076, -6), (key1111, 4), (key1155, 2), (key1190, 4), (key1193, 4), (key1212, 4)]

def row9554 : Integer.Sparse Key := [(key998, 4), (key1006, 2), (key1033, -12), (key1041, -6), (key1076, -6), (key1111, 4), (key1155, 2), (key1190, 4), (key1193, 4), (key1212, 4)]

def row9555 : Integer.Sparse Key := [(key998, 4), (key1006, 2), (key1033, -12), (key1041, -6), (key1076, -6), (key1111, 4), (key1155, 2), (key1190, 4), (key1193, 4), (key1212, 4)]

def row9556 : Integer.Sparse Key := [(key998, 4), (key1006, 2), (key1033, -12), (key1041, -6), (key1076, -6), (key1111, 4), (key1155, 2), (key1190, 4), (key1193, 4), (key1212, 4)]

def row9557 : Integer.Sparse Key := [(key998, 4), (key1006, 2), (key1033, -12), (key1041, -6), (key1076, -6), (key1111, 4), (key1155, 2), (key1190, 4), (key1193, 4), (key1212, 4)]

def row9558 : Integer.Sparse Key := [(key998, 4), (key1006, 2), (key1033, -12), (key1041, -6), (key1076, -6), (key1111, 4), (key1155, 2), (key1190, 4), (key1193, 4), (key1212, 4)]

def row9559 : Integer.Sparse Key := [(key998, 4), (key1006, 2), (key1033, -12), (key1041, -6), (key1076, -6), (key1111, 4), (key1155, 2), (key1190, 4), (key1193, 4), (key1212, 4)]

def row9560 : Integer.Sparse Key := [(key998, 4), (key1006, 2), (key1033, -12), (key1041, -6), (key1076, -6), (key1111, 4), (key1155, 2), (key1190, 4), (key1193, 4), (key1212, 4)]

def row9561 : Integer.Sparse Key := [(key998, 4), (key1019, 2), (key1033, 4), (key1076, 2), (key1111, -12), (key1127, -6), (key1155, -6), (key1190, 4), (key1199, 4), (key1212, 4)]

def row9562 : Integer.Sparse Key := [(key998, 4), (key1019, 2), (key1033, 4), (key1076, 2), (key1111, -12), (key1127, -6), (key1155, -6), (key1190, 4), (key1199, 4), (key1212, 4)]

def row9563 : Integer.Sparse Key := [(key998, 4), (key1019, 2), (key1033, 4), (key1076, 2), (key1111, -12), (key1127, -6), (key1155, -6), (key1190, 4), (key1199, 4), (key1212, 4)]

def row9564 : Integer.Sparse Key := [(key998, 4), (key1019, 2), (key1033, 4), (key1076, 2), (key1111, -12), (key1127, -6), (key1155, -6), (key1190, 4), (key1199, 4), (key1212, 4)]

def row9565 : Integer.Sparse Key := [(key998, 4), (key1019, 2), (key1033, 4), (key1076, 2), (key1111, -12), (key1127, -6), (key1155, -6), (key1190, 4), (key1199, 4), (key1212, 4)]

def row9566 : Integer.Sparse Key := [(key998, 4), (key1019, 2), (key1033, 4), (key1076, 2), (key1111, -12), (key1127, -6), (key1155, -6), (key1190, 4), (key1199, 4), (key1212, 4)]

def row9567 : Integer.Sparse Key := [(key998, 4), (key1019, 2), (key1033, 4), (key1076, 2), (key1111, -12), (key1127, -6), (key1155, -6), (key1190, 4), (key1199, 4), (key1212, 4)]

def row9568 : Integer.Sparse Key := [(key998, 4), (key1019, 2), (key1033, 4), (key1076, 2), (key1111, -12), (key1127, -6), (key1155, -6), (key1190, 4), (key1199, 4), (key1212, 4)]

def row9569 : Integer.Sparse Key := [(key998, 4), (key1019, 2), (key1033, 4), (key1076, 2), (key1111, -12), (key1127, -6), (key1155, -6), (key1190, 4), (key1199, 4), (key1212, 4)]

def row9570 : Integer.Sparse Key := [(key998, 4), (key1019, 2), (key1033, 4), (key1076, 2), (key1111, -12), (key1127, -6), (key1155, -6), (key1190, 4), (key1199, 4), (key1212, 4)]

def row9571 : Integer.Sparse Key := [(key998, 4), (key1019, 2), (key1033, 4), (key1076, 2), (key1111, -12), (key1127, -6), (key1155, -6), (key1190, 4), (key1199, 4), (key1212, 4)]

def row9572 : Integer.Sparse Key := [(key998, 4), (key1019, 2), (key1033, 4), (key1076, 2), (key1111, -12), (key1127, -6), (key1155, -6), (key1190, 4), (key1199, 4), (key1212, 4)]

def row9573 : Integer.Sparse Key := [(key2615, -6), (key2631, 2), (key2639, 4), (key2705, 2), (key2725, 4), (key2808, -6), (key2828, -12), (key2859, 4), (key2869, 4), (key2879, 4)]

def row9574 : Integer.Sparse Key := [(key2615, -6), (key2631, 2), (key2639, 4), (key2705, 2), (key2725, 4), (key2808, -6), (key2828, -12), (key2859, 4), (key2869, 4), (key2879, 4)]

def row9575 : Integer.Sparse Key := [(key2615, -6), (key2631, 2), (key2639, 4), (key2705, 2), (key2725, 4), (key2808, -6), (key2828, -12), (key2859, 4), (key2869, 4), (key2879, 4)]

def row9576 : Integer.Sparse Key := [(key2615, -6), (key2631, 2), (key2639, 4), (key2705, 2), (key2725, 4), (key2808, -6), (key2828, -12), (key2859, 4), (key2869, 4), (key2879, 4)]

def row9577 : Integer.Sparse Key := [(key2615, -6), (key2631, 2), (key2639, 4), (key2705, 2), (key2725, 4), (key2808, -6), (key2828, -12), (key2859, 4), (key2869, 4), (key2879, 4)]

def row9578 : Integer.Sparse Key := [(key2615, -6), (key2631, 2), (key2639, 4), (key2705, 2), (key2725, 4), (key2808, -6), (key2828, -12), (key2859, 4), (key2869, 4), (key2879, 4)]

def row9579 : Integer.Sparse Key := [(key2615, -6), (key2631, 2), (key2639, 4), (key2705, 2), (key2725, 4), (key2808, -6), (key2828, -12), (key2859, 4), (key2869, 4), (key2879, 4)]

def row9580 : Integer.Sparse Key := [(key2615, -6), (key2631, 2), (key2639, 4), (key2705, 2), (key2725, 4), (key2808, -6), (key2828, -12), (key2859, 4), (key2869, 4), (key2879, 4)]

def row9581 : Integer.Sparse Key := [(key2615, -6), (key2631, 2), (key2639, 4), (key2705, 2), (key2725, 4), (key2808, -6), (key2828, -12), (key2859, 4), (key2869, 4), (key2879, 4)]

def row9582 : Integer.Sparse Key := [(key2615, -6), (key2631, 2), (key2639, 4), (key2705, 2), (key2725, 4), (key2808, -6), (key2828, -12), (key2859, 4), (key2869, 4), (key2879, 4)]

def row9583 : Integer.Sparse Key := [(key2615, -6), (key2631, 2), (key2639, 4), (key2705, 2), (key2725, 4), (key2808, -6), (key2828, -12), (key2859, 4), (key2869, 4), (key2879, 4)]

def row9584 : Integer.Sparse Key := [(key2615, -6), (key2631, 2), (key2639, 4), (key2705, 2), (key2725, 4), (key2808, -6), (key2828, -12), (key2859, 4), (key2869, 4), (key2879, 4)]

def row9585 : Integer.Sparse Key := [(key2615, 2), (key2631, -6), (key2639, 4), (key2670, 2), (key2725, 4), (key2785, -6), (key2793, 4), (key2828, 4), (key2869, -12), (key2879, 4)]

def row9586 : Integer.Sparse Key := [(key2615, 2), (key2631, -6), (key2639, 4), (key2670, 2), (key2725, 4), (key2785, -6), (key2793, 4), (key2828, 4), (key2869, -12), (key2879, 4)]

def row9587 : Integer.Sparse Key := [(key2615, 2), (key2631, -6), (key2639, 4), (key2670, 2), (key2725, 4), (key2785, -6), (key2793, 4), (key2828, 4), (key2869, -12), (key2879, 4)]

def row9588 : Integer.Sparse Key := [(key2615, 2), (key2631, -6), (key2639, 4), (key2670, 2), (key2725, 4), (key2785, -6), (key2793, 4), (key2828, 4), (key2869, -12), (key2879, 4)]

def row9589 : Integer.Sparse Key := [(key2615, 2), (key2631, -6), (key2639, 4), (key2670, 2), (key2725, 4), (key2785, -6), (key2793, 4), (key2828, 4), (key2869, -12), (key2879, 4)]

def row9590 : Integer.Sparse Key := [(key2615, 2), (key2631, -6), (key2639, 4), (key2670, 2), (key2725, 4), (key2785, -6), (key2793, 4), (key2828, 4), (key2869, -12), (key2879, 4)]

def row9591 : Integer.Sparse Key := [(key2615, 2), (key2631, -6), (key2639, 4), (key2670, 2), (key2725, 4), (key2785, -6), (key2793, 4), (key2828, 4), (key2869, -12), (key2879, 4)]

def row9592 : Integer.Sparse Key := [(key2615, 2), (key2631, -6), (key2639, 4), (key2670, 2), (key2725, 4), (key2785, -6), (key2793, 4), (key2828, 4), (key2869, -12), (key2879, 4)]

def row9593 : Integer.Sparse Key := [(key2615, 2), (key2631, -6), (key2639, 4), (key2670, 2), (key2725, 4), (key2785, -6), (key2793, 4), (key2828, 4), (key2869, -12), (key2879, 4)]

def row9594 : Integer.Sparse Key := [(key2615, 2), (key2631, -6), (key2639, 4), (key2670, 2), (key2725, 4), (key2785, -6), (key2793, 4), (key2828, 4), (key2869, -12), (key2879, 4)]

def row9595 : Integer.Sparse Key := [(key2615, 2), (key2631, -6), (key2639, 4), (key2670, 2), (key2725, 4), (key2785, -6), (key2793, 4), (key2828, 4), (key2869, -12), (key2879, 4)]

def row9596 : Integer.Sparse Key := [(key2615, 2), (key2631, -6), (key2639, 4), (key2670, 2), (key2725, 4), (key2785, -6), (key2793, 4), (key2828, 4), (key2869, -12), (key2879, 4)]

def row9597 : Integer.Sparse Key := [(key2402, -12), (key2408, -6), (key2439, -6), (key2591, 4), (key2596, 2), (key2847, 4), (key2878, 4), (key2884, 4), (key3020, 2), (key3029, 4)]

def row9598 : Integer.Sparse Key := [(key2402, -12), (key2408, -6), (key2439, -6), (key2591, 4), (key2596, 2), (key2847, 4), (key2878, 4), (key2884, 4), (key3020, 2), (key3029, 4)]

def row9599 : Integer.Sparse Key := [(key2402, -12), (key2408, -6), (key2439, -6), (key2591, 4), (key2596, 2), (key2847, 4), (key2878, 4), (key2884, 4), (key3020, 2), (key3029, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block99
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row9600 : Integer.Sparse Key := [(key2402, -12), (key2408, -6), (key2439, -6), (key2591, 4), (key2596, 2), (key2847, 4), (key2878, 4), (key2884, 4), (key3020, 2), (key3029, 4)]

def row9601 : Integer.Sparse Key := [(key2402, -12), (key2408, -6), (key2439, -6), (key2591, 4), (key2596, 2), (key2847, 4), (key2878, 4), (key2884, 4), (key3020, 2), (key3029, 4)]

def row9602 : Integer.Sparse Key := [(key2402, -12), (key2408, -6), (key2439, -6), (key2591, 4), (key2596, 2), (key2847, 4), (key2878, 4), (key2884, 4), (key3020, 2), (key3029, 4)]

def row9603 : Integer.Sparse Key := [(key2402, -12), (key2408, -6), (key2439, -6), (key2591, 4), (key2596, 2), (key2847, 4), (key2878, 4), (key2884, 4), (key3020, 2), (key3029, 4)]

def row9604 : Integer.Sparse Key := [(key2402, -12), (key2408, -6), (key2439, -6), (key2591, 4), (key2596, 2), (key2847, 4), (key2878, 4), (key2884, 4), (key3020, 2), (key3029, 4)]

def row9605 : Integer.Sparse Key := [(key2402, -12), (key2408, -6), (key2439, -6), (key2591, 4), (key2596, 2), (key2847, 4), (key2878, 4), (key2884, 4), (key3020, 2), (key3029, 4)]

def row9606 : Integer.Sparse Key := [(key2402, -12), (key2408, -6), (key2439, -6), (key2591, 4), (key2596, 2), (key2847, 4), (key2878, 4), (key2884, 4), (key3020, 2), (key3029, 4)]

def row9607 : Integer.Sparse Key := [(key2402, -12), (key2408, -6), (key2439, -6), (key2591, 4), (key2596, 2), (key2847, 4), (key2878, 4), (key2884, 4), (key3020, 2), (key3029, 4)]

def row9608 : Integer.Sparse Key := [(key2402, -12), (key2408, -6), (key2439, -6), (key2591, 4), (key2596, 2), (key2847, 4), (key2878, 4), (key2884, 4), (key3020, 2), (key3029, 4)]

def row9609 : Integer.Sparse Key := [(key2374, 4), (key2391, 2), (key2468, -12), (key2481, -6), (key2505, -6), (key2770, 4), (key2878, 4), (key2926, 4), (key3006, 2), (key3029, 4)]

def row9610 : Integer.Sparse Key := [(key2374, 4), (key2391, 2), (key2468, -12), (key2481, -6), (key2505, -6), (key2770, 4), (key2878, 4), (key2926, 4), (key3006, 2), (key3029, 4)]

def row9611 : Integer.Sparse Key := [(key2374, 4), (key2391, 2), (key2468, -12), (key2481, -6), (key2505, -6), (key2770, 4), (key2878, 4), (key2926, 4), (key3006, 2), (key3029, 4)]

def row9612 : Integer.Sparse Key := [(key2402, 4), (key2439, 2), (key2468, -12), (key2481, -6), (key2505, -6), (key2591, 4), (key2605, 2), (key2878, 4), (key2926, 4), (key3029, 4)]

def row9613 : Integer.Sparse Key := [(key2402, 4), (key2439, 2), (key2468, -12), (key2481, -6), (key2505, -6), (key2591, 4), (key2605, 2), (key2878, 4), (key2926, 4), (key3029, 4)]

def row9614 : Integer.Sparse Key := [(key2402, 4), (key2439, 2), (key2468, -12), (key2481, -6), (key2505, -6), (key2591, 4), (key2605, 2), (key2878, 4), (key2926, 4), (key3029, 4)]

def row9615 : Integer.Sparse Key := [(key2374, 2), (key2391, 2), (key2402, 2), (key2439, 2), (key2468, -12), (key2481, -6), (key2505, -6), (key2535, 2), (key2542, 4), (key2553, 4), (key2591, 2), (key2770, 2), (key2878, 2)]

def row9616 : Integer.Sparse Key := [(key2374, 2), (key2391, 2), (key2402, 2), (key2439, 2), (key2468, -12), (key2481, -6), (key2505, -6), (key2535, 2), (key2542, 4), (key2553, 4), (key2591, 2), (key2770, 2), (key2878, 2)]

def row9617 : Integer.Sparse Key := [(key2374, 2), (key2391, 2), (key2402, 2), (key2439, 2), (key2468, -12), (key2481, -6), (key2505, -6), (key2535, 2), (key2542, 4), (key2553, 4), (key2591, 2), (key2770, 2), (key2878, 2)]

def row9618 : Integer.Sparse Key := [(key2374, 2), (key2391, 2), (key2402, 2), (key2439, 2), (key2468, -12), (key2481, -6), (key2505, -6), (key2535, 2), (key2542, 4), (key2553, 4), (key2591, 2), (key2770, 2), (key2878, 2)]

def row9619 : Integer.Sparse Key := [(key2374, 2), (key2391, 2), (key2402, 2), (key2439, 2), (key2468, -12), (key2481, -6), (key2505, -6), (key2535, 2), (key2542, 4), (key2553, 4), (key2591, 2), (key2770, 2), (key2878, 2)]

def row9620 : Integer.Sparse Key := [(key2374, 2), (key2391, 2), (key2402, 2), (key2439, 2), (key2468, -12), (key2481, -6), (key2505, -6), (key2535, 2), (key2542, 4), (key2553, 4), (key2591, 2), (key2770, 2), (key2878, 2)]

def row9621 : Integer.Sparse Key := [(key2612, -2), (key2616, -2), (key2621, -2), (key2632, 2), (key2640, 2), (key2644, 2), (key2706, 2), (key2726, 2), (key2732, 2), (key2809, -4), (key2829, -4), (key2835, -4), (key2860, 2), (key2870, 2), (key2885, 2), (key3012, -2), (key3017, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

def row9622 : Integer.Sparse Key := [(key2612, -2), (key2616, -2), (key2618, -2), (key2632, 2), (key2640, 2), (key2644, 2), (key2706, 2), (key2726, 2), (key2732, 2), (key2809, -4), (key2829, -4), (key2835, -4), (key2860, 2), (key2870, 2), (key2885, 2), (key3012, -2), (key3017, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

def row9623 : Integer.Sparse Key := [(key2612, -2), (key2616, -2), (key2618, -2), (key2632, 2), (key2640, 2), (key2644, 2), (key2706, 2), (key2726, 2), (key2732, 2), (key2809, -4), (key2829, -4), (key2835, -4), (key2860, 2), (key2870, 2), (key2885, 2), (key3012, -2), (key3017, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

def row9624 : Integer.Sparse Key := [(key2612, -2), (key2616, -2), (key2621, -2), (key2632, 2), (key2640, 2), (key2644, 2), (key2706, 2), (key2726, 2), (key2732, 2), (key2805, -4), (key2829, -4), (key2831, -2), (key2835, -4), (key2860, 2), (key2870, 2), (key2885, 2), (key3017, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

def row9625 : Integer.Sparse Key := [(key2612, -2), (key2616, -2), (key2621, -2), (key2632, 2), (key2640, 2), (key2644, 2), (key2706, 2), (key2726, 2), (key2732, 2), (key2805, -4), (key2829, -2), (key2831, -2), (key2835, -4), (key2860, 2), (key2870, 2), (key2885, 2), (key2948, -2), (key2960, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

def row9626 : Integer.Sparse Key := [(key2612, -2), (key2616, -2), (key2621, -2), (key2632, 2), (key2640, 2), (key2644, 2), (key2706, 2), (key2726, 2), (key2732, 2), (key2805, -4), (key2829, -2), (key2831, -2), (key2835, -4), (key2860, 2), (key2870, 2), (key2885, 2), (key2948, -2), (key2960, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

def row9627 : Integer.Sparse Key := [(key2612, -2), (key2616, -2), (key2618, -2), (key2632, 2), (key2640, 2), (key2644, 2), (key2706, 2), (key2726, 2), (key2732, 2), (key2805, -2), (key2809, -2), (key2829, -2), (key2831, -2), (key2860, 2), (key2870, 2), (key2885, 2), (key2948, -2), (key2950, -4), (key2960, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

def row9628 : Integer.Sparse Key := [(key2612, -2), (key2616, -2), (key2618, -2), (key2632, 2), (key2640, 2), (key2644, 2), (key2706, 2), (key2726, 2), (key2732, 2), (key2805, -2), (key2809, -2), (key2829, -2), (key2831, -2), (key2860, 2), (key2870, 2), (key2885, 2), (key2948, -2), (key2950, -4), (key2960, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

def row9629 : Integer.Sparse Key := [(key2612, -2), (key2616, -2), (key2618, -2), (key2632, 2), (key2640, 2), (key2644, 2), (key2706, 2), (key2726, 2), (key2732, 2), (key2805, -2), (key2809, -2), (key2829, -2), (key2831, -2), (key2860, 2), (key2870, 2), (key2885, 2), (key2948, -2), (key2950, -4), (key2960, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

def row9630 : Integer.Sparse Key := [(key2612, -2), (key2616, -2), (key2618, -2), (key2632, 2), (key2640, 2), (key2644, 2), (key2706, 2), (key2726, 2), (key2732, 2), (key2805, -2), (key2809, -2), (key2829, -2), (key2831, -2), (key2860, 2), (key2870, 2), (key2885, 2), (key2948, -2), (key2950, -4), (key2960, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

def row9631 : Integer.Sparse Key := [(key2612, -2), (key2616, -2), (key2618, -2), (key2632, 2), (key2640, 2), (key2644, 2), (key2706, 2), (key2726, 2), (key2732, 2), (key2805, -2), (key2809, -2), (key2829, -2), (key2831, -2), (key2860, 2), (key2870, 2), (key2885, 2), (key2948, -2), (key2950, -4), (key2960, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

def row9632 : Integer.Sparse Key := [(key2612, -2), (key2616, -2), (key2618, -2), (key2632, 2), (key2640, 2), (key2644, 2), (key2706, 2), (key2726, 2), (key2732, 2), (key2805, -2), (key2809, -2), (key2829, -2), (key2831, -2), (key2860, 2), (key2870, 2), (key2885, 2), (key2948, -2), (key2950, -4), (key2960, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

def row9633 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2628, -4), (key2640, 2), (key2641, -2), (key2660, 2), (key2671, 2), (key2702, -4), (key2726, 2), (key2728, -2), (key2758, 2), (key2794, 2), (key2829, 2), (key2927, 2), (key2972, -4), (key2976, -4), (key2983, -4), (key3010, 2), (key3017, 2), (key3030, 2)]

def row9634 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2628, -4), (key2640, 1), (key2641, -2), (key2646, 1), (key2653, 2), (key2671, 2), (key2702, -4), (key2726, 2), (key2728, -2), (key2758, 2), (key2794, 2), (key2829, 2), (key2927, 2), (key2972, -4), (key2976, -4), (key2983, -4), (key3010, 2), (key3017, 2), (key3030, 2)]

def row9635 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2628, -4), (key2640, 1), (key2641, -2), (key2646, 1), (key2653, 2), (key2671, 2), (key2702, -4), (key2726, 2), (key2728, -2), (key2758, 2), (key2794, 2), (key2829, 2), (key2927, 2), (key2972, -4), (key2976, -4), (key2983, -4), (key3010, 2), (key3017, 2), (key3030, 2)]

def row9636 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2628, -4), (key2640, 2), (key2641, -2), (key2660, 2), (key2667, 2), (key2702, -4), (key2726, 2), (key2728, -2), (key2735, 2), (key2747, 2), (key2758, 2), (key2829, 2), (key2927, 2), (key2972, -4), (key2976, -4), (key2983, -4), (key3017, 2), (key3030, 2)]

def row9637 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2628, -4), (key2640, 2), (key2641, -2), (key2660, 2), (key2667, 2), (key2702, -4), (key2726, 2), (key2728, -2), (key2735, 2), (key2747, 2), (key2758, 2), (key2829, 1), (key2927, 2), (key2948, 1), (key2960, 2), (key2972, -4), (key2976, -4), (key2983, -4), (key3030, 2)]

def row9638 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2628, -4), (key2640, 2), (key2641, -2), (key2660, 2), (key2667, 2), (key2702, -4), (key2726, 2), (key2728, -2), (key2735, 2), (key2747, 2), (key2758, 2), (key2829, 1), (key2927, 2), (key2948, 1), (key2960, 2), (key2972, -4), (key2976, -4), (key2983, -4), (key3030, 2)]

def row9639 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2628, -4), (key2640, 1), (key2641, -2), (key2646, 1), (key2653, 2), (key2667, 1), (key2671, 1), (key2702, -4), (key2726, 1), (key2728, -2), (key2735, 1), (key2747, 2), (key2794, 1), (key2829, 1), (key2936, 1), (key2943, 2), (key2948, 1), (key2960, 2), (key2972, -4), (key2976, -4), (key2983, -4), (key2998, 2), (key3000, 2)]

def row9640 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2628, -4), (key2640, 1), (key2641, -2), (key2646, 1), (key2653, 2), (key2667, 1), (key2671, 1), (key2702, -4), (key2726, 1), (key2728, -2), (key2735, 1), (key2747, 2), (key2794, 1), (key2829, 1), (key2936, 1), (key2943, 2), (key2948, 1), (key2960, 2), (key2972, -4), (key2976, -4), (key2983, -4), (key2998, 2), (key3000, 2)]

def row9641 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2628, -4), (key2640, 1), (key2641, -2), (key2646, 1), (key2653, 2), (key2667, 1), (key2671, 1), (key2702, -4), (key2726, 1), (key2728, -2), (key2735, 1), (key2747, 2), (key2794, 1), (key2829, 1), (key2936, 1), (key2943, 2), (key2948, 1), (key2960, 2), (key2972, -4), (key2976, -4), (key2983, -4), (key2998, 2), (key3000, 2)]

def row9642 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2628, -4), (key2640, 1), (key2641, -2), (key2646, 1), (key2653, 2), (key2667, 1), (key2671, 1), (key2702, -4), (key2726, 1), (key2728, -2), (key2735, 1), (key2747, 2), (key2794, 1), (key2829, 1), (key2936, 1), (key2943, 2), (key2948, 1), (key2960, 2), (key2972, -4), (key2976, -4), (key2983, -4), (key2998, 2), (key3000, 2)]

def row9643 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2628, -4), (key2640, 1), (key2641, -2), (key2646, 1), (key2653, 2), (key2667, 1), (key2671, 1), (key2702, -4), (key2726, 1), (key2728, -2), (key2735, 1), (key2747, 2), (key2794, 1), (key2829, 1), (key2936, 1), (key2943, 2), (key2948, 1), (key2960, 2), (key2972, -4), (key2976, -4), (key2983, -4), (key2998, 2), (key3000, 2)]

def row9644 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2628, -4), (key2640, 1), (key2641, -2), (key2646, 1), (key2653, 2), (key2667, 1), (key2671, 1), (key2702, -4), (key2726, 1), (key2728, -2), (key2735, 1), (key2747, 2), (key2794, 1), (key2829, 1), (key2936, 1), (key2943, 2), (key2948, 1), (key2960, 2), (key2972, -4), (key2976, -4), (key2983, -4), (key2998, 2), (key3000, 2)]

def row9645 : Integer.Sparse Key := [(key2590, 6), (key2769, -24), (key2846, 6), (key2877, 12)]

def row9646 : Integer.Sparse Key := [(key2590, 6), (key2769, -24), (key2846, 6), (key2877, 12)]

def row9647 : Integer.Sparse Key := [(key2590, 6), (key2769, -24), (key2846, 6), (key2877, 12)]

def row9648 : Integer.Sparse Key := [(key2590, 6), (key2769, -24), (key2846, 6), (key2877, 12)]

def row9649 : Integer.Sparse Key := [(key2590, 6), (key2769, -24), (key2846, 6), (key2877, 12)]

def row9650 : Integer.Sparse Key := [(key2590, 6), (key2769, -24), (key2846, 6), (key2877, 12)]

def row9651 : Integer.Sparse Key := [(key2590, 6), (key2769, -24), (key2846, 6), (key2877, 12)]

def row9652 : Integer.Sparse Key := [(key2590, 6), (key2769, -24), (key2846, 6), (key2877, 12)]

def row9653 : Integer.Sparse Key := [(key2590, 6), (key2769, -24), (key2846, 6), (key2877, 12)]

def row9654 : Integer.Sparse Key := [(key2590, 6), (key2769, -24), (key2846, 6), (key2877, 12)]

def row9655 : Integer.Sparse Key := [(key2590, 6), (key2769, -24), (key2846, 6), (key2877, 12)]

def row9656 : Integer.Sparse Key := [(key2590, 6), (key2769, -24), (key2846, 6), (key2877, 12)]

def row9657 : Integer.Sparse Key := [(key2590, 6), (key2769, 6), (key2846, -24), (key2877, 12)]

def row9658 : Integer.Sparse Key := [(key2590, 6), (key2769, 6), (key2846, -24), (key2877, 12)]

def row9659 : Integer.Sparse Key := [(key2590, 6), (key2769, 6), (key2846, -24), (key2877, 12)]

def row9660 : Integer.Sparse Key := [(key2590, 6), (key2769, 6), (key2846, -24), (key2877, 12)]

def row9661 : Integer.Sparse Key := [(key2590, 6), (key2769, 6), (key2846, -24), (key2877, 12)]

def row9662 : Integer.Sparse Key := [(key2590, 6), (key2769, 6), (key2846, -24), (key2877, 12)]

def row9663 : Integer.Sparse Key := [(key2590, 6), (key2769, 6), (key2846, -24), (key2877, 12)]

def row9664 : Integer.Sparse Key := [(key2590, 6), (key2769, 6), (key2846, -24), (key2877, 12)]

def row9665 : Integer.Sparse Key := [(key2590, 6), (key2769, 6), (key2846, -24), (key2877, 12)]

def row9666 : Integer.Sparse Key := [(key2590, 6), (key2769, 6), (key2846, -24), (key2877, 12)]

def row9667 : Integer.Sparse Key := [(key2590, 6), (key2769, 6), (key2846, -24), (key2877, 12)]

def row9668 : Integer.Sparse Key := [(key2590, 6), (key2769, 6), (key2846, -24), (key2877, 12)]

def row9669 : Integer.Sparse Key := [(key2612, 2), (key2616, 2), (key2621, 2), (key2667, -4), (key2673, -2), (key2702, -4), (key2728, -2), (key2735, -4), (key2737, -4), (key2747, -4), (key2809, 4), (key2829, 4), (key2835, 4), (key3012, 2), (key3017, 4)]

def row9670 : Integer.Sparse Key := [(key2612, 2), (key2616, 2), (key2618, 2), (key2667, -4), (key2673, -2), (key2702, -4), (key2728, -2), (key2735, -4), (key2737, -4), (key2747, -4), (key2809, 4), (key2829, 4), (key2835, 4), (key3012, 2), (key3017, 4)]

def row9671 : Integer.Sparse Key := [(key2612, 2), (key2616, 2), (key2618, 2), (key2667, -4), (key2673, -2), (key2702, -4), (key2728, -2), (key2735, -4), (key2737, -4), (key2747, -4), (key2809, 4), (key2829, 4), (key2835, 4), (key3012, 2), (key3017, 4)]

def row9672 : Integer.Sparse Key := [(key2612, 2), (key2616, 2), (key2621, 2), (key2667, -4), (key2673, -2), (key2702, -4), (key2728, -2), (key2735, -4), (key2737, -4), (key2747, -4), (key2805, 4), (key2829, 4), (key2831, 2), (key2835, 4), (key3017, 4)]

def row9673 : Integer.Sparse Key := [(key2612, 2), (key2616, 2), (key2621, 2), (key2667, -4), (key2673, -2), (key2702, -4), (key2728, -2), (key2735, -4), (key2737, -4), (key2747, -4), (key2805, 4), (key2829, 2), (key2831, 2), (key2835, 4), (key2948, 2), (key2960, 4)]

def row9674 : Integer.Sparse Key := [(key2612, 2), (key2616, 2), (key2621, 2), (key2667, -4), (key2673, -2), (key2702, -4), (key2728, -2), (key2735, -4), (key2737, -4), (key2747, -4), (key2805, 4), (key2829, 2), (key2831, 2), (key2835, 4), (key2948, 2), (key2960, 4)]

def row9675 : Integer.Sparse Key := [(key2612, 2), (key2616, 2), (key2618, 2), (key2667, -4), (key2673, -2), (key2702, -4), (key2728, -2), (key2735, -4), (key2737, -4), (key2747, -4), (key2805, 2), (key2809, 2), (key2829, 2), (key2831, 2), (key2948, 2), (key2950, 4), (key2960, 4)]

def row9676 : Integer.Sparse Key := [(key2612, 2), (key2616, 2), (key2618, 2), (key2667, -4), (key2673, -2), (key2702, -4), (key2728, -2), (key2735, -4), (key2737, -4), (key2747, -4), (key2805, 2), (key2809, 2), (key2829, 2), (key2831, 2), (key2948, 2), (key2950, 4), (key2960, 4)]

def row9677 : Integer.Sparse Key := [(key2612, 2), (key2616, 2), (key2618, 2), (key2667, -4), (key2673, -2), (key2702, -4), (key2728, -2), (key2735, -4), (key2737, -4), (key2747, -4), (key2805, 2), (key2809, 2), (key2829, 2), (key2831, 2), (key2948, 2), (key2950, 4), (key2960, 4)]

def row9678 : Integer.Sparse Key := [(key2612, 2), (key2616, 2), (key2618, 2), (key2667, -4), (key2673, -2), (key2702, -4), (key2728, -2), (key2735, -4), (key2737, -4), (key2747, -4), (key2805, 2), (key2809, 2), (key2829, 2), (key2831, 2), (key2948, 2), (key2950, 4), (key2960, 4)]

def row9679 : Integer.Sparse Key := [(key2612, 2), (key2616, 2), (key2618, 2), (key2667, -4), (key2673, -2), (key2702, -4), (key2728, -2), (key2735, -4), (key2737, -4), (key2747, -4), (key2805, 2), (key2809, 2), (key2829, 2), (key2831, 2), (key2948, 2), (key2950, 4), (key2960, 4)]

def row9680 : Integer.Sparse Key := [(key2612, 2), (key2616, 2), (key2618, 2), (key2667, -4), (key2673, -2), (key2702, -4), (key2728, -2), (key2735, -4), (key2737, -4), (key2747, -4), (key2805, 2), (key2809, 2), (key2829, 2), (key2831, 2), (key2948, 2), (key2950, 4), (key2960, 4)]

def row9681 : Integer.Sparse Key := [(key2628, 4), (key2641, 2), (key2702, 4), (key2728, 2), (key2782, -4), (key2795, -2), (key2805, -4), (key2831, -2), (key2893, -4), (key2897, -4), (key2904, -4), (key2972, 4), (key2976, 4), (key2983, 4)]

def row9682 : Integer.Sparse Key := [(key2628, 4), (key2641, 2), (key2702, 4), (key2728, 2), (key2782, -4), (key2795, -2), (key2805, -4), (key2831, -2), (key2893, -4), (key2897, -4), (key2904, -4), (key2972, 4), (key2976, 4), (key2983, 4)]

def row9683 : Integer.Sparse Key := [(key2628, 4), (key2641, 2), (key2702, 4), (key2728, 2), (key2782, -4), (key2795, -2), (key2805, -4), (key2831, -2), (key2893, -4), (key2897, -4), (key2904, -4), (key2972, 4), (key2976, 4), (key2983, 4)]

def row9684 : Integer.Sparse Key := [(key2628, 4), (key2641, 2), (key2702, 4), (key2728, 2), (key2782, -4), (key2795, -2), (key2805, -4), (key2831, -2), (key2893, -4), (key2897, -4), (key2904, -4), (key2972, 4), (key2976, 4), (key2983, 4)]

def row9685 : Integer.Sparse Key := [(key2628, 4), (key2641, 2), (key2702, 4), (key2728, 2), (key2782, -4), (key2795, -2), (key2805, -4), (key2831, -2), (key2893, -4), (key2897, -4), (key2904, -4), (key2972, 4), (key2976, 4), (key2983, 4)]

def row9686 : Integer.Sparse Key := [(key2628, 4), (key2641, 2), (key2702, 4), (key2728, 2), (key2782, -4), (key2795, -2), (key2805, -4), (key2831, -2), (key2893, -4), (key2897, -4), (key2904, -4), (key2972, 4), (key2976, 4), (key2983, 4)]

def row9687 : Integer.Sparse Key := [(key2628, 4), (key2641, 2), (key2702, 4), (key2728, 2), (key2782, -4), (key2795, -2), (key2805, -4), (key2831, -2), (key2893, -4), (key2897, -4), (key2904, -4), (key2972, 4), (key2976, 4), (key2983, 4)]

def row9688 : Integer.Sparse Key := [(key2628, 4), (key2641, 2), (key2702, 4), (key2728, 2), (key2782, -4), (key2795, -2), (key2805, -4), (key2831, -2), (key2893, -4), (key2897, -4), (key2904, -4), (key2972, 4), (key2976, 4), (key2983, 4)]

def row9689 : Integer.Sparse Key := [(key2628, 4), (key2641, 2), (key2702, 4), (key2728, 2), (key2782, -4), (key2795, -2), (key2805, -4), (key2831, -2), (key2893, -4), (key2897, -4), (key2904, -4), (key2972, 4), (key2976, 4), (key2983, 4)]

def row9690 : Integer.Sparse Key := [(key2628, 4), (key2641, 2), (key2702, 4), (key2728, 2), (key2782, -4), (key2795, -2), (key2805, -4), (key2831, -2), (key2893, -4), (key2897, -4), (key2904, -4), (key2972, 4), (key2976, 4), (key2983, 4)]

def row9691 : Integer.Sparse Key := [(key2628, 4), (key2641, 2), (key2702, 4), (key2728, 2), (key2782, -4), (key2795, -2), (key2805, -4), (key2831, -2), (key2893, -4), (key2897, -4), (key2904, -4), (key2972, 4), (key2976, 4), (key2983, 4)]

def row9692 : Integer.Sparse Key := [(key2628, 4), (key2641, 2), (key2702, 4), (key2728, 2), (key2782, -4), (key2795, -2), (key2805, -4), (key2831, -2), (key2893, -4), (key2897, -4), (key2904, -4), (key2972, 4), (key2976, 4), (key2983, 4)]

def row9693 : Integer.Sparse Key := [(key1296, -4), (key1303, -2), (key1316, 2), (key1337, 2), (key1340, 2), (key1546, 2), (key1573, -4), (key1597, -2), (key1655, 2), (key1668, 2), (key1772, 2), (key1775, 2), (key1788, -4), (key1791, -4), (key1799, -4), (key1813, 2), (key1826, 2), (key1840, 2), (key1845, 2)]

def row9694 : Integer.Sparse Key := [(key1296, -4), (key1303, -2), (key1316, 2), (key1337, 2), (key1340, 2), (key1546, 2), (key1573, -4), (key1597, -2), (key1655, 2), (key1668, 2), (key1772, 2), (key1775, 2), (key1788, -4), (key1791, -4), (key1799, -4), (key1813, 2), (key1826, 2), (key1840, 2), (key1845, 2)]

def row9695 : Integer.Sparse Key := [(key1296, -4), (key1303, -2), (key1316, 2), (key1337, 2), (key1340, 2), (key1546, 2), (key1573, -4), (key1597, -2), (key1655, 2), (key1668, 2), (key1772, 2), (key1775, 2), (key1788, -4), (key1791, -4), (key1799, -4), (key1813, 2), (key1826, 2), (key1840, 2), (key1845, 2)]

def row9696 : Integer.Sparse Key := [(key1296, -4), (key1303, -2), (key1316, 2), (key1337, 2), (key1340, 2), (key1546, 2), (key1573, -4), (key1597, -2), (key1655, 2), (key1668, 2), (key1772, 2), (key1775, 2), (key1788, -4), (key1791, -4), (key1799, -4), (key1813, 2), (key1826, 2), (key1840, 2), (key1845, 2)]

def row9697 : Integer.Sparse Key := [(key1296, -4), (key1303, -2), (key1316, 2), (key1337, 2), (key1340, 2), (key1546, 2), (key1573, -4), (key1597, -2), (key1655, 2), (key1668, 2), (key1772, 2), (key1775, 2), (key1788, -4), (key1791, -4), (key1799, -4), (key1813, 2), (key1826, 2), (key1840, 2), (key1845, 2)]

def row9698 : Integer.Sparse Key := [(key1296, -4), (key1303, -2), (key1316, 2), (key1337, 2), (key1340, 2), (key1546, 2), (key1573, -4), (key1597, -2), (key1655, 2), (key1668, 2), (key1772, 2), (key1775, 2), (key1788, -4), (key1791, -4), (key1799, -4), (key1813, 2), (key1826, 2), (key1840, 2), (key1845, 2)]

def row9699 : Integer.Sparse Key := [(key1296, -4), (key1303, -2), (key1316, 2), (key1337, 2), (key1340, 2), (key1546, 2), (key1573, -4), (key1597, -2), (key1655, 2), (key1668, 2), (key1772, 2), (key1775, 2), (key1788, -4), (key1791, -4), (key1799, -4), (key1813, 2), (key1826, 2), (key1840, 2), (key1845, 2)]

def row9700 : Integer.Sparse Key := [(key1296, -4), (key1303, -2), (key1316, 2), (key1337, 2), (key1340, 2), (key1546, 2), (key1573, -4), (key1597, -2), (key1655, 2), (key1668, 2), (key1772, 2), (key1775, 2), (key1788, -4), (key1791, -4), (key1799, -4), (key1813, 2), (key1826, 2), (key1840, 2), (key1845, 2)]

def row9701 : Integer.Sparse Key := [(key1296, -4), (key1303, -2), (key1316, 2), (key1337, 2), (key1340, 2), (key1546, 2), (key1573, -4), (key1597, -2), (key1655, 2), (key1668, 2), (key1772, 2), (key1775, 2), (key1788, -4), (key1791, -4), (key1799, -4), (key1813, 2), (key1826, 2), (key1840, 2), (key1845, 2)]

def row9702 : Integer.Sparse Key := [(key1296, -4), (key1303, -2), (key1316, 2), (key1337, 2), (key1340, 2), (key1546, 2), (key1573, -4), (key1597, -2), (key1655, 2), (key1668, 2), (key1772, 2), (key1775, 2), (key1788, -4), (key1791, -4), (key1799, -4), (key1813, 2), (key1826, 2), (key1840, 2), (key1845, 2)]

def row9703 : Integer.Sparse Key := [(key1296, -4), (key1303, -2), (key1316, 2), (key1337, 2), (key1340, 2), (key1546, 2), (key1573, -4), (key1597, -2), (key1655, 2), (key1668, 2), (key1772, 2), (key1775, 2), (key1788, -4), (key1791, -4), (key1799, -4), (key1813, 2), (key1826, 2), (key1840, 2), (key1845, 2)]

def row9704 : Integer.Sparse Key := [(key1296, -4), (key1303, -2), (key1316, 2), (key1337, 2), (key1340, 2), (key1546, 2), (key1573, -4), (key1597, -2), (key1655, 2), (key1668, 2), (key1772, 2), (key1775, 2), (key1788, -4), (key1791, -4), (key1799, -4), (key1813, 2), (key1826, 2), (key1840, 2), (key1845, 2)]

def row9705 : Integer.Sparse Key := [(key1296, 2), (key1316, -4), (key1330, -2), (key1337, 2), (key1346, 2), (key1391, 2), (key1424, -4), (key1448, -2), (key1455, 2), (key1467, 2), (key1772, 2), (key1781, 2), (key1788, 2), (key1799, 2), (key1813, -4), (key1818, -4), (key1826, -4), (key1842, 2), (key1845, 2)]

def row9706 : Integer.Sparse Key := [(key1296, 2), (key1316, -4), (key1330, -2), (key1337, 2), (key1346, 2), (key1391, 2), (key1424, -4), (key1448, -2), (key1455, 2), (key1467, 2), (key1772, 2), (key1781, 2), (key1788, 2), (key1799, 2), (key1813, -4), (key1818, -4), (key1826, -4), (key1842, 2), (key1845, 2)]

def row9707 : Integer.Sparse Key := [(key1296, 2), (key1316, -4), (key1330, -2), (key1337, 2), (key1346, 2), (key1391, 2), (key1424, -4), (key1448, -2), (key1455, 2), (key1467, 2), (key1772, 2), (key1781, 2), (key1788, 2), (key1799, 2), (key1813, -4), (key1818, -4), (key1826, -4), (key1842, 2), (key1845, 2)]

def row9708 : Integer.Sparse Key := [(key1296, 2), (key1316, -4), (key1330, -2), (key1337, 2), (key1346, 2), (key1391, 2), (key1424, -4), (key1448, -2), (key1455, 2), (key1467, 2), (key1772, 2), (key1781, 2), (key1788, 2), (key1799, 2), (key1813, -4), (key1818, -4), (key1826, -4), (key1842, 2), (key1845, 2)]

def row9709 : Integer.Sparse Key := [(key1296, 2), (key1316, -4), (key1330, -2), (key1337, 2), (key1346, 2), (key1391, 2), (key1424, -4), (key1448, -2), (key1455, 2), (key1467, 2), (key1772, 2), (key1781, 2), (key1788, 2), (key1799, 2), (key1813, -4), (key1818, -4), (key1826, -4), (key1842, 2), (key1845, 2)]

def row9710 : Integer.Sparse Key := [(key1296, 2), (key1316, -4), (key1330, -2), (key1337, 2), (key1346, 2), (key1391, 2), (key1424, -4), (key1448, -2), (key1455, 2), (key1467, 2), (key1772, 2), (key1781, 2), (key1788, 2), (key1799, 2), (key1813, -4), (key1818, -4), (key1826, -4), (key1842, 2), (key1845, 2)]

def row9711 : Integer.Sparse Key := [(key1296, 2), (key1316, -4), (key1330, -2), (key1337, 2), (key1346, 2), (key1391, 2), (key1424, -4), (key1448, -2), (key1455, 2), (key1467, 2), (key1772, 2), (key1781, 2), (key1788, 2), (key1799, 2), (key1813, -4), (key1818, -4), (key1826, -4), (key1842, 2), (key1845, 2)]

def row9712 : Integer.Sparse Key := [(key1296, 2), (key1316, -4), (key1330, -2), (key1337, 2), (key1346, 2), (key1391, 2), (key1424, -4), (key1448, -2), (key1455, 2), (key1467, 2), (key1772, 2), (key1781, 2), (key1788, 2), (key1799, 2), (key1813, -4), (key1818, -4), (key1826, -4), (key1842, 2), (key1845, 2)]

def row9713 : Integer.Sparse Key := [(key1296, 2), (key1316, -4), (key1330, -2), (key1337, 2), (key1346, 2), (key1391, 2), (key1424, -4), (key1448, -2), (key1455, 2), (key1467, 2), (key1772, 2), (key1781, 2), (key1788, 2), (key1799, 2), (key1813, -4), (key1818, -4), (key1826, -4), (key1842, 2), (key1845, 2)]

def row9714 : Integer.Sparse Key := [(key1296, 2), (key1316, -4), (key1330, -2), (key1337, 2), (key1346, 2), (key1391, 2), (key1424, -4), (key1448, -2), (key1455, 2), (key1467, 2), (key1772, 2), (key1781, 2), (key1788, 2), (key1799, 2), (key1813, -4), (key1818, -4), (key1826, -4), (key1842, 2), (key1845, 2)]

def row9715 : Integer.Sparse Key := [(key1296, 2), (key1316, -4), (key1330, -2), (key1337, 2), (key1346, 2), (key1391, 2), (key1424, -4), (key1448, -2), (key1455, 2), (key1467, 2), (key1772, 2), (key1781, 2), (key1788, 2), (key1799, 2), (key1813, -4), (key1818, -4), (key1826, -4), (key1842, 2), (key1845, 2)]

def row9716 : Integer.Sparse Key := [(key1296, 2), (key1316, -4), (key1330, -2), (key1337, 2), (key1346, 2), (key1391, 2), (key1424, -4), (key1448, -2), (key1455, 2), (key1467, 2), (key1772, 2), (key1781, 2), (key1788, 2), (key1799, 2), (key1813, -4), (key1818, -4), (key1826, -4), (key1842, 2), (key1845, 2)]

def row9717 : Integer.Sparse Key := [(key2632, 2), (key2640, 2), (key2644, 2), (key2658, -2), (key2660, -4), (key2706, 2), (key2726, 2), (key2732, 2), (key2753, -2), (key2758, -4), (key2860, 2), (key2870, 2), (key2885, 2), (key2920, -4), (key2923, -4), (key2927, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

def row9718 : Integer.Sparse Key := [(key2632, 2), (key2640, 2), (key2644, 2), (key2658, -2), (key2660, -4), (key2706, 2), (key2726, 2), (key2732, 2), (key2753, -2), (key2758, -4), (key2860, 2), (key2870, 2), (key2885, 2), (key2920, -4), (key2923, -4), (key2927, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

def row9719 : Integer.Sparse Key := [(key2632, 2), (key2640, 2), (key2644, 2), (key2658, -2), (key2660, -4), (key2706, 2), (key2726, 2), (key2732, 2), (key2753, -2), (key2758, -4), (key2860, 2), (key2870, 2), (key2885, 2), (key2920, -4), (key2923, -4), (key2927, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

def row9720 : Integer.Sparse Key := [(key2632, 2), (key2640, 2), (key2644, 2), (key2658, -2), (key2660, -4), (key2706, 2), (key2726, 2), (key2732, 2), (key2753, -2), (key2758, -4), (key2860, 2), (key2870, 2), (key2885, 2), (key2920, -4), (key2923, -4), (key2927, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

def row9721 : Integer.Sparse Key := [(key2632, 2), (key2640, 2), (key2644, 2), (key2658, -2), (key2660, -4), (key2706, 2), (key2726, 2), (key2732, 2), (key2753, -2), (key2758, -4), (key2860, 2), (key2870, 2), (key2885, 2), (key2920, -4), (key2923, -4), (key2927, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

def row9722 : Integer.Sparse Key := [(key2632, 2), (key2640, 2), (key2644, 2), (key2658, -2), (key2660, -4), (key2706, 2), (key2726, 2), (key2732, 2), (key2753, -2), (key2758, -4), (key2860, 2), (key2870, 2), (key2885, 2), (key2920, -4), (key2923, -4), (key2927, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

def row9723 : Integer.Sparse Key := [(key2632, 2), (key2640, 2), (key2644, 2), (key2658, -2), (key2660, -4), (key2706, 2), (key2726, 2), (key2732, 2), (key2753, -2), (key2758, -4), (key2860, 2), (key2870, 2), (key2885, 2), (key2920, -4), (key2923, -4), (key2927, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

def row9724 : Integer.Sparse Key := [(key2632, 2), (key2640, 2), (key2644, 2), (key2658, -2), (key2660, -4), (key2706, 2), (key2726, 2), (key2732, 2), (key2753, -2), (key2758, -4), (key2860, 2), (key2870, 2), (key2885, 2), (key2920, -4), (key2923, -4), (key2927, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

def row9725 : Integer.Sparse Key := [(key2632, 2), (key2640, 2), (key2644, 2), (key2658, -2), (key2660, -4), (key2706, 2), (key2726, 2), (key2732, 2), (key2753, -2), (key2758, -4), (key2860, 2), (key2870, 2), (key2885, 2), (key2920, -4), (key2923, -4), (key2927, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

def row9726 : Integer.Sparse Key := [(key2632, 2), (key2640, 2), (key2644, 2), (key2658, -2), (key2660, -4), (key2706, 2), (key2726, 2), (key2732, 2), (key2753, -2), (key2758, -4), (key2860, 2), (key2870, 2), (key2885, 2), (key2920, -4), (key2923, -4), (key2927, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

def row9727 : Integer.Sparse Key := [(key2632, 2), (key2640, 2), (key2644, 2), (key2658, -2), (key2660, -4), (key2706, 2), (key2726, 2), (key2732, 2), (key2753, -2), (key2758, -4), (key2860, 2), (key2870, 2), (key2885, 2), (key2920, -4), (key2923, -4), (key2927, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

end MUB6.Certificate.GramRows

end OAI
end


