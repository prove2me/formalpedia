-- Prove2me | Definitions.Def_OAIQ106D005
-- name    : OAIQ106D005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T11:57:45.096483+00:00
-- url     : https://prove2.me/theorems/9e824fa7-c4f9-4e74-9e7a-cf59aed332fa
-- title:
--   Definitions bundle OAIQ106D005 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 7529 declarations of OpenAI's Lean: 7529 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSemantics.raw10459step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw10459step1`, `OAI.MUB6.Certificate.MixedSemantics.raw10459step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw10459step2`, `OAI.MUB6.Certificate.MixedSemantics.raw10459step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw1045step0`, `OAI.MUB6.Certificate.MixedSemantics.raw1045step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw1046`, `OAI.MUB6.Certificate.MixedSemantics.raw10460`, `OAI.MUB6.Certificate.MixedSemantics.raw10460Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw10460step0`, `OAI.MUB6.Certificate.MixedSemantics.raw10460step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw10460step1`, `OAI.MUB6.Certificate.MixedSemantics.raw10460step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw10460step2`, `OAI.MUB6.Certificate.MixedSemantics.raw10460step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw10461`, `OAI.MUB6.Certificate.MixedSemantics.raw10461Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw10461step0`, `OAI.MUB6.Certificate.MixedSemantics.raw10461step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw10461step1`, `OAI.MUB6.Certificate.MixedSemantics.raw10461step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw10462`, `OAI.MUB6.Certificate.MixedSemantics.raw10462Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw10462step0`, `OAI.MUB6.Certificate.MixedSemantics.raw10462step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw10462step1`, `OAI.MUB6.Certificate.MixedSemantics.raw10462step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw10462step2`, `OAI.MUB6.Certificate.MixedSemantics.raw10462step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw10463`, `OAI.MUB6.Certificate.MixedSemantics.raw10463Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw10463step0`, `OAI.MUB6.Certificate.MixedSemantics.raw10463step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw10463step1`, `OAI.MUB6.Certificate.MixedSemantics.raw10463step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw10463step2`, `OAI.MUB6.Certificate.MixedSemantics.raw10463step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw10464`, `OAI.MUB6.Certificate.MixedSemantics.raw10464Labels` and 7489 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_MixedSemantics_Canonical0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical0.lean), [`MutuallyUnbiased_MixedSemantics_Canonical8`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical8.lean), [`MutuallyUnbiased_MixedSemantics_Canonical81`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical81.lean), [`MutuallyUnbiased_MixedSemantics_Canonical82`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical82.lean), [`MutuallyUnbiased_MixedSemantics_Canonical83`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical83.lean), [`MutuallyUnbiased_MixedSemantics_Canonical84`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical84.lean), [`MutuallyUnbiased_MixedSemantics_Canonical85`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical85.lean), [`MutuallyUnbiased_MixedSemantics_Canonical86`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical86.lean), [`MutuallyUnbiased_MixedSemantics_Canonical87`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical87.lean), [`MutuallyUnbiased_MixedSemantics_Canonical88`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical88.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound1343`, `OAI.MUB6.Certificate.MixedSemantics.sound1344`, `OAI.MUB6.Certificate.MixedSemantics.sound1346`, `OAI.MUB6.Certificate.MixedSemantics.sound1395`, `OAI.MUB6.Certificate.MixedSemantics.sourceEq1095`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound107`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound118`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound33`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound34`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound35`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound36`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound46`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound70`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound84`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound85`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero539`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1020`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1114`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1120`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1123`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1124`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1165`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1169`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1177`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1194`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1195`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1197`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1205`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1300`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1303`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1309`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1318`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1321`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1326`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1469`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1471`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1477`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1483`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1490`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1508`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1510`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1513`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1514`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1516`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1587`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1593`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1595`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1650`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1708`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1710`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1715`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1716`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1717`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1723`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1734`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1738`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1739`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1740`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1743`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1822`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1844`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1853`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1854`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1864`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1871`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1874`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1877`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1880`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1881`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1906`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1910`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1944`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1948`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1952`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1963`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1968`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1969`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1983`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1984`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1988`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1990`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1999`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2004`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2005`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2006`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2010`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2011`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2015`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2018`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2021`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2023`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound531`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound532`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound533`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound534`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound536`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound537`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound538`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound540`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound542`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound543`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound545`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound546`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound547`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound548`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound551`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound552`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound553`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound554`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound555`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound558`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound564`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound565`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound566`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound567`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound568`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound571`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound572`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound579`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound580`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound581`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound582`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound587`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound630`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound865`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound866`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound926`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound927`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound964`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound983` and `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound49`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw10Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw10step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw10step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw104Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw104step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw104step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw104step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw104step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw105 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![-2, 2, 0]]
def raw105Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw105step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw105step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw106 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw106Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw106step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw106step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw106step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw106step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw107 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw107Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw107step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw107step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw108 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw108Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw108step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw108step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw108step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw108step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw109 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw109Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw109step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw109step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw110 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-2, 2, 0], ![0, 3, -3]]
def raw110Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw110step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, 0, -2], ![3, -3, 0]]
def raw110step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw110step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, 0, -2], ![3, -3, 0]]
def raw110step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw111 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-2, 2, 0], ![0, 3, -3]]
def raw111Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw111step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw111step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw112 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw112Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw112step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw112step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw112step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw112step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw113 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw1045step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw1045step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1046 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 0, -1], ![-2, 2, 0], ![0, 3, -3]]
def raw1046Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1046step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-3, 0, 3]]
def raw1046step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1046step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, 0, -3]]
def raw1046step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1046step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, 0, -3]]
def raw1046step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1047 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 0, -1], ![-1, 2, -1], ![-1, 3, -2]]
def raw1047Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1047step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw1047step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1047step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw1047step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1048 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 0, -1], ![-1, 2, -1], ![-1, 3, -2]]
def raw1048Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1048step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw1048step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1049 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 0, -1], ![-1, 2, -1], ![-1, 3, -2]]
def raw1049Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1049step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw1049step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1049step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw1049step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1049step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw1049step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1050 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 0, -1], ![0, 2, -2], ![-2, 3, -1]]
def raw1050Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1050step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw1050step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1050step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw1050step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1051 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 0, -1], ![0, 2, -2], ![-2, 3, -1]]
def raw1051Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1051step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw1051step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1052 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 0, -1], ![0, 2, -2], ![-2, 3, -1]]
def raw1052Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1052step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![-1, 1, 0], ![-1, -2, 3], ![-2, 0, 2]]
def raw1052step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1052step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw1052step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1052step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw1052step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1056 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![0, 2, -2]]
def raw1056Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1056step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw1056step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1056step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw1056step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1057 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![0, 2, -2]]
def raw1057Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1057step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw1057step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1058 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![0, 2, -2]]
def raw1058Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1058step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw1058step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1058step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1058step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1058step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1058step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1062 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw1062Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1062step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw1062step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1062step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw1062step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1063 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw1063Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1063step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw1063step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1064 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw1064Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1064step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw1064step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1064step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw1064step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1064step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw1064step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1065 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![-1, 3, -2]]
def raw1065Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1065step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw1065step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1065step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw1065step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1066 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![-1, 3, -2]]
def raw1066Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1066step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw1066step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1067 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![-1, 3, -2]]
def raw1067Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1067step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, -1, 3]]
def raw1067step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1067step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, 1, -3]]
def raw1067step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1067step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, 1, -3]]
def raw1067step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1068 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![-1, 1, 0], ![-1, 2, -1], ![1, 2, -3]]
def raw1068Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1068step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw1068step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1068step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw1068step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1069 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![-1, 1, 0], ![-1, 2, -1], ![1, 2, -3]]
def raw1069Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1069step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw1069step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1070 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![-1, 1, 0], ![-1, 2, -1], ![1, 2, -3]]
def raw1070Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1070step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 1, 2]]
def raw1070step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1070step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -1, -2]]
def raw1070step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1070step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -1, -2]]
def raw1070step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1071 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw1071Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1071step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw1071step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1071step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw1071step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1072 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw1072Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1072step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw1072step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1073 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw1073Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1073step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw1073step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1073step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1073step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1073step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1073step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1074 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![-2, 3, -1]]
def raw1074Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1074step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw1074step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1074step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw1074step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1075 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![-2, 3, -1]]
def raw1075Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1075step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw1075step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1076 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![-2, 3, -1]]
def raw1076Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1076step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![-1, 0, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw1076step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1076step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -1, -1]]
def raw1076step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1076step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -1, -1]]
def raw1076step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1080 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 1, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw1080Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1080step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw1080step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1080step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw1080step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1081 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 1, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw1081Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1081step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw1081step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1082 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 1, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw1082Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1082step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![0, -2, 2], ![-2, 1, 1], ![-2, 0, 2]]
def raw1082step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1082step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, 0, -2]]
def raw1082step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1082step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, 0, -2]]
def raw1082step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1083 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 1, -2], ![-1, 2, -1], ![-1, 2, -1]]
def raw1083Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1083step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw1083step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1083step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw1083step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1084 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 1, -2], ![-1, 2, -1], ![-1, 2, -1]]
def raw1084Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1084step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw1084step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1085 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 1, -2], ![-1, 2, -1], ![-1, 2, -1]]
def raw1085Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1085step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![-1, -1, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw1085step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1085step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -1, -1]]
def raw1085step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1085step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -1, -1]]
def raw1085step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1086 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 1, -2], ![-2, 4, -2]]
def raw1086Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1086step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![4, -2, -2]]
def raw1086step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1086step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![4, -2, -2]]
def raw1086step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1087 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 1, -2], ![-2, 4, -2]]
def raw1087Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1087step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![4, -2, -2]]
def raw1087step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1088 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 1, -2], ![-2, 4, -2]]
def raw1088Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1088step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![-2, 1, 1], ![-2, -2, 4]]
def raw1088step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1088step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![2, -1, -1], ![2, 2, -4]]
def raw1088step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1088step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![2, -1, -1], ![2, 2, -4]]
def raw1088step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1092 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 2, -3], ![-2, 3, -1]]
def raw1092Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1092step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, 1, -3], ![3, -2, -1]]
def raw1092step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1092step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, 1, -3], ![3, -2, -1]]
def raw1092step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1093 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 2, -3], ![-2, 3, -1]]
def raw1093Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1093step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, 1, -3], ![3, -2, -1]]
def raw1093step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1094 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 2, -3], ![-2, 3, -1]]
def raw1094Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1094step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![-1, -2, 3], ![-3, 1, 2]]
def raw1094step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1094step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, 2, -3], ![3, -1, -2]]
def raw1094step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1094step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, 2, -3], ![3, -1, -2]]
def raw1094step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1095 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 3, -3]]
def raw1095Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1095step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw1095step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1095step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw1095step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1096 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 3, -3]]
def raw1096Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1096step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw1096step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1097 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 3, -3]]
def raw1097Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1097step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 0, 3]]
def raw1097step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1097step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw1097step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1097step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw1097step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1098 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![0, 2, -2]]
def raw1098Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1098step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw1098step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1098step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw1098step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1099 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![0, 2, -2]]
def raw1099Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1099step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw1099step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1100 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![0, 2, -2]]
def raw1100Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1100step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-2, 0, 2], ![-2, 0, 2]]
def raw1100step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1100step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw1100step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1100step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw1100step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1101 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw1101Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1101step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw1101step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1101step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw1101step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1102 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw1102Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1102step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw1102step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1103 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw1103Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1103step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw1103step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1103step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw1103step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1103step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw1103step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1104 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 0, 1], ![0, 1, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw1104Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1104step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1104step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1104step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1104step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1105 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 0, 1], ![0, 1, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw1105Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1105step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1105step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1106 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 0, 1], ![0, 1, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw1106Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1106step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw1106step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1106step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw1106step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1106step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw1106step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1107 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 0, 1], ![-1, 2, -1], ![0, 3, -3]]
def raw1107Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1107step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw1107step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1107step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw1107step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1108 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 0, 1], ![-1, 2, -1], ![0, 3, -3]]
def raw1108Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1108step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw1108step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1109 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 0, 1], ![-1, 2, -1], ![0, 3, -3]]
def raw1109Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1109step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-3, 0, 3]]
def raw1109step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1109step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, 0, -3]]
def raw1109step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1109step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, 0, -3]]
def raw1109step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1110 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 0, 1], ![0, 2, -2], ![-1, 3, -2]]
def raw1110Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1110step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw1110step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1110step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw1110step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1111 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 0, 1], ![0, 2, -2], ![-1, 3, -2]]
def raw1111Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1111step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw1111step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1112 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 0, 1], ![0, 2, -2], ![-1, 3, -2]]
def raw1112Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1112step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, 1, -1], ![-2, 0, 2], ![-2, -1, 3]]
def raw1112step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1112step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 1, -3]]
def raw1112step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1112step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 1, -3]]
def raw1112step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1113 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw1113Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1113step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1113step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1113step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1113step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1114 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw1114Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1114step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1114step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1115 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw1115Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1115step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw1115step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1115step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1115step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1115step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1115step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1116 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-2, 1, 1], ![0, 1, -1], ![0, 3, -3]]
def raw1116Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1116step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw1116step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1116step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw1116step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1117 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-2, 1, 1], ![0, 1, -1], ![0, 3, -3]]
def raw1117Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1117step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw1117step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1118 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-2, 1, 1], ![0, 1, -1], ![0, 3, -3]]
def raw1118Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1118step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-3, 0, 3]]
def raw1118step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1118step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw1118step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1118step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw1118step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1119 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-2, 1, 1], ![0, 2, -2], ![0, 2, -2]]
def raw1119Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1119step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw1119step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1119step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw1119step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1120 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-2, 1, 1], ![0, 2, -2], ![0, 2, -2]]
def raw1120Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1120step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw1120step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1121 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-2, 1, 1], ![0, 2, -2], ![0, 2, -2]]
def raw1121Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1121step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![0, 1, -1], ![-2, 0, 2], ![-2, 0, 2]]
def raw1121step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1121step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw1121step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1121step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw1121step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1122 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw1122Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1122step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw1122step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1122step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw1122step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1123 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw1123Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1123step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw1123step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1124 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw1124Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1124step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw1124step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1124step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1124step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1124step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1124step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1125 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw1125Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1125step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw1125step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1125step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw1125step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1126 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw1126Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1126step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw1126step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1127 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw1127Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1127step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw1127step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1127step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw1127step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1127step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw1127step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1128 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw1128Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1128step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1128step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1128step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1128step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1129 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw1129Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1129step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1129step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1130 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw1130Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1130step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw1130step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1130step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw1130step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1130step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw1130step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1131 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw1131Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1131step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw1131step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1131step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw1131step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1132 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw1132Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1132step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw1132step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1133 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw1133Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1133step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw1133step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1133step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw1133step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1133step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw1133step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1134 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw1134Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1134step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw1134step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1134step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw1134step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1135 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical81
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw10459step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10459step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw10459step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10459step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw10459step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10460Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10460step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10460step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10460step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10460step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10460step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10460step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10461 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10461Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10461step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10461step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10461step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10461step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10462Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10462step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10462step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10462step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10462step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10462step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10462step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw10463Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10463step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw10463step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10463step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10463step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10463step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10463step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw10464Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10464step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw10464step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10464step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw10464step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10464step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw10464step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10465 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10465Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10465step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10465step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10465step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10465step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10465step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw10465step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10465step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw10465step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10466 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10466Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10466step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10466step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10466step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw10466step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10466step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw10466step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10467Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10467step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10467step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10467step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw10467step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10467step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw10467step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10468 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, -1, -1]]
def raw10468Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10468step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, -1, -1]]
def raw10468step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10468step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -1, 1], ![2, -1, -1]]
def raw10468step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10468step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw10468step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10468step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw10468step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10469 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw10469Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10469step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw10469step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10469step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw10469step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10469step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw10469step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10469step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw10469step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10470 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw10470Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10470step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw10470step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10470step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw10470step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10470step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw10470step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10470step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw10470step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10471 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw10471Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10471step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw10471step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10471step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw10471step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10471step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw10471step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10472 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw10472Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10472step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw10472step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10472step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw10472step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10472step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw10472step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10473 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![2, -3, 1], ![2, -1, -1]]
def raw10473Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10473step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 2, -1], ![2, -3, 1], ![2, -1, -1]]
def raw10473step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10473step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![2, -3, 1], ![2, -1, -1]]
def raw10473step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10473step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, -1, -1], ![2, 1, -3]]
def raw10473step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10473step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, -1, -1], ![2, 1, -3]]
def raw10473step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10474 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![1, 0, -1]]
def raw10474Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10474step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![1, 0, -1]]
def raw10474step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10474step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![2, -3, 1], ![1, 0, -1]]
def raw10474step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10474step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10474step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10474step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10474step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10475 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw10475Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10475step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw10475step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10475step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw10475step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10475step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw10475step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10475step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw10475step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10476 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw10476Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10476step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw10476step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10476step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw10476step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10476step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw10476step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10476step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw10476step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10477 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw10477Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10477step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw10477step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10477step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw10477step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10477step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw10477step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10477step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw10477step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10478 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![3, -2, -1]]
def raw10478Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10478step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![3, -2, -1]]
def raw10478step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10478step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -2, 1], ![3, -2, -1]]
def raw10478step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10478step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 1, -2], ![3, -1, -2]]
def raw10478step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10478step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 1, -2], ![3, -1, -2]]
def raw10478step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10479 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![3, -2, -1]]
def raw10479Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10479step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![3, -2, -1]]
def raw10479step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10479step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![3, -2, -1]]
def raw10479step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10479step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw10479step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10479step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw10479step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10480 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10480Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10480step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10480step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10480step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw10480step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10480step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10480step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10481 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10481Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10481step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10481step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10481step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw10481step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10481step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10481step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10482 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10482Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10482step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10482step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10482step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10482step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10482step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw10482step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10483 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw10483Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10483step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw10483step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10483step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw10483step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10483step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw10483step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10484 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw10484Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10484step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw10484step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10484step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw10484step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10484step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw10484step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10485 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10485Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10485step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10485step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10485step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10485step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10486 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10486Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10486step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10486step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10487 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10487Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10487step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10487step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10487step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10487step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10488 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw10488Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10488step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw10488step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10488step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10488step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10489 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw10489Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10489step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw10489step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10489step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw10489step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10490 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10490Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10490step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10490step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10490step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10490step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10491 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10491Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10491step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10491step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10492 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10492Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10492step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10492step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10492step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10492step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10493 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw10493Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10493step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw10493step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10493step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10493step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10494 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw10494Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10494step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw10494step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10494step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw10494step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10495 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10495Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10495step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10495step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10495step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10495step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10495step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw10495step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical82
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw10496 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10496Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10496step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10496step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10496step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw10496step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10497 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10497Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10497step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10497step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10497step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw10497step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10498 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, -1, -1]]
def raw10498Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10498step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, -1, -1]]
def raw10498step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10498step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -1, 1], ![2, -1, -1]]
def raw10498step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10498step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw10498step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10499 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw10499Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10499step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw10499step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10499step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw10499step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10499step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw10499step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10500 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw10500Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10500step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw10500step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10500step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw10500step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10500step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw10500step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw10501Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10501step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw10501step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10501step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw10501step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw10502Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10502step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw10502step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10502step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw10502step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10503 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![2, -3, 1], ![2, -1, -1]]
def raw10503Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10503step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 2, -1], ![2, -3, 1], ![2, -1, -1]]
def raw10503step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10503step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![2, -3, 1], ![2, -1, -1]]
def raw10503step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10503step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, -1, -1], ![2, 1, -3]]
def raw10503step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10504 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![1, 0, -1]]
def raw10504Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10504step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![1, 0, -1]]
def raw10504step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10504step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![2, -3, 1], ![1, 0, -1]]
def raw10504step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10504step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10504step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10505 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw10505Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10505step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw10505step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10505step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw10505step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10505step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw10505step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10506 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw10506Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10506step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw10506step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10506step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw10506step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10506step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw10506step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10507 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw10507Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10507step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw10507step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10507step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw10507step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10507step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw10507step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10508 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![3, -2, -1]]
def raw10508Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10508step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![3, -2, -1]]
def raw10508step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10508step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -2, 1], ![3, -2, -1]]
def raw10508step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10508step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 1, -2], ![3, -1, -2]]
def raw10508step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10509 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![3, -2, -1]]
def raw10509Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10509step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![3, -2, -1]]
def raw10509step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10509step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![3, -2, -1]]
def raw10509step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10509step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw10509step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10510 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw10510Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10510step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw10510step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10510step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10510step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10510step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10510step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10511 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw10511Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10511step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw10511step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10511step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10511step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10511step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10511step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10512 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw10512Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10512step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw10512step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10512step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw10512step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10512step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw10512step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10512step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw10512step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10513 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw10513Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10513step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw10513step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10513step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw10513step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10513step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw10513step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10513step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw10513step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10514 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw10514Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10514step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10514step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw10514step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10514step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10515 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 2, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw10515Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10515step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 2, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw10515step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10515step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10515step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw10515step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10515step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10516 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw10516Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10516step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw10516step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10516step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw10516step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10516step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw10516step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10516step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw10516step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10516step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw10516step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10517 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw10517Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10517step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw10517step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10517step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10517step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10517step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10517step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10518 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw10518Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10518step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-2, 2, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw10518step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10518step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw10518step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10518step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw10518step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10518step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw10518step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10519 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -2, 2]]
def raw10519Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10519step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -2, 2]]
def raw10519step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10519step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -2, 1], ![0, -2, 2]]
def raw10519step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10519step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw10519step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10519step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw10519step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10519step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw10519step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10520 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -2, 2]]
def raw10520Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10520step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -2, 2]]
def raw10520step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10520step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw10520step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw10520step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw10520step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10521 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -2, 2]]
def raw10521Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10521step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -2, 2]]
def raw10521step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10521step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw10521step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw10521step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw10521step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10522 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![0, -2, 2]]
def raw10522Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10522step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![0, -2, 2]]
def raw10522step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10522step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -2, 1], ![0, -2, 2]]
def raw10522step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10522step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw10522step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw10522step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw10522step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10523 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw10523Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10523step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw10523step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10523step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10523step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10524 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw10524Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10524step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw10524step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10524step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10524step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10525 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw10525Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10525step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw10525step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10525step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw10525step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10525step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw10525step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10526 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw10526Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10526step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw10526step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10526step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10526step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10527 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw10527Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10527step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10527step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10528 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 2, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw10528Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10528step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 2, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw10528step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10528step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10528step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10529 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw10529Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10529step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw10529step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10529step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw10529step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10529step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw10529step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10530 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw10530Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10530step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw10530step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10530step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw10530step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10531 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw10531Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10531step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-2, 2, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw10531step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10531step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw10531step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10531step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw10531step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10532 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -2, 2]]
def raw10532Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10532step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -2, 2]]
def raw10532step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10532step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -2, 1], ![0, -2, 2]]
def raw10532step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10532step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw10532step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10533 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -2, 2]]
def raw10533Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10533step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -2, 2]]
def raw10533step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10533step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw10533step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10534 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -2, 2]]
def raw10534Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10534step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -2, 2]]
def raw10534step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10534step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw10534step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10535 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![0, -2, 2]]
def raw10535Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10535step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![0, -2, 2]]
def raw10535step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10535step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -2, 1], ![0, -2, 2]]
def raw10535step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10535step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw10535step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10536 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw10536Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10536step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw10536step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10536step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw10536step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10536step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw10536step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10537 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw10537Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10537step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw10537step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10537step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw10537step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10537step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw10537step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10537step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw10537step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10538 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -2, 2]]
def raw10538Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10538step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -2, 2]]
def raw10538step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10538step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -2, 1], ![0, -2, 2]]
def raw10538step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10538step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw10538step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10538step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw10538step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10539 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw10539Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10539step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw10539step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10539step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw10539step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10539step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10539step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw10540Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10540step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw10540step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10540step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw10540step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10540step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10540step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10541 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw10541Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10541step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw10541step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10541step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw10541step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10541step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw10541step2Labels : Fin 2 → Fin 3 := ![0, 2]

def raw10541step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw10541step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw10542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw10542Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10542step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw10542step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10542step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw10542step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10542step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10542step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10542step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10542step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10543 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw10543Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10543step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw10543step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10543step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw10543step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10543step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw10543step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10543step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10543step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10543step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10543step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10544 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw10544Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10544step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw10544step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10544step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw10544step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10545 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw10545Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10545step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw10545step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10546 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw10546Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10546step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw10546step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10546step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw10546step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10547 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw10547Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10547step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw10547step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10547step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10547step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10548 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw10548Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10548step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw10548step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10548step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw10548step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10549 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw10549Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10549step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw10549step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10549step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw10549step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10550 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw10550Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10550step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw10550step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10551 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw10551Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10551step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw10551step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10551step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw10551step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10552 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw10552Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10552step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw10552step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10552step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10552step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10553 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw10553Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10553step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw10553step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10553step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw10553step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10554 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw10554Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10554step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw10554step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10554step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw10554step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10555 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw10555Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10555step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw10555step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10556 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw10556Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10556step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw10556step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10557 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![2, 0, -2]]
def raw10557Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10557step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![2, 0, -2]]
def raw10557step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10557step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![2, 0, -2]]
def raw10557step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10557step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw10557step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10558 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw10558Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10558step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw10558step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10558step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw10558step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10559 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw10559Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10559step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw10559step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10559step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw10559step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10560 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw10560Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10560step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw10560step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10561 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw10561Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10561step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw10561step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10562 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw10562Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10562step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw10562step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10562step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw10562step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10563 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 1, -2]]
def raw10563Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10563step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 1, -2]]
def raw10563step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10563step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![2, -1, -1], ![1, 1, -2]]
def raw10563step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10563step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10563step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10564 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw10564Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10564step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw10564step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10564step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw10564step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10565 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw10565Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10565step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw10565step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10565step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw10565step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10565step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw10565step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10566 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw10566Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10566step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw10566step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10566step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw10566step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10566step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw10566step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10567 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw10567Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10567step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw10567step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10567step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw10567step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10568 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw10568Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10568step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw10568step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10568step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw10568step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10569 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw10569Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10569step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw10569step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10569step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw10569step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10569step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw10569step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10570 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw10570Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10570step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw10570step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10570step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw10570step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10570step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw10570step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10571 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -2, 2]]
def raw10571Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10571step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -2, 2]]
def raw10571step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10571step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![0, -1, 1], ![0, -2, 2]]
def raw10571step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10571step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw10571step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10571step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw10571step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10572 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw10572Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10572step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw10572step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10572step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw10572step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10572step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw10572step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10572step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw10572step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10573 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw10573Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10573step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw10573step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw10573step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw10573step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10574 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -2, 2]]
def raw10574Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10574step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -2, 2]]
def raw10574step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10574step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw10574step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw10574step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw10574step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10575 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2]]
def raw10575Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10575step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2]]
def raw10575step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10575step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2]]
def raw10575step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10575step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 3, -3], ![0, -1, 1], ![0, -2, 2]]
def raw10575step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10575step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-2, 2]]
def raw10575step3Labels : Fin 2 → Fin 3 := ![1, 2]

def raw10575step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw10575step4Labels : Fin 2 → Fin 3 := ![1, 2]

def raw10575step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw10575step5Labels : Fin 2 → Fin 2 := ![0, 1]

def raw10576 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2]]
def raw10576Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10576step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2]]
def raw10576step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10576step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw10576step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10576step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw10576step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw10576step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw10576step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10577 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2]]
def raw10577Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10577step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw10577step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10577step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw10577step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10577step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw10577step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw10577step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw10577step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10578 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -3, 2]]
def raw10578Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10578step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -3, 2]]
def raw10578step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10578step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, -1, 1], ![1, -3, 2]]
def raw10578step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10578step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw10578step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10578step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw10578step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10578step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw10578step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10579 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -3, 2]]
def raw10579Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10579step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -3, 2]]
def raw10579step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10579step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw10579step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10579step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw10579step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10580 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -3, 2]]
def raw10580Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10580step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -3, 2]]
def raw10580step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10580step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw10580step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10580step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw10580step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10581 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![1, -3, 2]]
def raw10581Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10581step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![1, -3, 2]]
def raw10581step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10581step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, -1, 1], ![1, -3, 2]]
def raw10581step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10581step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10581step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10581step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10581step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10582 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10582Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10582step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10582step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10582step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10582step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10582step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10582step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10583 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10583Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10583step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10583step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10583step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10583step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10583step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10583step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10584 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10584Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10584step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10584step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10584step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10584step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10584step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw10584step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10584step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw10584step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10585 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![2, 1, -3]]
def raw10585Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10585step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw10585step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10585step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw10585step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10585step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![2, 1, -3]]
def raw10585step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10585step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw10585step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10585step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw10585step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10586 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw10586Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10586step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw10586step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10586step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw10586step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10586step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10586step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw10586step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10586step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10587 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10587Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10587step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10587step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10587step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw10587step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10588 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10588Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10588step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw10588step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10589 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10589Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10589step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10589step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10589step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw10589step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10590 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![2, 1, -3]]
def raw10590Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10590step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw10590step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10590step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![2, 1, -3]]
def raw10590step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10590step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10590step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10591 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw10591Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10591step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw10591step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10591step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw10591step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10592 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10592Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10592step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10592step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10592step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw10592step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10593 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10593Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10593step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw10593step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10594 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10594Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10594step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10594step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10594step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw10594step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10595 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, 0, 0], ![2, 1, -3]]
def raw10595Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10595step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 1, -3]]
def raw10595step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10595step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![2, 1, -3]]
def raw10595step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10595step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10595step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10596 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw10596Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10596step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw10596step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10596step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw10596step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10597 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10597Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10597step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10597step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10597step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10597step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10598 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10598Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10598step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10598step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10599 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10599Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10599step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10599step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10600 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![2, 1, -3]]
def raw10600Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10600step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10600step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10600step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10600step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10600step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw10600step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10601 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw10601Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10601step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw10601step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10601step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw10601step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10601step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw10601step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw10601step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw10601step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10602 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10602Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10602step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10602step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10602step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10602step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10603 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10603Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10603step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10603step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10604 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10604Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10604step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10604step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10605 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10605Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10605step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10605step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10605step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10605step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10606 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![1, 2, -3]]
def raw10606Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10606step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![1, 2, -3]]
def raw10606step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10606step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![2, -2, 0], ![1, 2, -3]]
def raw10606step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10606step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw10606step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10607 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw10607Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10607step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw10607step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10607step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw10607step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10608 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw10608Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10608step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw10608step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10608step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw10608step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10608step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw10608step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10609 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw10609Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10609step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw10609step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10609step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw10609step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10609step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw10609step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10610 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw10610Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10610step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw10610step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10610step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw10610step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10610step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw10610step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10610step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw10610step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10611 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw10611Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10611step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw10611step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10611step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw10611step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10611step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![3, 0, -3]]
def raw10611step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10611step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-3, 1, 2]]
def raw10611step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10611step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw10611step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10612 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10612Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10612step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10612step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10612step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10612step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10613 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10613Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10613step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10613step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10613step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10613step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10614 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10614Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10614step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10614step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10614step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10614step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10614step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw10614step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10615 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![2, 1, -3]]
def raw10615Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10615step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw10615step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10615step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw10615step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10615step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![2, 1, -3]]
def raw10615step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10615step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![2, -2, 0]]
def raw10615step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10616 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw10616Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10616step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw10616step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10616step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw10616step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10616step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10616step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10617 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10617Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10617step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10617step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10617step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10617step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10618 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10618Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10618step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10618step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10619 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10619Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10619step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10619step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10619step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10619step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10620 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![2, 1, -3]]
def raw10620Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10620step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw10620step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10620step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![2, 1, -3]]
def raw10620step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10620step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10620step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10621 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw10621Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10621step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw10621step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10621step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10621step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10622 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10622Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10622step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10622step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10622step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10622step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10623 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10623Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10623step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10623step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw10624 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10624Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10624step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10624step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10624step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10624step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10625 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, 0, 0], ![2, 1, -3]]
def raw10625Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10625step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 1, -3]]
def raw10625step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10625step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![2, 1, -3]]
def raw10625step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10625step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10625step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10626 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw10626Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10626step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw10626step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10626step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10626step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10627 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10627Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10627step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10627step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10627step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10627step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10627step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw10627step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10628 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10628Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10628step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10628step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10628step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw10628step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10629 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10629Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10629step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10629step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10629step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw10629step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10630 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![2, 1, -3]]
def raw10630Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10630step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10630step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10630step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10630step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10630step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw10630step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10630step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 1, -2], ![2, -3, 1]]
def raw10630step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10631 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw10631Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10631step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw10631step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10631step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw10631step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10631step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw10631step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10632 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10632Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10632step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10632step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10632step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10632step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10632step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw10632step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10633 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10633Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10633step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10633step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10633step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw10633step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10634 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10634Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10634step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10634step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10634step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw10634step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10635 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10635Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10635step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10635step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10635step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10635step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10635step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw10635step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10636 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![1, 2, -3]]
def raw10636Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10636step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![1, 2, -3]]
def raw10636step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10636step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![2, -2, 0], ![1, 2, -3]]
def raw10636step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10636step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw10636step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10637 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw10637Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw10637step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10637step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw10637step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10637step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw10637step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10638 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw10638Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10638step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw10638step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10638step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw10638step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10639 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw10639Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10639step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw10639step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10639step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw10639step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10640 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw10640Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10640step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw10640step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10640step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw10640step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10640step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw10640step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10641 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw10641Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10641step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw10641step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10641step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw10641step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10641step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![3, 0, -3]]
def raw10641step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10641step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![3, -3, 0]]
def raw10641step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10642 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10642Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10642step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10642step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10642step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10642step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10642step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10642step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10643 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10643Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10643step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10643step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10643step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10643step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10643step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10643step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10644 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10644Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10644step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10644step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10644step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10644step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10644step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw10644step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10644step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw10644step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10645 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![2, 1, -3]]
def raw10645Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10645step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw10645step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10645step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw10645step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10645step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![2, 1, -3]]
def raw10645step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10645step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw10645step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10645step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw10645step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10646 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw10646Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10646step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw10646step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10646step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw10646step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10646step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10646step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10646step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10646step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10647 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10647Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10647step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10647step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10647step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw10647step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10647step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw10647step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10648 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10648Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10648step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw10648step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10648step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw10648step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10649 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10649Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10649step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10649step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10649step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw10649step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10649step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw10649step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10650 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![2, 1, -3]]
def raw10650Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10650step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw10650step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10650step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![2, 1, -3]]
def raw10650step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10650step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10650step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10650step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10650step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10651 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw10651Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10651step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw10651step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10651step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10651step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10651step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10651step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10652 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10652Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10652step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10652step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10652step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw10652step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10652step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw10652step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10653 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10653Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10653step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw10653step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10653step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw10653step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10654 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10654Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10654step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10654step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10654step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw10654step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10654step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw10654step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10655 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, 0, 0], ![2, 1, -3]]
def raw10655Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10655step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 1, -3]]
def raw10655step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10655step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![2, 1, -3]]
def raw10655step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10655step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10655step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10655step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10655step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10656 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw10656Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10656step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw10656step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10656step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10656step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10656step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10656step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10657 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10657Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10657step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10657step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10657step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10657step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10657step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw10657step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10657step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw10657step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10658 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10658Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10658step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10658step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10658step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw10658step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10658step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw10658step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10659 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10659Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10659step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10659step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10659step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw10659step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10659step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw10659step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10660 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![2, 1, -3]]
def raw10660Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10660step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10660step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10660step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10660step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10660step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw10660step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10660step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw10660step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10660step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw10660step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10661 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw10661Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10661step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw10661step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10661step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw10661step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10661step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw10661step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10661step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw10661step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10662 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10662Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10662step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10662step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10662step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10662step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10662step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw10662step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10662step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw10662step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10663 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10663Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10663step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10663step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10663step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw10663step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10663step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw10663step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10664 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10664Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10664step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10664step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw10664step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10664step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw10664step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10665 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10665Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10665step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10665step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10665step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10665step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10665step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw10665step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10665step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw10665step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10666 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![1, 2, -3]]
def raw10666Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10666step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![1, 2, -3]]
def raw10666step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10666step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![2, -2, 0], ![1, 2, -3]]
def raw10666step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10666step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw10666step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10666step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw10666step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10667 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw10667Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10667step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw10667step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10667step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw10667step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10667step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw10667step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10667step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw10667step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10668 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw10668Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10668step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw10668step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10668step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw10668step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10668step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw10668step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10669 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw10669Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10669step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw10669step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10669step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw10669step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10669step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw10669step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10670 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw10670Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10670step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw10670step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10670step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw10670step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10670step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw10670step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10670step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw10670step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10671 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw10671Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10671step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw10671step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10671step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw10671step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10671step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![3, 0, -3]]
def raw10671step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10671step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![2, 1, -3]]
def raw10671step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10671step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![2, 1, -3]]
def raw10671step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10672 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10672Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10672step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10672step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10672step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw10672step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10672step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw10672step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10673 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10673Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10673step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10673step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10673step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw10673step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10673step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw10673step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10674 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10674Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10674step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10674step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10674step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10674step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10674step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10674step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10674step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10674step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10675 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1]]
def raw10675Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10675step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1]]
def raw10675step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10675step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1]]
def raw10675step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10675step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw10675step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10675step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw10675step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10676 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw10676Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10676step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw10676step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10676step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw10676step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10676step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw10676step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10676step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw10676step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10677 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10677Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10677step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10677step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw10677step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10677step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw10677step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10678 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10678Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10678step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw10678step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10678step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw10678step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10679 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10679Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10679step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10679step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10679step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw10679step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10679step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw10679step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10680 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1]]
def raw10680Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10680step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1]]
def raw10680step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10680step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw10680step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10680step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw10680step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10681 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw10681Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10681step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw10681step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10681step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw10681step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10681step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw10681step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10682 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10682Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10682step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10682step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10682step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw10682step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10682step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw10682step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10683 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10683Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10683step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw10683step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10683step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw10683step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10684 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10684Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10684step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10684step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10684step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw10684step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10684step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw10684step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10685 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1]]
def raw10685Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10685step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1]]
def raw10685step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10685step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw10685step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10685step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw10685step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10686 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw10686Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10686step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw10686step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10686step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw10686step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10686step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw10686step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10687 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10687Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10687step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10687step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10687step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10687step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10687step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw10687step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10687step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw10687step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10688 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10688Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10688step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10688step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10688step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw10688step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10688step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw10688step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10689 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10689Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10689step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10689step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10689step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw10689step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10689step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw10689step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10690 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw10690Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10690step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw10690step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10690step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw10690step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10690step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10690step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10690step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10690step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10691 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw10691Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10691step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw10691step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10691step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw10691step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10691step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw10691step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10691step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw10691step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10692 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -3, 1]]
def raw10692Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10692step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -3, 1]]
def raw10692step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10692step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![2, -1, -1], ![2, -3, 1]]
def raw10692step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10692step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw10692step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10692step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw10692step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10693 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -3, 1]]
def raw10693Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10693step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -3, 1]]
def raw10693step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10693step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw10693step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10693step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw10693step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10694 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -3, 1]]
def raw10694Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10694step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -3, 1]]
def raw10694step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10694step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw10694step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10694step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw10694step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10695 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![2, -1, -1], ![2, -3, 1]]
def raw10695Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10695step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 2, -1], ![2, -1, -1], ![2, -3, 1]]
def raw10695step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10695step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -3, 1]]
def raw10695step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10695step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, -1, -1], ![2, 1, -3]]
def raw10695step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10695step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, -1, -1], ![2, 1, -3]]
def raw10695step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10696 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![1, -2, 1]]
def raw10696Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10696step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![1, -2, 1]]
def raw10696step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10696step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![2, -1, -1], ![1, -2, 1]]
def raw10696step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10696step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10696step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10696step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10696step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10697 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -4, 1]]
def raw10697Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -4, 1]]
def raw10697step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10697step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, 0, -1], ![3, -4, 1]]
def raw10697step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10697step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![3, 1, -4]]
def raw10697step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10697step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![3, 1, -4]]
def raw10697step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10698 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -4, 1]]
def raw10698Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10698step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -4, 1]]
def raw10698step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10698step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw10698step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10698step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw10698step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10699 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -4, 1]]
def raw10699Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10699step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -4, 1]]
def raw10699step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10699step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw10699step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10699step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw10699step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10700 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![3, -4, 1]]
def raw10700Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10700step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![3, -4, 1]]
def raw10700step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10700step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, 0, -1], ![3, -4, 1]]
def raw10700step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10700step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw10700step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10700step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw10700step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10701 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![3, -4, 1]]
def raw10701Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10701step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![3, -4, 1]]
def raw10701step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10701step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 1, -1], ![3, -4, 1]]
def raw10701step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10701step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw10701step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10701step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw10701step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10702 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10702Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10702step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10702step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10702step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10702step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10702step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, -2, 3], ![-2, 2, 0]]
def raw10702step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10702step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw10702step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10702step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw10702step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10703 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10703Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10703step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10703step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10703step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw10703step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10703step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10703step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10703step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10703step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10704 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10704Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10704step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10704step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10704step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw10704step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10704step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10704step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10704step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10704step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10705 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0]]
def raw10705Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10705step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0]]
def raw10705step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10705step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 1, -1], ![2, -2, 0]]
def raw10705step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10705step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw10705step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10705step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw10705step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10705step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw10705step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10706 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw10706Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10706step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw10706step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10706step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw10706step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10706step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw10706step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10706step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10706step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10706step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10706step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10707 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10707Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10707step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10707step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10707step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10707step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10707step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10707step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10708 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10708Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10708step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10708step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10708step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10708step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10709 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10709Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10709step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10709step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10709step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10709step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10710 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0]]
def raw10710Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10710step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0]]
def raw10710step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10710step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw10710step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10710step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10710step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10711 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw10711Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10711step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw10711step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10711step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw10711step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10711step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw10711step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10711step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10711step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10711step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10711step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10712 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10712Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10712step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10712step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10713 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10713Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10713step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10713step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10714 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10714Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10714step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10714step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10715 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0]]
def raw10715Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10715step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw10715step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10715step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw10715step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10716 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw10716Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10716step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw10716step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10716step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw10716step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10716step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10716step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10716step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10716step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10717 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10717Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10717step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10717step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10718 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10718Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10718step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10718step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10719 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10719Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10719step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10719step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10720 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw10720Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10720step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw10720step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10720step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw10720step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10721 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw10721Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10721step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw10721step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10721step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw10721step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10721step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10721step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10721step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10721step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10722 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -2, 0]]
def raw10722Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10722step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![2, -1, -1], ![2, -2, 0]]
def raw10722step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10722step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw10722step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10722step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw10722step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -2, 0]]
def raw10723Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10723step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![2, -1, -1], ![2, -2, 0]]
def raw10723step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10723step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -1, -1], ![2, -2, 0]]
def raw10723step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10723step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def raw10723step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10724 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -2, 0]]
def raw10724Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw10724step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10724step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw10724step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10725 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw10725Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10725step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw10725step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10725step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw10725step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10726 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0]]
def raw10726Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10726step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0]]
def raw10726step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10726step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![2, -1, -1], ![1, -1, 0]]
def raw10726step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10726step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw10726step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10726step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10726step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10726step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10726step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10727 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw10727Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10727step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw10727step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10727step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw10727step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10728 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw10728Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10728step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw10728step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10728step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, 0, -1], ![3, -3, 0]]
def raw10728step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10728step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -2, 3], ![-3, 3, 0]]
def raw10728step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10728step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw10728step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10728step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw10728step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10729 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw10729Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw10729step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10729step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw10729step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10730 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw10730Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10730step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw10730step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10730step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw10730step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10731 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0]]
def raw10731Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10731step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0]]
def raw10731step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10731step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![3, -3, 0]]
def raw10731step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10731step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw10731step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10732 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10732Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10732step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10732step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10732step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10732step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10732step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 3, -1]]
def raw10732step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10732step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw10732step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10732step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw10732step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10733 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10733Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10733step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10733step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10733step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw10733step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10733step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10733step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10733step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10733step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10734 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10734Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10734step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10734step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10734step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw10734step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10734step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10734step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10734step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10734step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10735 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0]]
def raw10735Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10735step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0]]
def raw10735step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10735step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 1, -1], ![2, -2, 0]]
def raw10735step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10735step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw10735step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10735step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw10735step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10735step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw10735step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw10736Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10736step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw10736step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10736step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw10736step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10736step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw10736step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10736step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10736step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10736step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10736step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10737 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10737Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10737step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10737step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10737step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10737step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10737step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw10737step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10737step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw10737step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10737step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw10737step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10738 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10738Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10738step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10738step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10738step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw10738step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10738step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw10738step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10738step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw10738step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10739 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10739Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10739step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10739step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10739step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw10739step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10739step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw10739step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10739step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw10739step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10740 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0]]
def raw10740Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10740step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0]]
def raw10740step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10740step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw10740step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10740step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw10740step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10740step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw10740step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10740step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw10740step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw10741Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10741step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw10741step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10741step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw10741step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10741step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw10741step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10741step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10741step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10741step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10741step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10742 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10742Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10742step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10742step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10742step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw10742step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10742step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10742step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10742step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10742step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10743Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10743step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10743step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10743step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 3, -1]]
def raw10743step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10743step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw10743step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10743step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw10743step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10744 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10744Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10744step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw10744step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10744step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10744step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10744step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10744step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0]]
def raw10745Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10745step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw10745step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10745step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw10745step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10745step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw10745step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10745step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw10745step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw10746Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10746step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw10746step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10746step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw10746step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10746step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10746step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10746step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10746step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10747 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10747Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10747step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10747step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10747step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw10747step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10747step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10747step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10747step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10747step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10748 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10748Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10748step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10748step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10748step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 3, -1]]
def raw10748step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10748step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw10748step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10748step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw10748step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10749 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10749Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10749step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw10749step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10749step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10749step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10749step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10749step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10750 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw10750Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10750step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw10750step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10750step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw10750step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10750step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw10750step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10750step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw10750step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw10751Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10751step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw10751step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10751step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw10751step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10751step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10751step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10751step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10751step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical84
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw10752 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -2, 0]]
def raw10752Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10752step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![2, -1, -1], ![2, -2, 0]]
def raw10752step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10752step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw10752step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10752step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw10752step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10752step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw10752step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10752step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw10752step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10753 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -2, 0]]
def raw10753Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10753step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![2, -1, -1], ![2, -2, 0]]
def raw10753step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10753step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -1, -1], ![2, -2, 0]]
def raw10753step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10753step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, -1, 2], ![-2, 3, -1]]
def raw10753step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10753step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]
def raw10753step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10753step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]
def raw10753step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10754 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -2, 0]]
def raw10754Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10754step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw10754step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10754step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw10754step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10754step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw10754step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10754step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw10754step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw10755Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10755step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw10755step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10755step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw10755step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10755step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw10755step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10755step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw10755step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0]]
def raw10756Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10756step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0]]
def raw10756step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10756step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![2, -1, -1], ![1, -1, 0]]
def raw10756step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10756step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw10756step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10756step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10756step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10756step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10756step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw10757Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10757step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw10757step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10757step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw10757step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10757step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 0, 1], ![-2, 2, 0]]
def raw10757step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10757step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw10757step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10757step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw10757step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10758 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw10758Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10758step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw10758step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10758step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, 0, -1], ![3, -3, 0]]
def raw10758step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10758step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![3, -2, -1]]
def raw10758step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10758step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![3, -2, -1]]
def raw10758step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10759 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw10759Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10759step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw10759step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10759step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw10759step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10759step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw10759step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw10760Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10760step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw10760step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10760step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw10760step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10760step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw10760step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0]]
def raw10761Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10761step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0]]
def raw10761step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10761step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![3, -3, 0]]
def raw10761step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10761step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -1, 0], ![2, -2, 0]]
def raw10761step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10761step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -1, 0], ![2, -2, 0]]
def raw10761step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10762Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10762step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10762step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10762step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10762step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10762step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10763Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10763step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10763step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10763step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10763step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10764 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10764Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10764step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10764step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10764step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10764step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10765Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10765step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10765step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10765step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10765step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10766 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0]]
def raw10766Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10766step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0]]
def raw10766step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10766step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw10766step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10766step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10766step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10767 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw10767Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10767step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw10767step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10767step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw10767step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10767step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw10767step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10768 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![0, 0], ![0, 0], ![1, -1], ![0, 0]]
def raw10768Labels : Fin 2 → Fin 2 := ![0, 1]

def raw10768step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![0, 0], ![0, 0], ![1, -1]]
def raw10768step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw10768step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![0, 0], ![1, -1]]
def raw10768step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw10768step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![1, -1]]
def raw10768step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw10768step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw10768step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw10769 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10769Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10769step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10769step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10769step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw10769step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10769step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw10769step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10769step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw10769step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10770 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10770Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10770step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10770step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10770step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10770step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10770step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10770step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10771 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10771Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10771step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10771step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10771step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10771step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10771step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10771step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10772 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw10772Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10772step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw10772step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10772step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![2, 0, -2]]
def raw10772step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10772step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![2, 0, -2]]
def raw10772step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10772step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![0, -2, 2], ![-2, 2, 0]]
def raw10772step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10772step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -2, 0]]
def raw10772step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10773 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw10773Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10773step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw10773step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10773step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2]]
def raw10773step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10773step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw10773step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10773step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw10773step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10774 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10774Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10774step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -3, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10774step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10774step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -3, 2], ![1, -1, 0], ![2, 0, -2]]
def raw10774step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10774step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw10774step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10774step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw10774step3Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10774step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw10774step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10775 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -3, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10775Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10775step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -3, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10775step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10775step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw10775step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10775step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw10775step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10775step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw10775step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10776 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -3, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10776Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10776step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -3, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10776step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10776step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw10776step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10776step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw10776step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10776step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw10776step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10777 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw10777Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10777step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -3, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw10777step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10777step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -3, 2], ![0, 0, 0], ![2, 0, -2]]
def raw10777step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10777step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -3, 2], ![2, 0, -2]]
def raw10777step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10777step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-3, 2, 1]]
def raw10777step3Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10777step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw10777step4Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10777step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw10777step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw10778Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10778step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -3, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw10778step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10778step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -3, 2], ![1, -1, 0], ![1, 1, -2]]
def raw10778step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10778step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw10778step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10778step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw10778step3Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10778step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw10778step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10779 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10779Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10779step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10779step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10779step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10779step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10779step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10779step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10780 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10780Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10780step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10780step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10780step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10780step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10780step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10780step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10781 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10781Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10781step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10781step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10781step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10781step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10782 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw10782Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10782step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw10782step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10782step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw10782step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10782step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10782step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10782step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10782step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10783 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw10783Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10783step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw10783step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10783step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw10783step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10783step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10783step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10783step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10783step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10784Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10784step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10784step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10784step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10784step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10784step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10784step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10785 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10785Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10785step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10785step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10785step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10785step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10785step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10785step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10786Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10786step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10786step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10786step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10786step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw10787Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10787step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10787step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10787step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw10787step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10787step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10787step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10787step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10787step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10788 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw10788Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10788step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw10788step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10788step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw10788step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10788step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10788step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10788step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10788step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10789 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw10789Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10789step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw10789step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10789step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw10789step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10789step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw10789step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10789step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw10789step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10790 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw10790Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10790step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw10790step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10790step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -2, 0], ![2, 0, -2]]
def raw10790step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10790step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw10790step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10790step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw10790step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw10791Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10791step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw10791step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10791step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw10791step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10791step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw10791step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw10792Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10792step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw10792step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10792step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw10792step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10792step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw10792step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw10793Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10793step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw10793step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10793step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![2, -2, 0], ![1, 1, -2]]
def raw10793step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10793step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw10793step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10793step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw10793step3Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10793step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw10793step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10794 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw10794Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10794step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw10794step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10794step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw10794step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10794step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw10794step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10794step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw10794step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10795 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw10795Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10795step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw10795step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10795step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![3, -1, -2]]
def raw10795step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10795step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw10795step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10795step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw10795step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10796 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw10796Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10796step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw10796step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10796step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw10796step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10796step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw10796step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10797 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw10797Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10797step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw10797step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10797step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw10797step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10797step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw10797step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10798 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw10798Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10798step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw10798step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10798step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![3, -1, -2]]
def raw10798step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10798step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![3, -1, -2]]
def raw10798step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10798step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw10798step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10798step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw10798step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10799 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10799Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10799step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10799step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10799step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![1, -1, 0], ![2, -1, -1]]
def raw10799step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10799step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 3, -1]]
def raw10799step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10799step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw10799step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10799step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw10799step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10800 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10800Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10800step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10800step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10800step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw10800step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10800step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10800step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10800step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10800step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10801 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10801Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10801step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10801step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10801step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw10801step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10801step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10801step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10801step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10801step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10802 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw10802Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10802step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw10802step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10802step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![2, -1, -1]]
def raw10802step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10802step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]
def raw10802step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10802step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![-1, -1, 2], ![-2, 2, 0]]
def raw10802step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10802step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw10802step4Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10802step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw10802step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw10803Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10803step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw10803step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10803step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw10803step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10803step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw10803step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10803step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10803step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10803step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10803step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10804 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10804Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10804step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10804step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10804step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw10804step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10804step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw10804step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10805 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10805Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10805step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10805step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10805step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw10805step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10806 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10806Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10806step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10806step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10806step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw10806step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10807 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw10807Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10807step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw10807step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10807step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![2, -1, -1]]
def raw10807step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10807step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def raw10807step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10808 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw10808Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10808step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw10808step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10808step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw10808step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10808step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw10808step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10808step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10808step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10808step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10808step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10809 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10809Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10809step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10809step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10810 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10810Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10810step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10810step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10811Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10811step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10811step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10812 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw10812Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10812step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw10812step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10812step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw10812step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10812step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw10812step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10812step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10812step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10812step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10812step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10813 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw10813Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10813step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw10813step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10813step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw10813step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10813step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10813step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10813step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10813step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10814 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10814Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10814step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10814step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10815 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10815Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10815step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10815step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10816 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10816Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10816step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10816step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10817 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw10817Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10817step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10817step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10817step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw10817step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10817step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw10817step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10817step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10817step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10817step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10817step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10818 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw10818Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10818step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw10818step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10818step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw10818step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10818step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10818step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10818step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10818step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10819 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw10819Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10819step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw10819step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10819step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw10819step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10820 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw10820Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10820step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw10820step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10820step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def raw10820step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10821 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw10821Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10821step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw10821step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10821step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw10821step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10822 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw10822Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10822step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw10822step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10822step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw10822step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10823 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1]]
def raw10823Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10823step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1]]
def raw10823step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10823step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![2, -2, 0], ![1, 0, -1]]
def raw10823step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10823step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10823step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10824 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw10824Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10824step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw10824step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10824step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw10824step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10825 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw10825Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10825step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw10825step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10825step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw10825step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10826 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw10826Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10826step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw10826step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10826step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw10826step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10827 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw10827Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10827step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw10827step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10827step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw10827step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10828 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1]]
def raw10828Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10828step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1]]
def raw10828step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10828step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![3, -2, -1]]
def raw10828step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10828step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw10828step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10829 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10829Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10829step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10829step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10829step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![1, -1, 0], ![2, -1, -1]]
def raw10829step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10829step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![-1, 2, -1], ![-2, -1, 3]]
def raw10829step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10829step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw10829step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10830 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10830Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10830step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10830step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10830step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw10830step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10830step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw10830step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10831 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10831Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10831step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10831step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10831step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw10831step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10831step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw10831step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10832 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw10832Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10832step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw10832step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10832step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![2, -1, -1]]
def raw10832step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10832step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]
def raw10832step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10832step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -2, -1], ![-1, 2, -1], ![-2, 0, 2]]
def raw10832step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10832step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw10832step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10833 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw10833Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10833step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw10833step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10833step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw10833step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10833step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw10833step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10833step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10833step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10834 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10834Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10834step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10834step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10834step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw10834step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10834step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw10834step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10835 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10835Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10835step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10835step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10835step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw10835step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10836 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10836Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10836step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10836step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10836step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw10836step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10837 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw10837Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10837step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw10837step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10837step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![2, -1, -1]]
def raw10837step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10837step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def raw10837step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10837step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![2, -1, -1]]
def raw10837step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10838 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw10838Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10838step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw10838step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10838step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw10838step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10838step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![0, 1, -1], ![-1, 1, 0], ![-2, 1, 1]]
def raw10838step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10838step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw10838step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10839 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10839Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10839step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10839step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10839step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10839step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10840 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10840Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10840step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10840step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10840step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10840step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10841 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10841Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10841step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10841step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10842 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw10842Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10842step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw10842step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10842step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw10842step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10842step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw10842step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10843 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw10843Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10843step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw10843step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10843step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw10843step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10844 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10844Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10844step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10844step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10844step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10844step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10845 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10845Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10845step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10845step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10845step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10845step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10846 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10846Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10846step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10846step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw10847Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10847step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10847step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10847step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw10847step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10847step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw10847step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw10848Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10848step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw10848step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10848step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw10848step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw10849Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10849step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw10849step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10849step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw10849step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10849step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw10849step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw10850Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10850step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw10850step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10850step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def raw10850step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10850step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![2, -1, -1], ![2, 0, -2]]
def raw10850step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw10851Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10851step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw10851step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10851step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw10851step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw10852Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10852step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw10852step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10852step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw10852step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1]]
def raw10853Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10853step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1]]
def raw10853step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10853step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![2, -2, 0], ![1, 0, -1]]
def raw10853step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10853step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw10853step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw10854Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10854step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw10854step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10854step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw10854step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10854step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw10854step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw10855Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10855step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw10855step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10855step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw10855step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10855step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, -2, 3], ![-3, 3, 0]]
def raw10855step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10855step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 2, -3], ![3, -3, 0]]
def raw10855step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw10856Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10856step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw10856step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10856step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 3, 0]]
def raw10856step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10856step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw10856step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw10857Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10857step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw10857step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10857step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 3, 0]]
def raw10857step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10857step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw10857step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10858 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1]]
def raw10858Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10858step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1]]
def raw10858step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10858step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![3, -2, -1]]
def raw10858step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10858step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw10858step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10858step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-3, 3, 0]]
def raw10858step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10858step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![3, -3, 0]]
def raw10858step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10859Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10859step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10859step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10859step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![1, -1, 0], ![2, -1, -1]]
def raw10859step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10859step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 3, -1]]
def raw10859step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10859step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw10859step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10859step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw10859step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10860Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10860step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10860step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10860step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw10860step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10860step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10860step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10860step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10860step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10861Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10861step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10861step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10861step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw10861step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10861step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10861step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10861step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10861step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw10862Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10862step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw10862step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10862step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![2, -1, -1]]
def raw10862step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10862step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]
def raw10862step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10862step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![-1, -1, 2], ![-2, 2, 0]]
def raw10862step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10862step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw10862step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10862step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw10862step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw10863Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10863step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw10863step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10863step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw10863step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10863step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw10863step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10863step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10863step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10863step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10863step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10864Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10864step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10864step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10864step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw10864step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10864step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw10864step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10864step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10864step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10864step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10864step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10865Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10865step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10865step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10865step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw10865step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10865step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10865step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10865step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10865step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10866Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10866step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10866step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10866step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw10866step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10866step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10866step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10866step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10866step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw10867Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10867step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw10867step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10867step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![2, -1, -1]]
def raw10867step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10867step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def raw10867step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10867step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![-1, -1, 2], ![-2, 1, 1]]
def raw10867step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10867step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def raw10867step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10867step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def raw10867step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw10868Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10868step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw10868step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10868step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw10868step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10868step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw10868step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10868step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10868step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10868step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10868step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10869Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10869step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10869step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10869step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw10869step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10869step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10869step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10869step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10869step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10870Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10870step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10870step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10870step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 3, -1]]
def raw10870step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10870step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw10870step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10870step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw10870step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10871Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10871step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw10871step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10871step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10871step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10871step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10871step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw10872Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10872step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw10872step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10872step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw10872step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10872step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw10872step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10872step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10872step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10872step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10872step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw10873Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10873step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw10873step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10873step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw10873step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10873step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10873step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10873step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10873step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10874Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10874step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10874step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10874step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw10874step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10874step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10874step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10874step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10874step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10875Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10875step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10875step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10875step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 3, -1]]
def raw10875step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10875step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw10875step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10875step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw10875step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10876Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10876step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw10876step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10876step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10876step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10876step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10876step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw10877Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10877step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10877step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10877step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw10877step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10877step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw10877step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10877step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10877step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10877step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10877step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw10878Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10878step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw10878step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10878step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw10878step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10878step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10878step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10878step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10878step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw10879Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10879step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw10879step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10879step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw10879step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10879step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw10879step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10879step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw10879step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10879step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw10879step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical85
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw10880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw10880Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10880step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw10880step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10880step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def raw10880step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10880step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, -1, 2], ![-2, 3, -1]]
def raw10880step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10880step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]
def raw10880step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10880step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]
def raw10880step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10881 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw10881Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10881step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw10881step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10881step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw10881step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10881step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw10881step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10881step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw10881step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw10882Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10882step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw10882step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10882step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw10882step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10882step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw10882step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10882step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw10882step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1]]
def raw10883Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10883step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1]]
def raw10883step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10883step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![2, -2, 0], ![1, 0, -1]]
def raw10883step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10883step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw10883step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10883step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10883step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10883step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10883step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw10884Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10884step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw10884step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10884step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw10884step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10884step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw10884step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10884step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw10884step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10884step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw10884step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10885 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw10885Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10885step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw10885step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10885step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw10885step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10885step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -2, 3], ![-2, 3, -1]]
def raw10885step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10885step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]
def raw10885step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10885step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]
def raw10885step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10886 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw10886Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10886step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw10886step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10886step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw10886step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10886step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw10886step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10886step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw10886step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw10887Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10887step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw10887step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10887step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw10887step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10887step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw10887step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10887step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw10887step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10888 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1]]
def raw10888Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10888step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1]]
def raw10888step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10888step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![3, -2, -1]]
def raw10888step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10888step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw10888step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10888step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![-1, -2, 3], ![-2, 2, 0]]
def raw10888step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10888step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![2, -2, 0]]
def raw10888step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10888step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![2, -2, 0]]
def raw10888step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10889Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10889step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10889step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10889step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw10889step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10890 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10890Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10890step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10890step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10890step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw10890step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10890step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw10890step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10891 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10891Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10891step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10891step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10892 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10892Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10892step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10892step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10893 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw10893Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10893step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw10893step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10893step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw10893step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10894 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw10894Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10894step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw10894step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10894step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw10894step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10895 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![0, 0], ![0, 0], ![0, 0], ![1, -1]]
def raw10895Labels : Fin 2 → Fin 2 := ![0, 1]

def raw10895step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![0, 0], ![0, 0], ![1, -1]]
def raw10895step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw10895step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![0, 0], ![1, -1]]
def raw10895step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw10895step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![1, -1]]
def raw10895step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw10895step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw10895step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw10896 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10896Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10896step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10896step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10896step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw10896step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10897 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10897Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10897step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10897step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10897step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw10897step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10898 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw10898Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10898step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw10898step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10898step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![2, -1, -1]]
def raw10898step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10898step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def raw10898step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10899 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw10899Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10899step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw10899step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10899step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw10899step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10899step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw10899step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10900 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10900Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10900step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10900step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10900step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw10900step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10900step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw10900step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10900step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw10900step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10901 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10901Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10901step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10901step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10901step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw10901step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10901step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10901step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10901step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10901step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10902 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10902Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10902step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10902step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10902step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw10902step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10902step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10902step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10902step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10902step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10903 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw10903Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10903step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw10903step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10903step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1]]
def raw10903step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10903step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw10903step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10903step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw10903step3Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10903step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw10903step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10904 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw10904Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10904step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw10904step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10904step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw10904step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10904step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw10904step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10904step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw10904step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10905 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -3, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10905Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10905step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -3, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10905step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10905step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -3, 2], ![1, 0, -1], ![2, -1, -1]]
def raw10905step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10905step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw10905step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10905step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw10905step3Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10905step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw10905step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10906 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -3, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10906Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10906step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -3, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10906step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10906step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw10906step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10906step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw10906step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10906step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw10906step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10907 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -3, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10907Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10907step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -3, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10907step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10907step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw10907step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10907step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw10907step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10907step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw10907step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10908 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw10908Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10908step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -3, 2], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw10908step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10908step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -3, 2], ![0, 1, -1], ![2, -1, -1]]
def raw10908step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10908step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw10908step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10908step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw10908step3Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10908step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw10908step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -3, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw10909Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10909step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -3, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw10909step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10909step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw10909step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10909step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw10909step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10909step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw10909step3Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10909step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw10909step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10910Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10910step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10910step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10910step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw10910step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10910step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10910step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10910step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10910step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10911 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10911Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10911step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10911step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10911step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10911step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10911step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10911step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10912 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10912Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10912step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw10912step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10912step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10912step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10912step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10912step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10913 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw10913Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10913step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw10913step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10913step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw10913step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10913step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10913step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10913step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10913step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10914 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw10914Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10914step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw10914step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10914step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw10914step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10914step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10914step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10914step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10914step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10915 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10915Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10915step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10915step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10915step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw10915step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10915step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10915step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10915step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10915step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10916 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10916Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10916step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10916step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10916step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10916step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10916step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10916step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10917 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10917Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10917step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw10917step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10917step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10917step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10917step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10917step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10918 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw10918Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10918step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw10918step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10918step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw10918step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10918step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10918step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10918step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10918step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10919 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw10919Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10919step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw10919step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10919step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw10919step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10919step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10919step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10919step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10919step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10920 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw10920Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10920step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw10920step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10920step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw10920step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10920step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw10920step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10920step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw10920step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10921 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw10921Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10921step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw10921step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10921step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -1, -1], ![2, -1, -1]]
def raw10921step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10921step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw10921step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10921step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw10921step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10922 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw10922Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10922step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw10922step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10922step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw10922step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10922step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw10922step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10923 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw10923Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10923step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw10923step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10923step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw10923step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10923step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw10923step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10924 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw10924Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10924step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw10924step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10924step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1]]
def raw10924step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10924step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw10924step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10924step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10924step3Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10924step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10924step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10925 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw10925Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10925step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw10925step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10925step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw10925step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10925step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-2, 2, 0], ![-2, -1, 3]]
def raw10925step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10925step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw10925step3Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10925step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw10925step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10926 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw10926Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10926step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw10926step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10926step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![3, -2, -1]]
def raw10926step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10926step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw10926step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10926step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw10926step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10927 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw10927Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10927step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw10927step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10927step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, -1, 3]]
def raw10927step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10927step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw10927step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10927step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw10927step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw10928Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10928step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw10928step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10928step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, -1, 3]]
def raw10928step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10928step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw10928step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10928step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw10928step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw10929Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10929step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw10929step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10929step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 1, -1], ![3, -2, -1]]
def raw10929step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10929step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-2, 2, 0], ![-2, -1, 3]]
def raw10929step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10929step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw10929step3Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10929step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw10929step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10930Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10930step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10930step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10930step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw10930step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10930step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw10930step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10931Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10931step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10931step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10931step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw10931step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10932Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10932step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10932step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10932step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw10932step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10933 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw10933Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10933step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw10933step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10933step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1]]
def raw10933step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10933step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw10933step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10934 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw10934Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10934step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw10934step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10934step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw10934step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10934step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw10934step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -3, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10935Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10935step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -3, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10935step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10935step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -3, 2], ![1, 0, -1], ![2, -1, -1]]
def raw10935step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10935step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw10935step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -3, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10936Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -3, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10936step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10936step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw10936step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -3, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10937Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10937step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -3, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10937step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10937step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw10937step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw10938Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10938step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -3, 2], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw10938step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10938step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -3, 2], ![0, 1, -1], ![2, -1, -1]]
def raw10938step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10938step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw10938step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -3, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw10939Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10939step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -3, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw10939step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10939step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw10939step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10939step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw10939step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10940Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10940step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10940step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10940step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10940step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10941Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10941step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10941step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10941step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10941step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10942Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10942step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10942step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw10943Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10943step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw10943step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10943step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw10943step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw10944Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10944step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw10944step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10944step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw10944step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10945Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10945step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10945step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10945step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10945step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10946Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10946step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10946step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10946step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10946step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10947Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10947step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10947step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw10948Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10948step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw10948step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10948step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw10948step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw10949Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10949step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw10949step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10949step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw10949step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw10950Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10950step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw10950step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10950step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw10950step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10950step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw10950step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10951 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw10951Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10951step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw10951step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10951step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -1, -1], ![2, -1, -1]]
def raw10951step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10951step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw10951step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw10952Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10952step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw10952step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10952step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw10952step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw10953Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10953step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw10953step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10953step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw10953step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw10954Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10954step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw10954step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10954step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1]]
def raw10954step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10954step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw10954step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw10955Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10955step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw10955step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10955step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw10955step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10955step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw10955step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw10956Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10956step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw10956step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10956step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![3, -2, -1]]
def raw10956step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10956step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw10956step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw10957Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10957step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw10957step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10957step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw10957step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw10958Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10958step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw10958step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10958step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw10958step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw10959Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10959step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw10959step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10959step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 1, -1], ![3, -2, -1]]
def raw10959step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10959step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw10959step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10960 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10960Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10960step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10960step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10960step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw10960step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw10960step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw10960step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10961 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw10961Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10961step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw10961step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10961step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw10961step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10961step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw10961step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw10961step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw10961step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![3, -3, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10962Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10962step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![3, -3, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10962step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10962step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 4, -3], ![3, -3, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10962step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10962step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw10962step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10962step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw10962step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10962step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw10962step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10963 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10963Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10963step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10963step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10963step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw10963step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10963step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw10963step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10963step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw10963step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10964 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10964Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10964step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10964step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10964step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw10964step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10964step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw10964step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10964step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw10964step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10965 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw10965Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10965step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw10965step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10965step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw10965step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10965step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw10965step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10965step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw10965step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10965step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw10965step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10966 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw10966Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10966step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw10966step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10966step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw10966step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10966step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-3, 3, 0]]
def raw10966step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10966step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw10966step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10966step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw10966step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10967Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10967step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10967step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10967step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw10967step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10967step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw10967step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10967step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw10967step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10968 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10968Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10968step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw10968step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10968step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw10968step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10968step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw10968step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10969 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw10969Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10969step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw10969step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10969step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw10969step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10969step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw10969step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10969step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw10969step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10970Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10970step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10970step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10970step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw10970step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10970step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw10970step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10970step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw10970step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10971 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10971Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10971step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw10971step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10971step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw10971step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10971step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw10971step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10972 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw10972Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10972step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw10972step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10972step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw10972step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10972step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw10972step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10972step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw10972step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw10973Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10973step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw10973step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10973step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw10973step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10973step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw10973step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10973step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10973step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10973step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10973step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10974 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw10974Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10974step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw10974step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10974step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw10974step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10974step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10974step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10974step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10974step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10975 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw10975Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10975step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw10975step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10975step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw10975step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10975step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw10975step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10975step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10975step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10975step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10975step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10976Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10976step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10976step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10976step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10976step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10976step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw10976step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10976step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw10976step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10976step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw10976step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10977 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10977Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10977step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10977step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10977step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw10977step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10977step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw10977step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10977step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw10977step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10978 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10978Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10978step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10978step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10978step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw10978step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10979 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw10979Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10979step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw10979step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10979step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw10979step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10979step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw10979step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![3, -3, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10980Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10980step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![3, -3, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10980step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10980step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 4, -3], ![3, -3, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10980step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10980step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw10980step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10981 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10981Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10981step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10981step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10981step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw10981step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10982 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10982Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10982step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10982step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10982step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw10982step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10983 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw10983Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10983step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw10983step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10983step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw10983step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10983step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -3, 3], ![-1, 2, -1], ![-2, 1, 1]]
def raw10983step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10983step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -2, 1], ![2, -1, -1]]
def raw10983step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10984 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw10984Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10984step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw10984step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10984step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw10984step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10984step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -3, 3], ![-1, 1, 0], ![-2, 2, 0]]
def raw10984step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10984step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -1, 0], ![2, -2, 0]]
def raw10984step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10985Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10985step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10985step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10985step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw10985step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10986 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10986Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10986step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw10986step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10987 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw10987Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10987step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw10987step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10987step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw10987step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10988Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10988step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10988step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10988step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw10988step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10989 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10989Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10989step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw10989step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10990 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw10990Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10990step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw10990step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10990step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw10990step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw10991Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10991step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw10991step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10991step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw10991step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10991step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw10991step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10992 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw10992Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10992step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw10992step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10992step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw10992step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10993 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw10993Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10993step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw10993step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10993step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw10993step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10993step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10993step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10994Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10994step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10994step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10994step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10994step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10994step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw10994step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10995 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10995Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10995step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10995step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10995step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw10995step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10996 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10996Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10996step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10996step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10996step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10996step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10996step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10996step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10997 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw10997Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10997step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw10997step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10997step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw10997step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10997step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw10997step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10997step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw10997step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![3, -3, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10998Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10998step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![3, -3, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10998step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10998step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 4, -3], ![3, -3, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10998step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10998step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -3, -1], ![0, 1, -1], ![-1, 2, -1], ![-3, 0, 3]]
def raw10998step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10998step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw10998step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10998step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw10998step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10999 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10999Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10999step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10999step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10999step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw10999step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10999step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw10999step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11000 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11000Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11000step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11000step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11000step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw11000step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11000step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw11000step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11001 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw11001Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11001step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw11001step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11001step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw11001step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11001step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw11001step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11001step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw11001step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11002 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw11002Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11002step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw11002step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11002step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw11002step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11002step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw11002step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11002step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw11002step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11003Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11003step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11003step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11003step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw11003step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11003step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw11003step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11003step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw11003step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11004 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11004Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11004step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw11004step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11004step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw11004step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11004step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw11004step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11005 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw11005Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11005step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw11005step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11005step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw11005step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11005step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw11005step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11005step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw11005step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11006 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11006Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11006step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11006step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11006step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw11006step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11006step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw11006step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11006step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw11006step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11007 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11007Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11007step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw11007step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11007step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw11007step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11007step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw11007step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical86
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw11008 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw11008Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11008step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw11008step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11008step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw11008step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11008step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw11008step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11008step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw11008step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw11009Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11009step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw11009step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11009step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw11009step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11009step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -3, -1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw11009step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11009step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw11009step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11009step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw11009step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11010 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw11010Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11010step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw11010step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11010step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw11010step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11010step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw11010step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11010step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw11010step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11011 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw11011Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11011step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw11011step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11011step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw11011step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11011step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![-1, 1, 0], ![-2, 0, 2]]
def raw11011step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11011step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw11011step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11011step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw11011step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11012 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw11012Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11012step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw11012step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11012step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw11012step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11012step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -3, -1], ![0, 1, -1], ![-2, 2, 0], ![-2, 0, 2]]
def raw11012step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11012step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw11012step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11012step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw11012step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11013 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw11013Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11013step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw11013step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11013step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0], ![-2, 0, 2]]
def raw11013step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11013step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw11013step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11013step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw11013step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11014 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11014Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11014step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11014step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11014step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11014step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11014step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw11014step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11014step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11014step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11015 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![3, -3, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11015Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11015step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![3, -3, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11015step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11015step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 4, -3], ![3, -3, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11015step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11015step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw11015step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11015step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw11015step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11016 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11016Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11016step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11016step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11016step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw11016step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11016step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw11016step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11017Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11017step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11017step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw11017step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11017step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw11017step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11018 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw11018Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11018step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw11018step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11018step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw11018step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11018step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw11018step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11018step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11018step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11019 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw11019Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11019step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw11019step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11019step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw11019step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11019step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw11019step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11019step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw11019step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11020Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11020step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11020step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11020step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw11020step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11020step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw11020step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11020step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw11020step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11021Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11021step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11021step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11021step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw11021step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11021step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw11021step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11021step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw11021step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11022 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11022Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11022step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw11022step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11022step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11022step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11022step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11022step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11023 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0]]
def raw11023Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11023step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw11023step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11023step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw11023step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11023step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw11023step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11023step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw11023step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw11024Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11024step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11024step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11024step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw11024step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11024step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11024step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11024step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11024step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11025Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11025step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11025step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11025step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11025step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11026Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11026step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11026step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11026step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11026step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11027Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11027step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11027step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11028 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0]]
def raw11028Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11028step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw11028step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11028step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11028step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11029 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw11029Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11029step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11029step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11029step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11029step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11030 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11030Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11030step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11030step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11031 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11031Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11031step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11031step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11032 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11032Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11032step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11032step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11033 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0]]
def raw11033Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11033step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw11033step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11033step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11033step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11034 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw11034Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11034step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11034step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11034step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11034step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11035 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11035Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11036 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11036Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11037 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11037Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11037step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11037step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11038 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw11038Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11038step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw11038step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11039 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw11039Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11039step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11039step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11040 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -2, 0]]
def raw11040Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11040step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw11040step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11040step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw11040step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11041 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -2, 0]]
def raw11041Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11041step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw11041step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11041step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw11041step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11042 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![2, -2, 0]]
def raw11042Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11042step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![2, -1, -1], ![2, -2, 0]]
def raw11042step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11042step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw11042step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11043 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw11043Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11043step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw11043step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11044 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0]]
def raw11044Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11044step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw11044step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11044step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11044step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11045 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw11045Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11045step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw11045step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11046 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw11046Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11046step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw11046step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11046step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw11046step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11046step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw11046step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11046step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw11046step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11047 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw11047Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11047step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw11047step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11047step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw11047step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11047step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw11047step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11047step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw11047step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11048 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw11048Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11048step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw11048step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11049 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0]]
def raw11049Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11049step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw11049step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11050 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11050Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11050step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11050step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11050step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw11050step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11050step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw11050step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11050step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw11050step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11051 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11051Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11051step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11051step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11051step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw11051step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11051step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw11051step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11051step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw11051step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11052 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11052Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11052step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw11052step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11052step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11052step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11052step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11052step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11053 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0]]
def raw11053Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11053step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw11053step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11053step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw11053step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11053step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw11053step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11053step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw11053step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11054 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw11054Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11054step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11054step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11054step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw11054step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11054step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11054step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11054step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11054step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11055 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11055Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11055step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11055step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11055step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw11055step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11055step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11055step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11055step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11055step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11056 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11056Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11056step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11056step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11056step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw11056step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11056step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw11056step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11056step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw11056step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11057 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11057Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11057step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw11057step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11057step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11057step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11057step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11057step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11058 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0]]
def raw11058Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11058step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw11058step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11058step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw11058step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11058step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11058step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11058step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11058step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11059 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw11059Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11059step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11059step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11059step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw11059step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11059step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11059step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11059step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11059step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11060 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11060Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11060step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11060step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11060step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw11060step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11060step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11060step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11060step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11060step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11061 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11061Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11061step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11061step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11061step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw11061step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11061step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw11061step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11061step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw11061step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11062 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11062Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11062step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw11062step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11062step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11062step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11062step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11062step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11063 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0]]
def raw11063Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11063step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw11063step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11063step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw11063step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11063step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11063step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11063step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11063step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11064 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw11064Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11064step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11064step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11064step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw11064step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11064step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11064step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11064step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11064step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11065 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11065Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11065step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw11065step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11065step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11065step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11065step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11065step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11066 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11066Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11066step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw11066step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11066step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw11066step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11066step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw11066step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11067 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11067Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11067step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw11067step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11067step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw11067step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11067step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw11067step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11068 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw11068Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11068step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw11068step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11068step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw11068step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11068step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw11068step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11069 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw11069Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11069step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw11069step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11069step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11069step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11069step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11069step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11070 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -2, 0]]
def raw11070Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11070step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw11070step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11070step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw11070step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11070step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11070step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11070step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11070step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11071 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -2, 0]]
def raw11071Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11071step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw11071step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11071step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw11071step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11071step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11071step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11071step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11071step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11072 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![2, -2, 0]]
def raw11072Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11072step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![2, -1, -1], ![2, -2, 0]]
def raw11072step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11072step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw11072step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11072step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11072step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11072step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11072step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11073 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw11073Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11073step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw11073step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11073step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11073step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11073step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11073step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11074 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0]]
def raw11074Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11074step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw11074step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11074step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw11074step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11074step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11074step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11074step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11074step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11075 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw11075Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11075step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw11075step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11075step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw11075step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11075step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11075step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11075step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11075step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11076 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw11076Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11076step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw11076step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11076step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw11076step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11076step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw11076step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11077 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw11077Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11077step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw11077step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11077step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw11077step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11077step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw11077step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11078 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw11078Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11078step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11078step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11078step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11078step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11079 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0]]
def raw11079Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11079step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw11079step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11079step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw11079step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11079step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw11079step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11080 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11080Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11080step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11080step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11081 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11081Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11081step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11081step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11082 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11082Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11082step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11082step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11082step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11082step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11083 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11083Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11083step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11083step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11084 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0]]
def raw11084Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11084step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw11084step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11085 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw11085Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11085step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11085step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11085step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw11085step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11086 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![0, 0], ![1, -1], ![0, 0]]
def raw11086Labels : Fin 2 → Fin 2 := ![0, 1]

def raw11086step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![0, 0], ![1, -1]]
def raw11086step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw11086step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw11086step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw11087 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11087Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11087step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11087step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11087step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11087step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11088 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11088Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11088step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11088step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11088step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11088step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11089 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11089Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11089step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11089step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11090 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0]]
def raw11090Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11090step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw11090step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11090step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11090step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11091 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw11091Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11091step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11091step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11091step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11091step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11092 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11092Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11092step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11092step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11093 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11093Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11094 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -2, 0]]
def raw11094Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11094step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw11094step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11094step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw11094step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11095 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw11095Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11095step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw11095step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11096 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11096Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11096step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11096step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11097 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw11097Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11097step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw11097step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11098 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw11098Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11098step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw11098step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11099 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -2, 0]]
def raw11099Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11099step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw11099step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11099step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw11099step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11100 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![2, -2, 0]]
def raw11100Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11100step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![2, -1, -1], ![2, -2, 0]]
def raw11100step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11100step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw11100step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11101 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0]]
def raw11101Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11101step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw11101step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11101step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11101step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11102 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11102Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11102step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw11102step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11102step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw11102step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11102step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11102step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11103 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11103Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11103step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw11103step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11103step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw11103step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11103step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11103step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11104Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11104step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11104step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11104step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11104step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw11105Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11105step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw11105step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11105step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw11105step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11105step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0]]
def raw11105step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11105step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw11105step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11106 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11106Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11106step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11106step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11106step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw11106step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw11106step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11106step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw11106step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11106step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11107 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -2, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11107Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11107step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw11107step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11107step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11107step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11107step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11107step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11108Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11108step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw11108step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11108step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11108step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11108step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11108step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11109 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11109Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11109step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11109step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11109step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11109step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11110 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw11110Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11110step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw11110step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11110step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -1, 1], ![2, 0, -2]]
def raw11110step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11110step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11110step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11110step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11110step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11111 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11111Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11111step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11111step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11111step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw11111step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw11111step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11111step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw11111step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11111step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11112Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11112step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw11112step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11112step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11112step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11112step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11112step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11113 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11113Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11113step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw11113step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11113step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11113step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11113step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11113step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11114Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11114step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11114step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11114step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11114step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11115 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw11115Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11115step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![0, 0, 0], ![2, 0, -2]]
def raw11115step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11115step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw11115step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11115step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11115step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11115step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11115step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11116 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11116Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11116step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11116step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11116step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw11116step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw11116step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11116step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw11116step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11116step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11117 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11117Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11117step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11117step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11117step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11117step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11118 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11118Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11118step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11118step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11118step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11118step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11119 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11119Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11119step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11119step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11119step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11119step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11120 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw11120Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11120step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw11120step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11120step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11120step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11120step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11120step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11121 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11121Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11121step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw11121step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw11121step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11121step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw11121step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11121step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11122 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw11122Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11122step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw11122step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11122step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw11122step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11122step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw11122step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11123 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw11123Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11123step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw11123step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11123step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw11123step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11123step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw11123step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11124 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw11124Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11124step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw11124step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11124step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw11124step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11124step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw11124step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11125 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw11125Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11125step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw11125step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11125step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw11125step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11126 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw11126Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11126step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw11126step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11126step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw11126step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw11126step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11126step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw11126step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11126step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11127 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw11127Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11127step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw11127step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11127step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw11127step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11127step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw11127step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11128 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw11128Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11128step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw11128step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11128step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw11128step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11128step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw11128step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11129 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw11129Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11129step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw11129step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11129step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw11129step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11129step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw11129step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11130 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw11130Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11130step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw11130step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11130step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw11130step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11131 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw11131Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11131step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![3, -1, -2]]
def raw11131step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11131step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![3, -1, -2]]
def raw11131step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11131step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw11131step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11131step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw11131step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11132 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11132Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11132step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw11132step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11132step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11132step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11133 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11133Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11133step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw11133step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11133step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11133step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11134 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11134Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11134step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11134step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11135 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw11135Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11135step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw11135step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11135step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw11135step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11135step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw11135step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical87
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw11136 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11136Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11136step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11136step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11136step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw11136step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11137 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -2, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11137Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11137step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw11137step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11137step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11137step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11138 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11138Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11138step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw11138step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11138step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11138step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11139Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11139step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11139step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11140 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw11140Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11140step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw11140step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11140step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -1, 1], ![2, 0, -2]]
def raw11140step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11140step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11140step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11141 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11141Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11141step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11141step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11141step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11141step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11142 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11142Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11142step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw11142step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11142step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11142step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11143 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11143Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11143step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw11143step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11143step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11143step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11144 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11144Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11144step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11144step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11145 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw11145Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11145step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![0, 0, 0], ![2, 0, -2]]
def raw11145step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11145step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw11145step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11145step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11145step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11146 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11146Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11146step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11146step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11146step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11146step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11147 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11147Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11147step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11147step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11148 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11148Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11148step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11148step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11149 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11149Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11149step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11149step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw11150Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11150step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw11150step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11150step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11150step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11151 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11151Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11151step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw11151step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11152 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw11152Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11152step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw11152step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11152step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw11152step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11153 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw11153Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11153step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw11153step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11153step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw11153step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11154 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw11154Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11154step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw11154step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11154step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw11154step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11155 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw11155Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11155step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw11155step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11156 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw11156Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11156step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw11156step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11156step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw11156step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11157 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw11157Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11157step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw11157step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11157step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw11157step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11158 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw11158Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11158step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw11158step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11158step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw11158step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11159 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw11159Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11159step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw11159step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11159step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw11159step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11160 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw11160Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11160step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw11160step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11161 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw11161Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11161step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![3, -1, -2]]
def raw11161step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11161step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![3, -1, -2]]
def raw11161step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11161step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw11161step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11162 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw11162Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11162step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw11162step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11162step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw11162step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11162step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11162step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11162step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11162step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11163 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw11163Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11163step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw11163step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11163step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11163step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11163step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11163step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11164 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw11164Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11164step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw11164step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11164step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw11164step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11164step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11164step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11164step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11164step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11165 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw11165Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11165step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw11165step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11165step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw11165step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11165step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11165step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11165step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11165step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11166 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw11166Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11166step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw11166step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11166step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw11166step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11166step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw11166step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11166step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw11166step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11166step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw11166step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11167 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw11167Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11167step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw11167step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11167step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11167step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11167step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11167step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11168 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw11168Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11168step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw11168step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11168step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw11168step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11168step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11168step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11168step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11168step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11169 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw11169Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11169step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw11169step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11169step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw11169step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11169step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11169step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11169step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11169step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11170 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw11170Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11170step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw11170step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11170step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11170step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11170step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11170step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11171 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw11171Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11171step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw11171step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11171step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw11171step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11171step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11171step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11171step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11171step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw11172Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11172step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw11172step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11172step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11172step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11172step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11172step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11172step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11172step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11173 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw11173Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11173step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw11173step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11173step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw11173step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11173step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11173step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw11173step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11173step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11174 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw11174Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11174step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw11174step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11174step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw11174step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11175 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw11175Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11175step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw11175step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11176 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw11176Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11176step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw11176step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11176step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw11176step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11177 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw11177Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11177step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw11177step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11177step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw11177step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11178 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw11178Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11178step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw11178step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11178step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw11178step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11178step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw11178step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11179 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw11179Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11179step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw11179step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11180 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw11180Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11180step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw11180step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11180step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw11180step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11181 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw11181Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11181step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw11181step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11181step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11181step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11182 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw11182Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11182step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11182step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11183 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw11183Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11183step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw11183step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11183step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw11183step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11184 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw11184Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11184step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw11184step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11184step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11184step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11185 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw11185Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11185step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw11185step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11185step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw11185step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11185step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11185step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11186 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw11186Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11186step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw11186step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11186step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw11186step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11186step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11186step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11186step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11186step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11187 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw11187Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11187step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw11187step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11187step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11187step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11187step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11187step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11188 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw11188Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11188step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw11188step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11188step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw11188step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11188step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11188step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11188step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11188step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11189 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw11189Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11189step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw11189step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11189step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw11189step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11189step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11189step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11189step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11189step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11190 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw11190Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11190step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw11190step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11190step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw11190step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11190step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![-1, 1, 0], ![-2, 0, 2]]
def raw11190step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11190step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw11190step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11190step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw11190step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11191 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw11191Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11191step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw11191step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11191step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11191step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11191step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11191step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11192 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw11192Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11192step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw11192step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11192step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw11192step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11192step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11192step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11192step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11192step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11193 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw11193Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11193step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw11193step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11193step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw11193step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11193step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11193step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11193step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11193step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11194 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw11194Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11194step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw11194step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11194step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11194step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11194step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11194step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11195 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw11195Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11195step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw11195step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11195step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw11195step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11195step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11195step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11195step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11195step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11196 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw11196Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11196step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw11196step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11196step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw11196step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11196step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11196step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11196step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11196step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11197 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw11197Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11197step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw11197step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11197step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw11197step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11197step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw11197step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11197step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw11197step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11198 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw11198Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11198step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw11198step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11198step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw11198step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11198step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11198step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11199 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw11199Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11199step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw11199step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11199step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw11199step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11199step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11199step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw11200Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11200step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw11200step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11200step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw11200step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11200step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11200step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw11201Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11201step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw11201step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11201step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11201step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11201step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11201step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11202Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11202step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11202step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11202step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw11202step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11202step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11202step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11202step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11202step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11203 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11203Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11203step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11203step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11203step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw11203step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11203step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11203step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11203step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11203step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11204 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11204Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11204step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw11204step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11204step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11204step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11204step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11204step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11205 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw11205Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11205step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw11205step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11205step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw11205step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11205step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw11205step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11205step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11205step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11205step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11205step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11206 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11206Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11206step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw11206step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11206step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw11206step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11206step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11206step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11206step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11206step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11207 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11207Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11207step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11207step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11207step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11207step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11208 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11208Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11208step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11208step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11208step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11208step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11209 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11209Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11209step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11209step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11210 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw11210Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11210step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw11210step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11210step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw11210step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11210step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11210step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11211 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11211Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11211step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw11211step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11211step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11211step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11212 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11212Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11212step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11212step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11212step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11212step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11213 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11213Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11213step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11213step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11213step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11213step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11214 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11214Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11214step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11214step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11215 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw11215Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11215step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw11215step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11215step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11215step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11216 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11216Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11216step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw11216step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11216step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11216step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11217 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11217Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11218 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11218Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11219 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11219Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11219step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11219step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11220 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw11220Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11220step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11220step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11221Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11222 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw11222Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11222step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw11222step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw11223Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11223step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw11223step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11224 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw11224Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11224step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw11224step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11224step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw11224step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11225 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw11225Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11225step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw11225step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11226 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1]]
def raw11226Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11226step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw11226step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11226step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11226step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11227 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw11227Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11227step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw11227step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11228 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw11228Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11228step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw11228step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11229 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw11229Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11229step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw11229step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11229step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw11229step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11230 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw11230Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11230step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw11230step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11231 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1]]
def raw11231Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11231step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw11231step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11231step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw11231step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11232Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11232step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11232step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11232step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw11232step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11232step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11232step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11233 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11233Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11233step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11233step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11233step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw11233step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11233step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11233step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11234 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11234Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11234step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw11234step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11234step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw11234step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11235 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw11235Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11235step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw11235step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11235step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw11235step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11235step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw11235step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11235step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw11235step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11236 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11236Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11236step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw11236step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11236step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw11236step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11236step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11236step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11237 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11237Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11237step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11237step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11237step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11237step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11238 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11238Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11238step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11238step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11238step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11238step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11239 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11239Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11239step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11239step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11240 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw11240Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11240step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw11240step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11240step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw11240step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11240step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw11240step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11241 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11241Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11241step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw11241step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11241step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11241step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11242 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11242Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11242step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11242step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11242step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11242step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11243 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11243Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11243step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11243step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11243step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11243step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11244 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11244Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11244step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11244step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11245 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw11245Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11245step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw11245step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11245step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11245step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11245step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw11245step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11246 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11246Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11246step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw11246step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11246step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11246step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11247 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11247Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11247step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11247step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11248Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11248step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11248step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11249 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11249Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11249step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11249step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw11250Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11250step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11250step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11250step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw11250step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11251 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11251Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11251step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11251step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11252 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw11252Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11252step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw11252step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11252step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw11252step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11253 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw11253Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11253step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw11253step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11253step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw11253step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11254 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw11254Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11254step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw11254step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11254step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw11254step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11255 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw11255Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11255step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw11255step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11256 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1]]
def raw11256Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11256step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw11256step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11256step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw11256step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11256step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11256step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11257 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw11257Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11257step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw11257step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11257step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw11257step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11258 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw11258Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11258step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw11258step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11258step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw11258step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11258step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw11258step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11259 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw11259Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11259step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw11259step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11259step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw11259step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11259step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw11259step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11260 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw11260Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11260step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw11260step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11260step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw11260step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11261 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1]]
def raw11261Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11261step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw11261step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11261step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw11261step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11261step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-3, 3, 0]]
def raw11261step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11261step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw11261step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11262 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11262Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11262step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11262step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11262step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw11262step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11262step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11262step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11262step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11262step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11263 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11263Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11263step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11263step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11263step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw11263step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11263step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11263step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11263step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11263step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical88
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw11264 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11264Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11264step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw11264step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11264step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11264step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11264step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11264step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11265 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw11265Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11265step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw11265step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11265step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw11265step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11265step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw11265step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11265step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11265step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11265step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11265step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11266 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11266Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11266step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw11266step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11266step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw11266step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11266step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11266step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11266step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11266step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11267 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11267Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11267step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11267step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11267step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11267step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11267step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11267step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11267step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11267step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11268 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11268Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11268step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11268step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11268step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw11268step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11268step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11268step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11268step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11268step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11269 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11269Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11269step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11269step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11269step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11269step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11269step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11269step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11270 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw11270Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11270step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw11270step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11270step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw11270step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11270step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11270step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11270step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11270step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11270step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11270step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11271 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11271Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11271step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw11271step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11271step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw11271step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11271step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11271step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11271step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11271step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11272 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11272Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11272step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11272step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11272step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11272step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11272step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11272step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11272step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11272step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11273 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11273Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11273step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11273step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11273step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw11273step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11273step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11273step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11273step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11273step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11274 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11274Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11274step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11274step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11274step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11274step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11274step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11274step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11275 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw11275Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11275step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw11275step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11275step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11275step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11275step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11275step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11275step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11275step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11275step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11275step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11276 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11276Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11276step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw11276step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11276step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw11276step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11276step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11276step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11276step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11276step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11277 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11277Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11277step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw11277step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11277step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11277step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11277step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11277step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11278 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11278Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11278step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw11278step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11278step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11278step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11278step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11278step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11279 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11279Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11279step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw11279step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11279step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11279step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11279step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11279step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11280 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw11280Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11280step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11280step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11280step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw11280step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11280step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11280step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11280step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11280step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11281 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11281Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11281step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw11281step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11281step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11281step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11281step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11281step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11282 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw11282Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11282step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw11282step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11282step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw11282step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11282step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11282step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11282step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11282step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11283 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw11283Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11283step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw11283step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11283step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw11283step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11283step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11283step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11283step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11283step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11284 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw11284Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11284step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw11284step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11284step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw11284step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11284step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11284step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11284step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11284step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11285 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw11285Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11285step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw11285step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11285step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11285step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11285step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11285step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11286 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1]]
def raw11286Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11286step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw11286step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11286step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw11286step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11286step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11286step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11286step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11286step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11287 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw11287Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11287step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw11287step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11287step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw11287step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11287step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw11287step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11287step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw11287step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11288 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw11288Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11288step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw11288step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11288step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -2, 3]]
def raw11288step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11288step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw11288step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11288step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw11288step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11289 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw11289Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11289step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw11289step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11289step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -2, 3]]
def raw11289step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11289step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw11289step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11289step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw11289step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11290 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw11290Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11290step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw11290step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11290step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw11290step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11290step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw11290step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11291 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1]]
def raw11291Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11291step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw11291step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11291step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw11291step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11291step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw11291step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11291step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw11291step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11291step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw11291step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11292 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11292Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11292step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11292step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11293 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11293Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11293step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11293step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11294 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11294Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11294step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11294step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11294step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11294step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11295 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11295Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11295step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11295step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11296 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw11296Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11296step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw11296step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11296step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw11296step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11297 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11297Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11297step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw11297step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11298 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![0, 0], ![0, 0], ![1, -1]]
def raw11298Labels : Fin 2 → Fin 2 := ![0, 1]

def raw11298step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![0, 0], ![1, -1]]
def raw11298step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw11298step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw11298step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw11299 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11299Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11299step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11299step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11299step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11299step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11300 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11300Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11300step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11300step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11300step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11300step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11301 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11301Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11302 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw11302Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11302step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw11302step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11303 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw11303Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11303step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw11303step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11304 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11304Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11304step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11304step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11304step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11304step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11305 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11305Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11305step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11305step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11306 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw11306Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11306step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw11306step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11306step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw11306step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11306step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11306step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11307 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11307Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11307step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw11307step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11307step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11307step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11308 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11308Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11308step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11308step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11308step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11308step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11309 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11309Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11310 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw11310Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11310step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw11310step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11311 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw11311Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11311step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw11311step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11312 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11312Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11312step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11312step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11313 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw11313Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11313step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11313step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11314 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11314Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11315 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11315Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11315step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw11315step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11315step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11315step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11315step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11315step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11316 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11316Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11316step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw11316step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11316step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11316step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11316step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11316step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11317 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11317Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11317step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11317step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11317step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11317step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11318 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw11318Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11318step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw11318step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11318step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw11318step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw11318step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11318step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw11318step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11318step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11319 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11319Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11319step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw11319step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11319step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw11319step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11319step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw11319step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11320 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -2, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11320Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11320step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw11320step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11320step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11320step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11320step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11320step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11321 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11321Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11321step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw11321step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11321step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11321step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11321step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11321step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11322Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11322step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11322step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11322step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11322step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11323 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw11323Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11323step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw11323step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11323step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw11323step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw11323step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11323step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw11323step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11323step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11324 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11324Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11324step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw11324step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11324step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw11324step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw11324step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11324step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw11324step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11324step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11325 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11325Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11325step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw11325step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11325step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11325step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11325step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11325step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11326 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11326Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11326step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw11326step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11326step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11326step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11326step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11326step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11327 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11327Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11327step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11327step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11327step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11327step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11328 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw11328Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11328step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw11328step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11328step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw11328step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw11328step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11328step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw11328step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11328step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11329 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11329Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11329step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw11329step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11329step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw11329step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw11329step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11329step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw11329step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11329step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11330 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11330Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11330step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11330step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11330step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11330step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11331 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11331Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11331step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11331step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11331step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11331step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11332 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11332Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11332step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11332step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11332step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11332step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11333 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw11333Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11333step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11333step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw11333step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11333step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw11333step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11333step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11334 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11334Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11334step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11334step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11334step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11334step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11335 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw11335Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11335step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw11335step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11335step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw11335step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11335step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw11335step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11336 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw11336Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11336step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw11336step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11336step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw11336step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11336step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw11336step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11337 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw11337Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11337step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw11337step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11337step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw11337step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11337step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw11337step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11338 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw11338Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11338step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw11338step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11338step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw11338step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11339 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw11339Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11339step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw11339step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11339step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11339step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11339step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11339step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11340 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw11340Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11340step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw11340step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11340step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw11340step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11340step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw11340step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11341 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw11341Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11341step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw11341step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11341step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw11341step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11341step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw11341step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11342 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw11342Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11342step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw11342step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11342step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw11342step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11342step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw11342step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11343 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw11343Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11343step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw11343step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11343step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw11343step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11344 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw11344Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11344step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw11344step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11344step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw11344step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw11344step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw11344step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw11344step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw11344step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11345 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11345Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11345step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw11345step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11345step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11345step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11346 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11346Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11346step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw11346step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11346step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11346step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11347 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11347Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11347step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11347step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11348 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw11348Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11348step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw11348step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11348step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw11348step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11349 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11349Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11349step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw11349step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11349step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw11349step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11350 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -2, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11350Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11350step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw11350step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11350step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11350step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11351 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11351Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11351step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw11351step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11351step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11351step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11352 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]

end MUB6.Certificate.MixedSemantics

end OAI
end


