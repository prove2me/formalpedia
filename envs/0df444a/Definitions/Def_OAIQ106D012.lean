-- Prove2me | Definitions.Def_OAIQ106D012
-- name    : OAIQ106D012
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T12:02:47.100208+00:00
-- url     : https://prove2.me/theorems/14d114c6-77c5-4e8e-9c76-45396737bdf0
-- title:
--   Definitions bundle OAIQ106D012 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 5589 declarations of OpenAI's Lean: 5589 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSemantics.raw17572`, `OAI.MUB6.Certificate.MixedSemantics.raw17572step0`, `OAI.MUB6.Certificate.MixedSemantics.raw17572step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw17572step1`, `OAI.MUB6.Certificate.MixedSemantics.raw17572step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw17573`, `OAI.MUB6.Certificate.MixedSemantics.raw17573Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw17573step0`, `OAI.MUB6.Certificate.MixedSemantics.raw17573step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw17573step1`, `OAI.MUB6.Certificate.MixedSemantics.raw17573step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw17574`, `OAI.MUB6.Certificate.MixedSemantics.raw17574Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw17574step0`, `OAI.MUB6.Certificate.MixedSemantics.raw17574step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw17574step1`, `OAI.MUB6.Certificate.MixedSemantics.raw17574step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw17575`, `OAI.MUB6.Certificate.MixedSemantics.raw17575Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw17575step0`, `OAI.MUB6.Certificate.MixedSemantics.raw17575step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw17575step1`, `OAI.MUB6.Certificate.MixedSemantics.raw17575step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw17576`, `OAI.MUB6.Certificate.MixedSemantics.raw17576Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw17576step0`, `OAI.MUB6.Certificate.MixedSemantics.raw17576step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw17576step1`, `OAI.MUB6.Certificate.MixedSemantics.raw17576step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw17576step2`, `OAI.MUB6.Certificate.MixedSemantics.raw17576step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw17577`, `OAI.MUB6.Certificate.MixedSemantics.raw17577Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw17577step0`, `OAI.MUB6.Certificate.MixedSemantics.raw17577step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw17577step1`, `OAI.MUB6.Certificate.MixedSemantics.raw17577step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw17578`, `OAI.MUB6.Certificate.MixedSemantics.raw17578Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw17578step0` and 5549 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_MixedSemantics_Canonical0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical0.lean), [`MutuallyUnbiased_MixedSemantics_Canonical1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical1.lean), [`MutuallyUnbiased_MixedSemantics_Canonical13`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical13.lean), [`MutuallyUnbiased_MixedSemantics_Canonical137`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical137.lean), [`MutuallyUnbiased_MixedSemantics_Canonical138`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical138.lean), [`MutuallyUnbiased_MixedSemantics_Canonical139`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical139.lean), [`MutuallyUnbiased_MixedSemantics_Canonical14`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical14.lean), [`MutuallyUnbiased_MixedSemantics_Canonical140`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical140.lean), [`MutuallyUnbiased_MixedSemantics_Canonical141`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical141.lean), [`MutuallyUnbiased_MixedSemantics_Canonical142`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical142.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound1161`, `OAI.MUB6.Certificate.MixedSemantics.sound1475`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound103`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound111`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound113`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound115`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound119`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound123`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound128`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound19`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound28`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound30`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound34`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound35`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound36`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound46`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound49`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound57`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound58`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound6`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound68`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound7`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound8`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound81`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1780`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero925`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound109`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1108`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound113`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1130`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1158`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1165`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1169`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1179`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1191`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1293`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1300`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1309`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1312`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1317`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1318`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound14`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound145`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1465`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1471`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1477`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1483`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1493`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1505`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1508`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound151`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1516`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1584`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1593`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1650`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1655`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1657`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1668`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1672`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1673`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1679`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1686`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1687`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1702`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1708`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1716`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1723`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1738`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1739`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1740`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1743`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1782`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1788`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1795`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1797`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1811`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1839`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1844`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1848`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1853`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1858`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1864`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1865`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1871`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1872`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1873`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1877`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1880`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1916`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1944`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1960`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1963`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1965`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1968`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1970`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1971`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1976`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1980`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1983`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1984`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1988`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1989`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1990`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1993`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1994`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1995`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1998`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1999`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2002`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2003`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2005`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2006`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2018`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2019`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2021`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2022`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2023`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2033`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2036`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2048`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2051`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2052`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2056`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2059`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2060`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2062`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2075`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2077`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2086`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2087`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2099`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2102`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2105`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound267`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound339`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound357`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound365`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound369`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound444`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound452`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound483`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound499`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound512`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound520`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound533`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound542`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound545`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound546`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound551`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound553`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound564`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound566`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound580`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound584`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound587`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound588`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound589`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound599`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound620`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound632`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound660`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound686`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound708`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound719`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound735`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound746`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound749`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound787`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound795`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound799`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound865`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound908`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound918`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound920`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound921`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound922`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound923`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound924`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound926`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound927`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound928`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound93`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound930`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound931`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound932`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound933`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound934`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound935`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound936`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound938`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound939`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound940`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound941`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound942`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound943`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound944`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound952`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound956`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound963`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound967`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound969`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound97`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound983`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound986` and `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1914`.
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

def raw17Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw17step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -2, 0], ![3, 0, -3]]
def raw17step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw18 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw175Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw175step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw175step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw175step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw175step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw176 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![2, 0, -2], ![-1, 1, 0], ![-1, 3, -2]]
def raw176Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw176step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw176step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw176step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw176step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw177 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![2, 0, -2], ![-1, 1, 0], ![-1, 3, -2]]
def raw177Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw177step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-2, 2, 0], ![-2, -1, 3]]
def raw177step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw177step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw177step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw180 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![2, 0, -2], ![-1, 2, -1], ![-1, 2, -1]]
def raw180Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw180step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw180step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw180step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw180step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw181 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![2, 0, -2], ![-1, 2, -1], ![-1, 2, -1]]
def raw181Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw181step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw181step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw182 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw1757Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1757step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-3, 1, 2]]
def raw1757step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1757step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw1757step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1757step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw1757step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1758 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-2, 1, 1], ![1, 1, -2], ![0, 2, -2]]
def raw1758Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1758step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw1758step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1758step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw1758step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1759 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-2, 1, 1], ![1, 1, -2], ![0, 2, -2]]
def raw1759Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1759step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw1759step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1760 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-2, 1, 1], ![1, 1, -2], ![0, 2, -2]]
def raw1760Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1760step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw1760step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1760step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw1760step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1760step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw1760step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1761 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2]]
def raw1761Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1761step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw1761step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1761step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw1761step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1762 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2]]
def raw1762Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1762step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw1762step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1763 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2]]
def raw1763Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1763step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw1763step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1763step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1763step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1763step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1763step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1764 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, 2, -3]]
def raw1764Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1764step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw1764step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1764step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw1764step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1765 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, 2, -3]]
def raw1765Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1765step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw1765step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1766 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, 2, -3]]
def raw1766Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1766step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw1766step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1766step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw1766step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1766step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw1766step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1767 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![-1, 2, -1]]
def raw1767Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1767step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw1767step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1767step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw1767step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1768 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![-1, 2, -1]]
def raw1768Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1768step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw1768step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1769 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![-1, 2, -1]]
def raw1769Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1769step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw1769step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1769step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw1769step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1769step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw1769step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1770 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw1770Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1770step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw1770step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1770step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw1770step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1771 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw1771Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1771step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw1771step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1772 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw1772Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1772step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw1772step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1772step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw1772step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1772step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw1772step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1773 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 1, -2], ![-2, 3, -1]]
def raw1773Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1773step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw1773step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1773step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw1773step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1774 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 1, -2], ![-2, 3, -1]]
def raw1774Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1774step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw1774step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1775 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 1, -2], ![-2, 3, -1]]
def raw1775Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1775step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, -2, 3], ![-2, 1, 1]]
def raw1775step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1775step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw1775step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1775step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw1775step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1776 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-2, 2, 0], ![1, 2, -3]]
def raw1776Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1776step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw1776step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1776step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw1776step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1777 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-2, 2, 0], ![1, 2, -3]]
def raw1777Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1777step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw1777step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1778 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-2, 2, 0], ![1, 2, -3]]
def raw1778Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1778step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-3, 1, 2]]
def raw1778step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1778step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw1778step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1778step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw1778step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1779 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw1779Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1779step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1779step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1779step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1779step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1780 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw1780Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1780step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1780step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1781 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw1781Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1781step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw1781step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1781step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1781step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1781step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1781step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1782 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2]]
def raw1782Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1782step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw1782step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1782step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw1782step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1783 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2]]
def raw1783Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1783step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw1783step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1784 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2]]
def raw1784Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1784step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw1784step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1784step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw1784step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1784step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw1784step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1785 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-2, 1, 1], ![0, 3, -3]]
def raw1785Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1785step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![3, 0, -3]]
def raw1785step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1785step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![3, 0, -3]]
def raw1785step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1786 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-2, 1, 1], ![0, 3, -3]]
def raw1786Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1786step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![3, 0, -3]]
def raw1786step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1787 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-2, 1, 1], ![0, 3, -3]]
def raw1787Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1787step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![3, 0, -3]]
def raw1787step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1787step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![3, 0, -3]]
def raw1787step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1788 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]
def raw1788Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1788step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw1788step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1788step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw1788step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1789 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]
def raw1789Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1789step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw1789step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1790 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]
def raw1790Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1790step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw1790step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1790step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw1790step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1790step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw1790step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1791 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw1791Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1791step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw1791step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1791step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw1791step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical137
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw17572 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]

def raw17572step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw17572step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17572step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw17572step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17573 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw17573Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17573step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17573step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17573step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17573step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17574 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw17574Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17574step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw17574step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17574step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw17574step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17575 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw17575Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17575step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17575step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17575step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17575step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17576 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw17576Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17576step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw17576step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17576step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw17576step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17576step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw17576step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17577 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw17577Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17577step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw17577step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17577step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw17577step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17578 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw17578Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17578step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17578step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17578step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17578step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17579 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw17579Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17579step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw17579step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17579step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw17579step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17580 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![0, 0, 0], ![3, -1, -2]]
def raw17580Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17580step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![3, -1, -2]]
def raw17580step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17580step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17580step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17580step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17580step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17581 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17581Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17581step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17581step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17581step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17581step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17582 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17582Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17582step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw17582step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17582step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17582step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17582step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17582step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17583 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17583Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17583step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17583step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17583step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17583step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17584 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw17584Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17584step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17584step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17584step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17584step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17585 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw17585Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17585step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw17585step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17586 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17586Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17586step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17586step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17586step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17586step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17586step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17586step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17586step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17586step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17587 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17587Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17587step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17587step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17587step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17587step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17587step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17587step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17587step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17587step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17588 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw17588Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17588step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw17588step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17588step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17588step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17588step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17588step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17589 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17589Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17589step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw17589step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17589step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw17589step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17590 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17590Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17590step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw17590step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17590step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw17590step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17591 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17591Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17591step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17591step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17591step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17591step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17592 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw17592Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17592step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17592step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17592step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17592step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17593 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw17593Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17593step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17593step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17593step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17593step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17594 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17594Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17594step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17594step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17594step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17594step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17595 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17595Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17595step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17595step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17595step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17595step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17595step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17595step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17596 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw17596Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17596step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17596step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17596step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17596step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17596step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17596step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17597 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw17597Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17597step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17597step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17597step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17597step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17598 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw17598Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17598step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17598step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17598step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17598step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17599 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw17599Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17599step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17599step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17599step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17599step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17599step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17599step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17600 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -2, 0]]
def raw17600Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17600step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17600step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17600step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17600step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17600step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17600step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17601 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw17601Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17601step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17601step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17601step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17601step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17602 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw17602Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17602step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw17602step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17602step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw17602step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17602step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw17602step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17603 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw17603Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17603step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw17603step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17603step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17603step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17603step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17603step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17604 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw17604Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17604step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17604step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17604step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17604step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17604step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17604step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17605 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw17605Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17605step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17605step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17605step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17605step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17605step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17605step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17606 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw17606Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17606step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17606step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17606step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17606step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17607 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17607Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17607step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17607step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17608 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17608Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17608step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw17608step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17608step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17608step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17609 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17609Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17609step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17609step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17609step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17609step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17610 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw17610Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17610step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw17610step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17610step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw17610step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17611 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw17611Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17611step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw17611step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17612 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17612Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17612step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17612step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17612step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17612step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17612step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17612step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17613 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17613Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17613step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17613step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17613step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17613step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17613step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17613step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17614 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw17614Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17614step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw17614step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17614step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw17614step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17614step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw17614step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17615 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17615Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17615step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw17615step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17616 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17616Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17616step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw17616step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17617 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17617Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17617step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17617step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17617step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17617step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17618 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw17618Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17618step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17618step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17618step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17618step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17619 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw17619Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17619step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17619step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17620 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17620Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17620step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17620step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17621 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17621Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17621step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17621step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17621step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17621step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17622 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw17622Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17622step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17622step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17622step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17622step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17623 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw17623Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17623step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17623step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17624 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw17624Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17624step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17624step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17625 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw17625Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17625step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17625step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17625step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17625step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17626 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -2, 0]]
def raw17626Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17626step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17626step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17626step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17626step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17627 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw17627Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17627step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17627step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17628 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw17628Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17628step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw17628step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17628step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw17628step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17629 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw17629Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17629step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw17629step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17629step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17629step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17630 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw17630Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17630step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17630step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17630step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17630step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17631 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw17631Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17631step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17631step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17631step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17631step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17632 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw17632Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17632step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17632step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17632step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17632step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17633 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17633Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17633step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw17633step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17633step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17633step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17633step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17633step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17634 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17634Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17634step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17634step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17634step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw17634step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17634step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17634step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17634step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17634step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17635 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17635Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17635step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw17635step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17635step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw17635step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17636 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17636Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17636step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17636step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17636step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17636step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17637 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17637Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17637step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17637step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17637step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17637step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17637step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17637step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17637step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17638 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17638Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17638step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17638step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17638step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17638step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17639 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17639Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17639step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw17639step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17639step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw17639step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17640 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17640Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17640step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17640step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17640step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17640step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17641 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17641Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17641step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17641step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17641step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17641step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17642 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17642Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17642step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17642step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17642step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17642step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17642step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17642step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17643 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17643Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17643step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17643step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17643step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17643step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17644 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw17644Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17644step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw17644step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17644step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw17644step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17645 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw17645Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17645step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17645step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17645step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17645step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17646 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw17646Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17646step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw17646step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17646step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17646step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17646step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17646step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17647 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-2, 2, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw17647Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17647step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17647step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17647step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17647step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17648 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17648Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17648step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw17648step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17648step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17648step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17649 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17649Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17649step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17649step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17649step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw17649step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17649step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17649step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17650 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17650Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17650step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw17650step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17651 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17651Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17651step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17651step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17652 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17652Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17652step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17652step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17652step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17652step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17652step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17652step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17653 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17653Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17653step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw17653step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17653step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17653step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17654 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17654Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17654step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw17654step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17655 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17655Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17655step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17655step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17655step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17655step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17656 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17656Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17656step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw17656step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17656step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw17656step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17657 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17657Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17657step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17657step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17657step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17657step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17657step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17657step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17658 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17658Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17658step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17658step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17659 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw17659Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17659step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw17659step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17659step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw17659step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17660 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw17660Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17660step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17660step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17660step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17660step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17661 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw17661Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17661step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw17661step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17661step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17661step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17661step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17661step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17662 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-2, 2, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw17662Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17662step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw17662step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17662step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw17662step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17663 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17663Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17663step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17663step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17663step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17663step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17663step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17663step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical138
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw17664 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17664Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17664step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17664step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw17664step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17664step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17664step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17665 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17665Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17665step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17665step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17665step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw17665step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17665step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17665step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17666 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17666Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17666step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17666step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17666step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17666step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17666step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]
def raw17666step2Labels : Fin 2 → Fin 3 := ![0, 2]

def raw17666step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]
def raw17666step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw17667 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17667Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17667step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17667step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17667step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17667step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17667step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17667step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17668 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17668Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17668step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17668step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17669 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17669Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17669step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17669step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17670 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17670Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17670step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17670step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17671 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17671Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17671step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17671step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17671step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17671step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17671step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17671step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17672 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17672Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17672step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17672step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17673 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17673Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17674 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17674Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17674step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17674step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17675 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw17675Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17675step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw17675step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17675step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw17675step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17675step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw17675step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17675step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw17675step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17676 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw17676Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17676step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw17676step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17676step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw17676step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17677 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw17677Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw17677step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17677step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17677step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17677step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17677step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17678 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw17678Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17678step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw17678step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17678step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17678step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17678step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17678step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17679 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw17679Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17679step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw17679step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17679step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1]]
def raw17679step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17679step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17679step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17680 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw17680Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17680step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw17680step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17680step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw17680step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17680step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw17680step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17680step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw17680step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17680step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw17680step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17681 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw17681Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17681step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw17681step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17681step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17681step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17681step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17681step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17681step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17681step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17682 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw17682Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17682step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw17682step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17682step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17682step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17682step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17682step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17682step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17682step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17683 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17683Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17683step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17683step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17683step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17683step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17683step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17683step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17683step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17683step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17684 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17684Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17684step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17684step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17684step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw17684step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17684step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17684step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17685 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17685Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17685step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17685step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17685step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw17685step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17685step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17685step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17686 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw17686Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17686step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw17686step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17686step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![2, 0, -2]]
def raw17686step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17686step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![2, 0, -2]]
def raw17686step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17686step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]
def raw17686step3Labels : Fin 2 → Fin 3 := ![0, 2]

def raw17686step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![2, -2], ![-1, 1], ![-1, 1]]
def raw17686step4Labels : Fin 2 → Fin 3 := ![0, 2]

def raw17686step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def raw17686step5Labels : Fin 2 → Fin 3 := ![0, 2]

def raw17686step6 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def raw17686step6Labels : Fin 2 → Fin 2 := ![0, 1]

def raw17687 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17687Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17687step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17687step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17687step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17687step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17687step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17687step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17688 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17688Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17688step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17688step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17688step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw17688step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17688step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw17688step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17689 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17689Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17689step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17689step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17689step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17689step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17690 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw17690Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17690step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw17690step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17690step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17690step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17690step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17690step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17690step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17690step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17691 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17691Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17691step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17691step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17691step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw17691step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17691step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw17691step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17692 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17692Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17692step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17692step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17692step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17692step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17693 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw17693Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17693step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17693step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17693step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17693step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17693step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17693step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17693step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17693step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17694 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw17694Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17694step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw17694step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17694step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw17694step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17694step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw17694step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17694step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw17694step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17695 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw17695Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17695step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw17695step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17695step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw17695step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17695step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw17695step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17695step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![2, -1, -1]]
def raw17695step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17696 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw17696Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17696step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw17696step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17696step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17696step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17696step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17696step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17697 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw17697Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw17697step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17697step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17697step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17697step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17697step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17698 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw17698Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17698step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw17698step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17698step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw17698step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17698step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw17698step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17698step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw17698step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17699 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw17699Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17699step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw17699step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17699step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw17699step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17699step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw17699step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17699step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw17699step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17700 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw17700Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17700step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw17700step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17700step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17700step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17700step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17700step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17701 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw17701Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17701step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw17701step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17701step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17701step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17701step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17701step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17702 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw17702Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17702step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw17702step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17702step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![3, -1, -2]]
def raw17702step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17702step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![3, -1, -2]]
def raw17702step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17702step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 0, 1], ![-2, 1, 1]]
def raw17702step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17702step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw17702step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17703 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17703Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17703step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17703step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17703step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17703step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17703step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17703step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17704 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17704Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17704step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw17704step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17704step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17704step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17705 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17705Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17705step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17705step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17705step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw17705step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17705step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw17705step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17706 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw17706Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17706step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw17706step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17706step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17706step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17706step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17706step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17707 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw17707Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17707step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw17707step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17707step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17707step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17707step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17707step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17708 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17708Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17708step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17708step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17708step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17708step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17708step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17708step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17709 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17709Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17709step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17709step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17709step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17709step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17710 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17710Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17710step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17710step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17710step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17710step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17710step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17710step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17711 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw17711Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17711step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw17711step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17711step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw17711step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17711step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17711step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17711step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17711step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17712 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw17712Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17712step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw17712step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17712step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17712step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17712step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17712step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17713 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17713Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17713step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17713step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17713step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17713step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17714 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17714Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17714step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17714step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17715 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17715Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17715step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17715step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17715step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17715step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17716 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw17716Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17716step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw17716step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17716step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw17716step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17716step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw17716step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17717 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw17717Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17717step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17717step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17718 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17718Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17718step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17718step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17718step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17718step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17718step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17718step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17719 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17719Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17719step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17719step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17720 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17720Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17720step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17720step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17720step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17720step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17721 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw17721Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17721step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw17721step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17721step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw17721step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17721step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17721step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17721step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17721step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17722 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw17722Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17722step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw17722step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17722step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17722step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw17723Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17723step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw17723step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17723step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17723step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17723step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17723step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17724 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw17724Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw17724step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17724step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw17724step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17724step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw17724step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17725 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw17725Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17725step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17725step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17725step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17725step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17726 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw17726Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17726step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw17726step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17726step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17726step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17726step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17726step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17727 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw17727Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17727step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw17727step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17727step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17727step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17727step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17727step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17728 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw17728Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17728step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw17728step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17728step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw17728step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17728step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw17728step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17729 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw17729Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw17729step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17729step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-2, 1, 1], ![-2, 1, 1]]
def raw17729step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17729step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw17729step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17729step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw17729step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17730 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw17730Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17730step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17730step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17730step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17730step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17730step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17730step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17731 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw17731Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17731step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw17731step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17731step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw17731step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17731step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw17731step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17731step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw17731step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17732 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw17732Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17732step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw17732step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17732step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw17732step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17732step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17732step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17732step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17732step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17733 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17733Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17733step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17733step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17733step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17733step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17733step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17733step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17734 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17734Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17734step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17734step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17734step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17734step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17735 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17735Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17735step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17735step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17735step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw17735step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17735step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw17735step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw17736Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17736step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw17736step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17736step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17736step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17736step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17736step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17737 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw17737Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17737step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw17737step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17737step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17737step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17737step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17737step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17738 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17738Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17738step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17738step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17738step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw17738step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17738step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17738step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17738step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17738step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17739 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17739Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17739step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17739step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17739step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17739step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17740 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17740Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17740step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17740step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17740step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17740step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17740step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17740step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw17741Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17741step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw17741step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17741step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw17741step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17741step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17741step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17741step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17741step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17742 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw17742Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17742step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw17742step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17742step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17742step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17742step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17742step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17743Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17743step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17743step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17743step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17743step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17743step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17743step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17744 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17744Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17744step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw17744step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17744step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw17744step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17745Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17745step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw17745step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17745step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw17745step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw17746Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17746step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17746step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17746step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17746step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17746step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17746step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17747 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw17747Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17747step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17747step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17747step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17747step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17748 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17748Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17748step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17748step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17748step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17748step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17748step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17748step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17748step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17748step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17749 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17749Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17749step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17749step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17749step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw17749step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17749step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw17749step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17750 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17750Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17750step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17750step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17750step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17750step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw17751Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17751step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw17751step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17751step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17751step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17751step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17751step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17752 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw17752Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17752step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw17752step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17752step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17752step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17752step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17752step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17753 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw17753Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17753step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw17753step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17753step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, -1, 2]]
def raw17753step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17753step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]
def raw17753step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17753step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]
def raw17753step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17754 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw17754Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17754step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw17754step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17754step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw17754step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17754step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw17754step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw17755Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17755step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17755step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17755step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17755step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw17756Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17756step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw17756step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17756step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw17756step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17756step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw17756step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw17757Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17757step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw17757step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17757step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17757step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17757step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17757step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17758 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw17758Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17758step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw17758step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17758step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw17758step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17758step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw17758step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17759 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw17759Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17759step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw17759step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17759step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw17759step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17759step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw17759step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw17760Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17760step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17760step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17760step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17760step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw17761Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17761step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw17761step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17761step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw17761step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17761step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw17761step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw17762Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw17762step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17762step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17762step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17762step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17762step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17763Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17763step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17763step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17763step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17763step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17763step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17763step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17764 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17764Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17764step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw17764step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17764step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17764step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17764step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17764step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17765Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17765step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17765step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17765step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17765step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17765step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17765step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17766 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw17766Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17766step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw17766step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17766step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw17766step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17766step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw17766step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17767 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw17767Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17767step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw17767step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17767step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw17767step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17767step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw17767step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17768 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17768Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17768step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17768step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17768step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17768step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17768step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17768step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17768step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17768step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17769 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17769Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17769step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17769step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17769step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17769step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17770 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17770Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17770step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17770step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17770step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17770step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17771 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw17771Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17771step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17771step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17771step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17771step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17772 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw17772Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17772step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17772step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17772step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17772step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17773 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17773Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17773step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17773step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17773step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17773step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17773step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17773step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17774 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17774Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17774step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17774step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17774step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17774step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17774step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17774step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17775 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, -1, -1]]
def raw17775Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17775step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![0, -1, 1], ![2, -1, -1]]
def raw17775step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17775step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17775step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17775step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17775step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17776 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw17776Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17776step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw17776step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17776step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17776step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17776step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17776step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17777 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw17777Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17777step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw17777step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17777step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw17777step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17777step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw17777step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw17778Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17778step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw17778step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17778step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw17778step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17779 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![-1, 2, -1], ![2, -3, 1], ![2, -1, -1]]
def raw17779Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17779step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 2, -1], ![2, -3, 1], ![2, -1, -1]]
def raw17779step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17779step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17779step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17779step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17779step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17780 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![1, 0, -1]]
def raw17780Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17780step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![1, 0, -1]]
def raw17780step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17780step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17780step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17780step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17780step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17781 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw17781Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17781step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw17781step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17781step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw17781step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17781step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17781step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17781step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17781step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17782 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw17782Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17782step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17782step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17782step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17782step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17782step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17782step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17783 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![3, -2, -1]]
def raw17783Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17783step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![3, -2, -1]]
def raw17783step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17783step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17783step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17783step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17783step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17783step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17783step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![3, -2, -1]]
def raw17784Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17784step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![3, -2, -1]]
def raw17784step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17784step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17784step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17784step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17784step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17784step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17784step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17785 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17785Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17785step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17785step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17785step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17785step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17786Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17786step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw17786step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17786step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17786step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17787Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17787step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17787step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17787step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17787step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17787step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17787step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17788 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw17788Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17788step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw17788step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17788step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw17788step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17788step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw17788step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17789 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw17789Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17789step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw17789step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17789step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw17789step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17789step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw17789step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17790 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17790Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17790step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17790step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17790step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17790step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17790step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17790step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17791Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17791step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17791step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical139
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw17792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17792Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17792step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17792step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw17793Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17793step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17793step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17794 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw17794Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17794step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17794step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17795 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17795Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17795step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17795step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17795step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17795step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17796 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17796Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17796step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17796step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17796step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17796step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17797 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, -1, -1]]
def raw17797Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17797step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![0, -1, 1], ![2, -1, -1]]
def raw17797step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17797step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17797step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17798 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw17798Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17798step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw17798step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17798step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17798step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17799 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw17799Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17799step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw17799step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17799step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw17799step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17799step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17799step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17800 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw17800Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17800step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17800step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17800step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17800step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17801 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![-1, 2, -1], ![2, -3, 1], ![2, -1, -1]]
def raw17801Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17801step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 2, -1], ![2, -3, 1], ![2, -1, -1]]
def raw17801step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17801step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17801step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17801step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17801step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17802 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![1, 0, -1]]
def raw17802Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17802step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![1, 0, -1]]
def raw17802step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17802step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17802step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17802step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17802step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw17803Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17803step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw17803step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17803step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw17803step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17803step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17803step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17804 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw17804Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17804step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17804step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17804step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17804step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17805 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![3, -2, -1]]
def raw17805Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17805step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![3, -2, -1]]
def raw17805step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17805step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17805step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17805step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17805step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17806 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![3, -2, -1]]
def raw17806Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17806step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![3, -2, -1]]
def raw17806step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17806step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17806step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17806step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17806step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17807 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17807Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17807step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17807step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17807step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17807step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17807step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17807step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17808 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17808Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17808step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17808step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17808step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17808step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17809 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17809Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17809step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-2, 2, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17809step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17809step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw17809step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17809step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw17809step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17809step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw17809step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17810 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw17810Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17810step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw17810step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17810step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17810step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17811 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17811Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17811step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17811step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17811step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17811step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17811step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17811step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17812 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17812Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17812step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-2, 2, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17812step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17812step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw17812step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17812step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17812step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17812step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17812step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17813 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17813Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17813step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17813step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17813step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -2, 1], ![-1, -1, 2]]
def raw17813step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17813step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw17813step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17813step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw17813step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17814 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17814Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17814step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17814step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17814step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17814step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17814step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17814step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17814step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17814step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17815 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw17815Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17815step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw17815step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17815step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17815step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17815step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17815step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17816 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw17816Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17816step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw17816step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17816step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17816step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17816step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17816step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17817 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw17817Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17817step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17817step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17817step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17817step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17818 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![-2, 2, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw17818Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17818step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-2, 2, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw17818step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17818step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17818step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17818step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17818step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17819 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw17819Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17819step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw17819step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17819step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw17819step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17819step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw17819step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17820 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -2, 2]]
def raw17820Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17820step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![0, -2, 2]]
def raw17820step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17820step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw17820step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17820step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw17820step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17821 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -2, 2]]
def raw17821Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17821step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![-1, 1, 0], ![1, -2, 1], ![0, -2, 2]]
def raw17821step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17821step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17821step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17821step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17821step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17822 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -2, 2]]
def raw17822Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17822step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17822step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17822step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17822step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17823 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![0, -2, 2]]
def raw17823Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17823step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-2, 2, 0], ![1, -2, 1], ![0, -2, 2]]
def raw17823step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17823step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17823step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17823step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17823step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17824 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17824Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17824step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17824step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17824step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw17824step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17824step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17824step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17825 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17825Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17825step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw17825step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17825step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17825step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17826 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17826Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17826step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-2, 2, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17826step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17826step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw17826step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17827 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw17827Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17827step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw17827step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17827step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw17827step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17827step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17827step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17828 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17828Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17828step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17828step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17828step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17828step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17829 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17829Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17829step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17829step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17829step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17829step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17830 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17830Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17830step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-2, 2, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17830step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17830step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17830step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17831 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw17831Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17831step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw17831step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17831step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw17831step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17832 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17832Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17832step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17832step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17832step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -2, 1], ![-1, -1, 2]]
def raw17832step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17832step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17832step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17833 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17833Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17833step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17833step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17833step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -2, 1], ![-1, -1, 2]]
def raw17833step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17833step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw17833step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17834 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17834Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17834step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17834step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17834step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17834step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17834step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17834step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17835 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw17835Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17835step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw17835step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17835step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -2, 1], ![-2, 0, 2]]
def raw17835step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17835step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw17835step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17836 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw17836Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17836step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw17836step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17836step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1]]
def raw17836step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17836step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw17836step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17837 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw17837Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17837step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw17837step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17837step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw17837step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17837step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17837step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17838 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw17838Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17838step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw17838step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17838step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17838step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17839 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![-2, 2, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw17839Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17839step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-2, 2, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw17839step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17839step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw17839step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17839step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17839step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17840 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw17840Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17840step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw17840step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17840step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw17840step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17840step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17840step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17841 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -2, 2]]
def raw17841Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17841step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![0, -2, 2]]
def raw17841step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17841step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw17841step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17841step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw17841step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17842 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -2, 2]]
def raw17842Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17842step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![-1, 1, 0], ![1, -2, 1], ![0, -2, 2]]
def raw17842step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17842step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17842step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17842step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17842step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17843 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -2, 2]]
def raw17843Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17843step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17843step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17843step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17843step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17844 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![0, -2, 2]]
def raw17844Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17844step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-2, 2, 0], ![1, -2, 1], ![0, -2, 2]]
def raw17844step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17844step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw17844step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17844step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw17844step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17845 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17845Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17845step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17845step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17845step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17845step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17845step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17845step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17846 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17846Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17846step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw17846step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17846step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17846step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17847Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17847step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17847step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17847step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2]]
def raw17847step1Labels : Fin 2 → Fin 3 := ![0, 2]

def raw17847step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw17847step2Labels : Fin 2 → Fin 3 := ![0, 2]

def raw17847step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw17847step3Labels : Fin 2 → Fin 3 := ![0, 2]

def raw17847step4 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw17847step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw17848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw17848Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17848step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw17848step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17848step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17848step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17848step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17848step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17849Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17849step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17849step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17849step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17849step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17849step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17849step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17850Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17850step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17850step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17850step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw17850step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17850step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw17850step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17851Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17851step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17851step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17851step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17851step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17852Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17852step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17852step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17852step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17852step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17852step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17852step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw17853Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17853step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw17853step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17853step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17853step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17853step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17853step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17854Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17854step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17854step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17854step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17854step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17854step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17854step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17855Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17855step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17855step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17855step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17855step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17856Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17856step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw17856step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17856step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw17856step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17857Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17857step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17857step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17857step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17857step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17858 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw17858Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17858step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17858step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17858step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17858step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17859Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17859step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17859step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17860Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17860step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17860step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17860step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17860step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17860step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17860step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17861Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17861step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17861step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17861step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw17861step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17861step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw17861step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17862Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17862step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17862step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17862step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17862step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![2, 0, -2]]
def raw17863Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17863step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![0, 1, -1], ![2, 0, -2]]
def raw17863step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17863step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17863step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17863step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17863step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17864Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17864step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17864step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw17865Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17865step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw17865step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17865step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17865step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17865step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17865step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw17866Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17866step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw17866step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17866step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw17866step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17866step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw17866step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw17867Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17867step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17867step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17867step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17867step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw17868Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17868step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw17868step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17868step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17868step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17868step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17868step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 1, -2]]
def raw17869Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17869step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![1, 1, -2]]
def raw17869step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17869step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17869step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17869step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17869step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw17870Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17870step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw17870step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17870step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw17870step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17870step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw17870step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw17871Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17871step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw17871step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17871step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw17871step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17871step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw17871step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw17872Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17872step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17872step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17872step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17872step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw17873Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17873step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw17873step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17873step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17873step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17873step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17873step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw17874Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17874step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw17874step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17874step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17874step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17874step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17874step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17875 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17875Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17875step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17875step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17875step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw17875step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17875step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17875step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17875step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17875step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17876 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17876Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17876step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw17876step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17876step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17876step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17876step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17876step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17877 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17877Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17877step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-2, 2, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17877step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17877step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw17877step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17877step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw17877step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17878 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17878Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17878step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17878step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17878step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17878step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17878step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17878step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17879 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17879Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17879step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17879step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17879step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17879step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17879step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17879step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17880 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17880Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17880step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-2, 2, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17880step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17880step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17880step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17880step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17880step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17881 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17881Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17881step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17881step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17881step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2]]
def raw17881step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17881step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-2, 2]]
def raw17881step2Labels : Fin 2 → Fin 3 := ![1, 2]

def raw17881step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw17881step3Labels : Fin 2 → Fin 3 := ![1, 2]

def raw17881step4 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw17881step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw17882 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17882Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17882step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17882step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17882step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![0, -1, 1], ![0, -2, 2]]
def raw17882step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17882step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17882step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17882step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17882step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17883 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17883Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17883step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17883step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17883step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17883step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17883step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17883step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17883step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17883step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17884 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -3, 2]]
def raw17884Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17884step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -3, 2]]
def raw17884step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17884step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw17884step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17884step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw17884step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17885 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -3, 2]]
def raw17885Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17885step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -3, 2]]
def raw17885step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17885step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17885step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17885step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17885step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17886 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -3, 2]]
def raw17886Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17886step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17886step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17886step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17886step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17887 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![1, -3, 2]]
def raw17887Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17887step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-2, 2, 0], ![0, -1, 1], ![1, -3, 2]]
def raw17887step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17887step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17887step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17887step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17887step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17888 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17888Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17888step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17888step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17888step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17888step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17889Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17889step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17889step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17889step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw17889step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17889step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17889step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17890 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17890Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17890step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17890step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17890step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17890step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17891 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw17891Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17891step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw17891step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17891step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![2, 0, -2]]
def raw17891step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17891step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17891step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17891step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17891step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17892 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17892Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17892step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw17892step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17892step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17892step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17892step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17892step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17893 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17893Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17893step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17893step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17893step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw17893step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17893step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw17893step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17894 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17894Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17894step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17894step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17894step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw17894step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17894step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw17894step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17895 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17895Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17895step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17895step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17895step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17895step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17896 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw17896Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17896step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw17896step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17896step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw17896step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17896step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17896step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17896step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17896step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17897 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17897Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17897step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw17897step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17897step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17897step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17897step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17897step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17898 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17898Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17898step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17898step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17898step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17898step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17898step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17898step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17899 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17899Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17899step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17899step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17899step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw17899step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17900 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17900Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17900step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw17900step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17900step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17900step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17901 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw17901Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17901step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw17901step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17901step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw17901step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17901step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17901step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17901step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17901step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17902 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17902Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17902step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw17902step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17902step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17902step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17902step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17902step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17902step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17902step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17903 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17903Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17903step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17903step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17903step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17903step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17904 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17904Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17904step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17904step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17905 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17905Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17905step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17905step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17905step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17905step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17906 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw17906Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17906step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17906step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17906step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17906step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17906step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17906step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17907 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17907Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17907step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17907step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17907step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17907step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17907step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17907step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17908 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw17908Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17908step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw17908step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17908step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw17908step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17908step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw17908step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw17909Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17909step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw17909step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17909step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw17909step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw17910Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17910step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw17910step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17910step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17910step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17910step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17910step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17911 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw17911Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17911step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw17911step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17911step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17911step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17912 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw17912Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17912step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![1, 1, -2]]
def raw17912step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17912step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw17912step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17912step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17912step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17912step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17912step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17913 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw17913Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17913step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw17913step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17913step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw17913step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17913step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw17913step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17914 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw17914Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17914step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw17914step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17914step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw17914step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17914step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw17914step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17915 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw17915Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17915step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw17915step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17915step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17915step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17915step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17915step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17916 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw17916Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17916step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw17916step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17916step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17916step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17917 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw17917Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17917step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2]]
def raw17917step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17917step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![3, -1, -2]]
def raw17917step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17917step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17917step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17917step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17917step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17918 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17918Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17918step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17918step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17918step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw17918step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17918step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17918step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17918step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17918step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17919 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17919Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17919step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17919step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17919step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17919step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17919step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17919step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw1792 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw1792Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1792step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw1792step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1793 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw1793Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1793step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw1793step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1793step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw1793step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1793step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw1793step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1794 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw1794Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1794step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw1794step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1794step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw1794step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1795 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw1795Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1795step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw1795step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1796 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw1796Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1796step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw1796step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1796step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw1796step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1796step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw1796step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1797 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw1797Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1797step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw1797step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1797step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw1797step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1798 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw1798Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1798step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw1798step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1799 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw1799Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1799step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 2, -1], ![-2, -1, 3]]
def raw1799step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1799step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw1799step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1799step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw1799step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1800 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1800Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1800step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1800step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1800step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1800step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1801 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1801Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1801step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1801step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1802 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1802Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1802step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw1802step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1802step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw1802step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1802step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw1802step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1803 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1803Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1803step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1803step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1803step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1803step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1804 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1804Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1804step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1804step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1805 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1805Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1805step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 2, -1], ![-1, 0, 1], ![-1, -2, 3]]
def raw1805step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1805step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw1805step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1805step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw1805step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1806 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1806Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1806step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1806step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1806step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1806step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1807 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1807Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1807step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1807step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1808 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1808Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1808step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw1808step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1808step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw1808step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1808step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw1808step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1809 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1809Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1809step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1809step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1809step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1809step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1810 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1810Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1810step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1810step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1811 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1811Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1811step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw1811step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1811step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw1811step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1811step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw1811step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1812 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1]]
def raw1812Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1812step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw1812step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1812step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw1812step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1813 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1]]
def raw1813Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1813step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw1813step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1814 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1]]
def raw1814Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1814step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw1814step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1814step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw1814step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1814step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw1814step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1815 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw1815Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1815step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw1815step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1815step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw1815step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1816 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw1816Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1816step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw1816step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1817 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw1817Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1817step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw1817step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1817step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw1817step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1817step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw1817step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1818 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1818Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1818step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1818step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1818step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1818step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1819 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1819Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1819step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1819step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1820 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1820Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1820step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw1820step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1820step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw1820step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1820step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw1820step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1821 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![-2, 3, -1]]
def raw1821Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1821step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw1821step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1821step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw1821step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1822 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![-2, 3, -1]]
def raw1822Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1822step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw1822step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1823Labels : Fin 3 → Fin 2 := ![1, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical140
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw17920 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17920Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17920step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17920step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17920step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17920step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17921 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw17921Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17921step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw17921step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17921step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![2, 0, -2]]
def raw17921step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17921step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17921step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17921step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17921step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17922 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17922Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17922step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw17922step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17922step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17922step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17922step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17922step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17922step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17922step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17923 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17923Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17923step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17923step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17923step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw17923step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17923step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw17923step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17923step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw17923step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17924 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17924Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17924step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17924step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17924step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw17924step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17924step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw17924step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17925 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17925Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17925step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17925step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17925step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17925step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17926 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw17926Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17926step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw17926step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17926step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw17926step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17926step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17926step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17926step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17926step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17927 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17927Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17927step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw17927step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17927step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw17927step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17927step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw17927step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17928Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17928step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17928step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17928step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1]]
def raw17928step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17928step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw17928step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17928step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw17928step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17929Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17929step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17929step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17929step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw17929step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17929step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw17929step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17929step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw17929step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17930Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17930step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17930step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17930step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17930step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw17931Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17931step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw17931step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17931step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw17931step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17931step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17931step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17931step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17931step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17932Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17932step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw17932step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17932step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17932step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17932step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17932step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17932step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17932step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17933 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17933Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17933step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw17933step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17933step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17933step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17933step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17933step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17934 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17934Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17934step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw17934step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17934step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17934step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17934step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17934step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17935Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17935step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17935step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17935step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17935step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw17936Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17936step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17936step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17936step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17936step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17936step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17937Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17937step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17937step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17937step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17937step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17937step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17937step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw17938Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17938step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw17938step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17938step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw17938step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17938step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw17938step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17938step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw17938step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw17939Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17939step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw17939step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17939step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw17939step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17939step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw17939step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17939step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw17939step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw17940Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17940step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw17940step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17940step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw17940step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17940step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw17940step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw17941Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17941step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17941step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17941step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17941step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw17942Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17942step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![1, 1, -2]]
def raw17942step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17942step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17942step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17942step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17942step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw17943Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17943step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw17943step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17943step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw17943step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17943step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw17943step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw17944Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17944step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw17944step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17944step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw17944step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17944step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw17944step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw17945Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17945step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw17945step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17945step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17945step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17945step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17945step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw17946Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17946step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17946step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17946step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17946step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw17947Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17947step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2]]
def raw17947step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17947step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![3, -1, -2]]
def raw17947step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17947step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17947step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17947step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17947step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 3, -1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17948Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17948step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 3, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw17948step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17948step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw17948step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17948step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17948step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17948step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17948step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17949Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17949step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0]]
def raw17949step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17949step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw17949step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17949step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17949step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17949step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17949step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17950Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17950step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17950step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17950step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17950step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17951 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0]]
def raw17951Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17951step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0]]
def raw17951step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17951step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17951step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17951step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17951step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw17952Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17952step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]
def raw17952step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17952step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw17952step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17952step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw17952step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17952step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw17952step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17953Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17953step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw17953step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17953step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17953step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17953step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17953step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17954Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17954step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0]]
def raw17954step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17954step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17954step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17954step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17954step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17954step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17954step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17955Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17955step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17955step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17955step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17955step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17955step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17955step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0]]
def raw17956Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17956step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0]]
def raw17956step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17956step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17956step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17956step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17956step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw17957Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17957step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]
def raw17957step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17957step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw17957step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17958Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17958step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -2, 0]]
def raw17958step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17958step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw17958step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17958step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw17958step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 3, -1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17959Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17959step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 3, -1], ![1, -2, 1], ![1, 0, -1], ![2, -2, 0]]
def raw17959step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17959step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw17959step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17959step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17959step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17959step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17959step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -2, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17960Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17960step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17960step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17960step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17960step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0]]
def raw17961Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17961step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -2, 1], ![0, 1, -1], ![2, -2, 0]]
def raw17961step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17961step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17961step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17961step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17961step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw17962Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17962step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0]]
def raw17962step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17962step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17962step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17962step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17962step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17962step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17962step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17963Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17963step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw17963step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17963step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw17963step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 3, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17964Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17964step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17964step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17964step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw17964step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17964step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw17964step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17965Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17965step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw17965step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17965step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17965step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17965step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17965step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw17966Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17966step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17966step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17966step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17966step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw17967Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17967step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17967step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17967step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17967step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![2, -2, 0]]
def raw17968Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17968step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -2, 0]]
def raw17968step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17968step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17968step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17968step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17968step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17969 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 3, -1], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![2, -2, 0]]
def raw17969Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17969step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 3, -1], ![0, -1, 1], ![2, -1, -1], ![2, -2, 0]]
def raw17969step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17969step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw17969step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17969step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw17969step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17969step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw17969step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![2, -2, 0]]
def raw17970Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17970step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![-1, 0, 1], ![2, -1, -1], ![2, -2, 0]]
def raw17970step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17970step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw17970step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17970step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17970step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17970step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17970step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![-1, 1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw17971Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17971step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17971step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17971step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17971step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17971step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17971step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0]]
def raw17972Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17972step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0]]
def raw17972step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17972step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17972step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17972step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17972step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw17973Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17973step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -3, 0]]
def raw17973step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17973step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-3, 1, 2]]
def raw17973step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17973step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw17973step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17973step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw17973step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 3, -1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw17974Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17974step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 3, -1], ![0, -1, 1], ![1, 0, -1], ![3, -3, 0]]
def raw17974step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17974step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw17974step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17974step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw17974step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw17975Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17975step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![-1, 0, 1], ![1, 0, -1], ![3, -3, 0]]
def raw17975step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17975step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw17975step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17975step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17975step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17975step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17975step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw17976Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17976step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17976step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17976step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17976step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17976step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17976step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0]]
def raw17977Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17977step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![3, -3, 0]]
def raw17977step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17977step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17977step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17977step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17977step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17978Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17978step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17978step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17978step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![1, 1, -2], ![2, -1, -1]]
def raw17978step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17978step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17978step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17979Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17979step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17979step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17979step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17979step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17979step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17979step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17980Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17980step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17980step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17980step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17980step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17980step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17980step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw17981Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17981step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw17981step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17981step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![2, -1, -1]]
def raw17981step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17981step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17981step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17981step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17981step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1]]
def raw17982Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17982step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1]]
def raw17982step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17982step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![1, 1, -2], ![1, 0, -1]]
def raw17982step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17982step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17982step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17982step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17982step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17983Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17983step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17983step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17983step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw17983step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17983step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw17983step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17983step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw17983step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17984Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17984step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17984step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17984step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw17984step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17984step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17984step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17984step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17984step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17985Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17985step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17985step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17985step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw17985step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17985step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17985step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17985step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17985step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw17986Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17986step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw17986step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17986step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw17986step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17986step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17986step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17986step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17986step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1]]
def raw17987Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17987step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1]]
def raw17987step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17987step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw17987step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17987step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17987step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17987step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17987step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17987step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17987step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17988Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17988step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17988step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17988step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17988step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17988step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17988step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17989Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17989step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17989step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17989step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17989step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17990Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17990step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17990step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw17991Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17991step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 2, -2], ![2, -1, -1]]
def raw17991step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17991step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17991step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17991step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17991step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1]]
def raw17992Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17992step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1]]
def raw17992step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17992step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17992step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17992step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17992step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17992step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17992step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17993Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17993step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17993step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17993step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17993step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17993step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17993step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17994Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17994step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17994step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17994step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17994step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17995Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![2, -1, -1]]
def raw17996Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17996step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 2, -2], ![2, -1, -1]]
def raw17996step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17996step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17996step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17996step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17996step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1]]
def raw17997Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17997step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1]]
def raw17997step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17997step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17997step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17997step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17997step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17997step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17997step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw17998Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17998step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw17998step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17998step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw17998step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17998step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17998step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17998step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17998step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw17999Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17999step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw17999step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17999step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![2, 0, -2], ![2, -1, -1]]
def raw17999step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17999step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw17999step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw18000Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18000step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw18000step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18000step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw18000step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18000step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18000step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18001 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw18001Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18001step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw18001step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18001step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw18001step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18001step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18001step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18002 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw18002Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18002step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw18002step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18002step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![2, 0, -2], ![1, 0, -1]]
def raw18002step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18002step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw18002step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18002step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18002step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw18003Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18003step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw18003step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18003step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 1, -2], ![3, -2, -1]]
def raw18003step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18003step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![3, -1, -2]]
def raw18003step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18003step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![3, -1, -2]]
def raw18003step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18004 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw18004Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18004step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw18004step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18004step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 1, -2], ![3, -2, -1]]
def raw18004step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18004step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw18004step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18004step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw18004step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18004step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw18004step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18005 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw18005Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18005step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw18005step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18005step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18005step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18005step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw18005step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18005step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw18005step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18006 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw18006Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18006step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw18006step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18006step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18006step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18006step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw18006step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18006step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw18006step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw18007Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18007step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw18007step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18007step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![3, -2, -1]]
def raw18007step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18007step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw18007step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18007step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw18007step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18007step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw18007step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18008 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18008Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18008step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18008step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18008step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![1, 1, -2], ![2, -1, -1]]
def raw18008step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18008step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw18008step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18008step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18008step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18008step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18008step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18009Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18009step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18009step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18009step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18009step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18009step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18009step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18010 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18010Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18010step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18010step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18010step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18010step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18010step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18010step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18011 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw18011Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18011step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw18011step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18011step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![2, -1, -1]]
def raw18011step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18011step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18011step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18011step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw18011step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18011step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw18011step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18012 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1]]
def raw18012Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18012step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1]]
def raw18012step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18012step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![1, 1, -2], ![1, 0, -1]]
def raw18012step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18012step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw18012step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18012step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw18012step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18013 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18013Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18013step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18013step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18013step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw18013step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18013step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18013step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18013step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18013step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18013step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18013step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18014 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18014Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18014step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18014step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18014step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18014step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18014step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18014step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18015 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18015Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18015step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18015step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18015step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18015step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18015step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18015step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18016 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw18016Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18016step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw18016step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18016step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw18016step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18016step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw18016step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18016step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw18016step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1]]
def raw18017Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1]]
def raw18017step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18017step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw18017step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18017step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw18017step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18017step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw18017step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18018 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18018Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18018step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18018step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18018step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw18018step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18018step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18018step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18018step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18018step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18019 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18019Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18019step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18019step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18019step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw18019step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18019step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18019step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18019step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18019step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18020Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18020step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18020step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18020step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18020step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw18021Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18021step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 2, -2], ![2, -1, -1]]
def raw18021step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18021step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18021step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18021step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18021step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18021step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18021step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18022 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1]]
def raw18022Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18022step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1]]
def raw18022step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18022step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18022step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18022step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18022step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18022step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18022step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18023 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18023Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18023step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18023step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18023step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw18023step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18023step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18023step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18023step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18023step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18024Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18024step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18024step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18024step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw18024step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18024step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18024step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18024step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18024step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18025Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18025step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18025step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18025step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18025step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![2, -1, -1]]
def raw18026Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18026step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 2, -2], ![2, -1, -1]]
def raw18026step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18026step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18026step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18026step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18026step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18026step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18026step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1]]
def raw18027Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18027step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1]]
def raw18027step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18027step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18027step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18027step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18027step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18027step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18027step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18028 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw18028Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18028step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw18028step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18028step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw18028step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18028step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, -1, 2]]
def raw18028step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18028step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]
def raw18028step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18028step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]
def raw18028step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18029 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw18029Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18029step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw18029step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18029step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![2, 0, -2], ![2, -1, -1]]
def raw18029step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18029step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, 1, -2], ![2, 0, -2]]
def raw18029step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18029step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, 1, -2], ![2, 0, -2]]
def raw18029step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18030 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw18030Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18030step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw18030step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18030step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18030step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18030step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18030step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18031 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw18031Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18031step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw18031step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18031step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18031step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18031step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18031step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18032 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw18032Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18032step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw18032step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18032step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![2, 0, -2], ![1, 0, -1]]
def raw18032step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18032step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18032step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18032step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18032step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18033 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw18033Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18033step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw18033step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18033step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 1, -2], ![3, -2, -1]]
def raw18033step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18033step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![2, 1, -3]]
def raw18033step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18033step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![2, 1, -3]]
def raw18033step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18034 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw18034Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18034step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw18034step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18034step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 1, -2], ![3, -2, -1]]
def raw18034step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18034step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]
def raw18034step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18034step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]
def raw18034step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18035 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw18035Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18035step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw18035step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18035step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18035step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18035step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18035step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18036 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw18036Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18036step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw18036step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18036step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18036step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18036step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18036step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18037 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw18037Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18037step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw18037step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18037step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![3, -2, -1]]
def raw18037step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18037step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18037step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18037step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18037step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18038 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw18038Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18038step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 3, -1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw18038step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18038step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 3, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18038step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18038step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw18038step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18038step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18038step3Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18038step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18038step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18039 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw18039Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18039step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1]]
def raw18039step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18039step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18039step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18039step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18039step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18040 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1]]
def raw18040Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18040step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1]]
def raw18040step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18040step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18040step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18040step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18040step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18041 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1]]
def raw18041Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18041step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1]]
def raw18041step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18041step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1]]
def raw18041step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18041step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw18041step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18041step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18041step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18041step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18041step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18042 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1]]
def raw18042Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18042step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1]]
def raw18042step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18042step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1]]
def raw18042step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18042step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw18042step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18042step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw18042step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18043 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw18043Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18043step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw18043step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18043step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18043step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18043step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18043step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18043step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18043step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18044 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw18044Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18044step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1]]
def raw18044step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18044step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18044step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18044step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18044step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18044step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18044step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18045 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1]]
def raw18045Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18045step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1]]
def raw18045step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18045step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18045step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18045step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18045step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18045step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18045step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18046 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1]]
def raw18046Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18046step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1]]
def raw18046step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18046step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw18046step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18046step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw18046step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18047 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1]]
def raw18047Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18047step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1]]
def raw18047step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18047step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw18047step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18047step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18047step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18047step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18047step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical141
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw18048 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw18048Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18048step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -2, 1], ![2, -1, -1]]
def raw18048step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18048step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18048step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18048step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18048step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18049 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 3, -1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw18049Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18049step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 3, -1], ![1, -1, 0], ![1, -2, 1], ![2, -1, -1]]
def raw18049step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18049step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw18049step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18049step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18049step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18049step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18049step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18050 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1]]
def raw18050Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18050step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18050step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18050step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18050step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18051 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1]]
def raw18051Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18051step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![2, -1, -1]]
def raw18051step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18051step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18051step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18051step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18051step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18052 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1]]
def raw18052Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18052step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -2, 1], ![1, 0, -1]]
def raw18052step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18052step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18052step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18052step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18052step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18052step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18052step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18053 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, -1, -1]]
def raw18053Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18053step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -2, 1], ![2, -1, -1]]
def raw18053step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18053step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18053step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18053step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18053step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18054 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, -1, -1]]
def raw18054Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18054step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 3, -1], ![1, -1, 0], ![1, -2, 1], ![2, -1, -1]]
def raw18054step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18054step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw18054step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18054step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18054step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18054step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18054step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18055 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![2, -1, -1]]
def raw18055Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18055step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18055step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18055step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18055step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18056 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, -1, -1]]
def raw18056Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18056step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![2, -1, -1]]
def raw18056step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18056step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18056step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18056step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18056step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18057 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, 0, -1]]
def raw18057Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18057step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -2, 1], ![1, 0, -1]]
def raw18057step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18057step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18057step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18057step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18057step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18057step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18057step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18058 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, -1, -1]]
def raw18058Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18058step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![2, -3, 1], ![2, -1, -1]]
def raw18058step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18058step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![2, -3, 1], ![2, -1, -1]]
def raw18058step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18058step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, -1, -1], ![2, 1, -3]]
def raw18058step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18058step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, -1, -1], ![2, 1, -3]]
def raw18058step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18059 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, -1, -1]]
def raw18059Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18059step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 3, -1], ![0, 0, 0], ![2, -3, 1], ![2, -1, -1]]
def raw18059step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18059step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 3, -1], ![2, -3, 1], ![2, -1, -1]]
def raw18059step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18059step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 1, -2], ![3, -1, -2]]
def raw18059step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18059step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 1, -2], ![3, -1, -2]]
def raw18059step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18060 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![2, -1, -1]]
def raw18060Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18060step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![-1, 1, 0], ![2, -3, 1], ![2, -1, -1]]
def raw18060step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18060step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18060step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18060step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18060step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18061 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![2, -1, -1]]
def raw18061Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18061step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![-1, 1, 0], ![2, -3, 1], ![2, -1, -1]]
def raw18061step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18061step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18061step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18061step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18061step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18062 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![1, 0, -1]]
def raw18062Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18062step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![2, -3, 1], ![1, 0, -1]]
def raw18062step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18062step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![2, -3, 1], ![1, 0, -1]]
def raw18062step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18062step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18062step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18062step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18062step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18063 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, -2, -1]]
def raw18063Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18063step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![3, -2, -1]]
def raw18063step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18063step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -2, 1], ![3, -2, -1]]
def raw18063step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18063step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 1, -2], ![3, -1, -2]]
def raw18063step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18063step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 1, -2], ![3, -1, -2]]
def raw18063step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18064 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, -2, -1]]
def raw18064Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18064step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 3, -1], ![0, 0, 0], ![1, -2, 1], ![3, -2, -1]]
def raw18064step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18064step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 3, -1], ![1, -2, 1], ![3, -2, -1]]
def raw18064step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18064step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![-2, 1, 1], ![-2, -1, 3]]
def raw18064step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18064step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, -1, -1], ![2, 1, -3]]
def raw18064step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18064step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, -1, -1], ![2, 1, -3]]
def raw18064step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18065 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, -2, -1]]
def raw18065Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18065step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![-1, 1, 0], ![1, -2, 1], ![3, -2, -1]]
def raw18065step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18065step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw18065step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18065step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18065step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18065step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18065step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18066 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, -2, -1]]
def raw18066Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18066step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![-1, 1, 0], ![1, -2, 1], ![3, -2, -1]]
def raw18066step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18066step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw18066step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18066step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18066step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18066step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18066step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18067 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -2, -1]]
def raw18067Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18067step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![3, -2, -1]]
def raw18067step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18067step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![3, -2, -1]]
def raw18067step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18067step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw18067step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18067step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18067step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18067step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18067step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18068 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18068Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18068step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18068step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18068step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18068step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18068step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw18068step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18068step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw18068step3Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18068step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw18068step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18069 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18069Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18069step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18069step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18069step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18069step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18069step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18069step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18070 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18070Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18070step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18070step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18070step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18070step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18070step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18070step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18071 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw18071Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18071step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw18071step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18071step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, 0, -2]]
def raw18071step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18071step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18071step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18071step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18071step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18072 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw18072Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18072step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw18072step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18072step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2]]
def raw18072step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18072step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw18072step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18072step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw18072step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18073 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18073Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18073step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18073step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18073step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw18073step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18073step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18073step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18073step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18073step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18074 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18074Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18074step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18074step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18075 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw18075Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18075step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw18075step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18075step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw18075step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18075step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18075step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18076 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw18076Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18076step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw18076step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18076step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw18076step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18076step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18076step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18076step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18076step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18077 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18077Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18077step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18077step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18077step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw18077step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18077step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18077step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18077step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18077step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18078 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18078Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18078step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18078step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18079 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw18079Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18079step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw18079step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18079step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw18079step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18079step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18079step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18080 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw18080Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18080step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw18080step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18080step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw18080step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18080step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18080step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18080step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18080step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18081 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw18081Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18081step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw18081step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18081step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![2, -3, 1], ![2, 0, -2]]
def raw18081step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18081step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]
def raw18081step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18081step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]
def raw18081step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18082 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw18082Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18082step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw18082step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18082step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18082step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18082step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18082step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18083 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw18083Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18083step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw18083step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18083step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18083step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18083step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18083step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18084 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw18084Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18084step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw18084step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18084step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![2, -3, 1], ![1, 1, -2]]
def raw18084step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18084step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw18084step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18084step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw18084step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18085 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw18085Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18085step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw18085step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18085step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -2, 1], ![3, -1, -2]]
def raw18085step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18085step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw18085step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18085step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw18085step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18086 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw18086Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18086step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw18086step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18086step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw18086step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18086step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18086step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18087 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw18087Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18087step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw18087step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18087step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw18087step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18087step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18087step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18088 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18088Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18088step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18088step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18088step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18088step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18088step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw18088step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18088step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw18088step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18088step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw18088step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18089 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18089Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18089step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18089step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18089step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18089step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18089step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18089step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18090 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18090Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18090step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18090step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18090step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18090step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18090step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18090step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18091 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw18091Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18091step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw18091step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18091step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, 0, -2]]
def raw18091step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18091step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18091step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18091step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18091step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18092 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw18092Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18092step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw18092step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18092step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2]]
def raw18092step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18092step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18092step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18092step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18092step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18093 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18093Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18093step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18093step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18093step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw18093step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18093step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18093step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18093step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18093step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18094 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18094Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18094step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18094step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18094step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18094step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18095 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw18095Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18095step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw18095step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18095step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw18095step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18095step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18095step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18095step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18095step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18096 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw18096Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18096step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw18096step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18096step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw18096step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18096step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18096step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18096step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18096step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18097 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18097Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18097step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18097step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18097step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw18097step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18097step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18097step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18097step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18097step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18098 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18098Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18098step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18098step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18098step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18098step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18099 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw18099Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18099step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw18099step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18099step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw18099step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18099step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18099step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18099step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18099step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18100 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw18100Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18100step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw18100step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18100step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw18100step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18100step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18100step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18100step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18100step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18101 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw18101Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18101step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw18101step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18101step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![2, -3, 1], ![2, 0, -2]]
def raw18101step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18101step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]
def raw18101step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18101step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]
def raw18101step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18102 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw18102Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18102step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw18102step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18102step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18102step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18102step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18102step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18103 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw18103Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18103step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw18103step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18103step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18103step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18103step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18103step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw18104Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18104step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw18104step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18104step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![2, -3, 1], ![1, 1, -2]]
def raw18104step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18104step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw18104step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18104step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw18104step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw18105Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18105step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw18105step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18105step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -2, 1], ![3, -1, -2]]
def raw18105step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18105step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, -2, 3], ![-2, 1, 1]]
def raw18105step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18105step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw18105step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18105step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw18105step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18106 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw18106Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18106step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw18106step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18106step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18106step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18106step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18106step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18107 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw18107Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18107step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw18107step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18107step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18107step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18107step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18107step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18108Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18108step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18108step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18108step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![1, 1, -2], ![2, -2, 0]]
def raw18108step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18108step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18108step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18109 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18109Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18109step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18109step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18109step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18109step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18109step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18109step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18109step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18109step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18110 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18110Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18110step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18110step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18110step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18110step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18110step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18110step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18110step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18110step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18111 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw18111Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18111step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw18111step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18111step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 2, -2], ![2, -2, 0]]
def raw18111step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18111step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw18111step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18111step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18111step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18111step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18111step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw18112Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18112step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw18112step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18112step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![1, 1, -2], ![1, -1, 0]]
def raw18112step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18112step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw18112step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18112step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw18112step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18113 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18113Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18113step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18113step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18113step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 1, -2], ![2, -2, 0]]
def raw18113step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18113step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw18113step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18113step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw18113step3Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18113step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw18113step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18114Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18114step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18114step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18114step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18114step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18114step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18114step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18115 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18115Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18115step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18115step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18115step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18115step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18115step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18115step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18116 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw18116Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18116step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw18116step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18116step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 2, -2], ![2, -2, 0]]
def raw18116step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18116step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![2, 0, -2]]
def raw18116step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18116step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![2, 0, -2]]
def raw18116step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18117 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw18117Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18117step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw18117step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18117step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![1, 1, -2], ![1, -1, 0]]
def raw18117step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18117step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18117step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18117step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18117step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18118 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18118Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18118step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18118step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18118step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18118step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18118step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18118step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18119 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18119Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18119step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18119step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18119step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18119step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18119step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18119step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18120 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18120Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18120step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18120step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18120step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18120step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18121 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw18121Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18121step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw18121step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18121step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw18121step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18121step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18121step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18121step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18121step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18122 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw18122Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18122step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw18122step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18122step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18122step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18122step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18122step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18123 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18123Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18123step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18123step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18123step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18123step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18123step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18123step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18124 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18124Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18124step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18124step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18124step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18124step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18124step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18124step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18125 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18125Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18125step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18125step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18125step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18125step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18126 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw18126Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18126step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw18126step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18126step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw18126step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18126step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18126step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18126step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18126step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18127 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw18127Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18127step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw18127step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18127step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18127step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18127step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18127step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18128 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw18128Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18128step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw18128step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18128step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, 0, -2], ![2, -2, 0]]
def raw18128step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18128step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw18128step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18128step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw18128step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18129 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw18129Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18129step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw18129step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18129step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![2, 0, -2], ![2, -2, 0]]
def raw18129step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18129step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![2, 0, -2]]
def raw18129step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18130 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw18130Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18130step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw18130step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18130step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw18130step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18130step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18130step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18130step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18130step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18131 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw18131Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18131step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw18131step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18131step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw18131step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18131step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18131step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18131step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18131step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18132 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw18132Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18132step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw18132step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18132step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![2, 0, -2], ![1, -1, 0]]
def raw18132step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18132step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw18132step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18132step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18132step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18133 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw18133Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18133step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw18133step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18133step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 1, -2], ![3, -3, 0]]
def raw18133step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18133step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![3, 0, -3]]
def raw18133step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18133step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![3, 0, -3]]
def raw18133step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18134 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw18134Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18134step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw18134step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18134step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, 1, -2], ![3, -3, 0]]
def raw18134step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18134step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw18134step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18134step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw18134step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18134step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw18134step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18135 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw18135Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18135step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw18135step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18135step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw18135step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18135step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18135step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18135step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18135step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18136 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw18136Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18136step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw18136step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18136step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw18136step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18136step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18136step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18136step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18136step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18137 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw18137Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18137step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw18137step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18137step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 2, -2], ![3, -3, 0]]
def raw18137step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18137step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw18137step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18137step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw18137step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18138 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18138Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18138step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18138step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18138step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw18138step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18138step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18138step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18138step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18138step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18139Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18139step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw18139step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18139step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18139step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18140 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18140Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18140step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18140step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18140step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw18140step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18140step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18140step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18141 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw18141Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18141step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw18141step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18141step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, 0, -2]]
def raw18141step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18141step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18141step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18141step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18141step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18142 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18142Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18142step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18142step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18142step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18142step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18142step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18142step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18143 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18143Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18143step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18143step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18143step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18143step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18144 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18144Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18144step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw18144step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18144step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18144step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18144step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18144step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18145 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18145Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18145step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18145step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18146 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw18146Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18146step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw18146step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18146step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw18146step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18146step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18146step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18147 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18147Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18147step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw18147step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18147step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18147step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18147step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18147step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18148 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18148Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18148step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18148step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18148step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw18148step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18148step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18148step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18148step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18148step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18149 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18149Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18149step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18149step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![2, 0, -2]]
def raw18150Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18150step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18150step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18150step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18150step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18151 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18151Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18151step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18151step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18151step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw18151step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18151step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18151step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18151step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18151step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18152 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw18152Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18152step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw18152step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18152step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw18152step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18152step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw18152step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18152step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw18152step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18153 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw18153Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18153step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18153step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18153step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18153step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18153step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18153step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18154 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw18154Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18154step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw18154step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18154step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw18154step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18154step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18154step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18155 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw18155Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18155step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw18155step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18155step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw18155step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18155step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw18155step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18156 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw18156Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18156step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw18156step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18156step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw18156step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18156step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw18156step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18157 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw18157Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18157step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw18157step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18157step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18157step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18158 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw18158Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18158step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw18158step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18158step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw18158step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18158step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18158step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18159 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![3, -1, -2]]
def raw18159Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18159step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw18159step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18159step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![3, -1, -2]]
def raw18159step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18159step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw18159step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18159step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18159step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18160 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18160Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18160step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18160step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18160step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw18160step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18160step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18160step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18160step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18160step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18161 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18161Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18161step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18161step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18161step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18161step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18162 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18162Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18162step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18162step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18162step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw18162step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18162step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw18162step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18163 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw18163Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18163step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw18163step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18163step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, 0, -2]]
def raw18163step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18163step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18163step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18163step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18163step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18164 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18164Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18164step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18164step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18164step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw18164step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18164step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18164step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18164step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18164step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18165 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18165Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18165step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18165step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18165step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw18165step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18165step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18165step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18165step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18165step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18166 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18166Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18166step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw18166step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18166step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18166step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18166step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18166step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18167 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18167Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18167step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw18167step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18167step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18167step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18167step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18167step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18168 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw18168Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18168step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw18168step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18168step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw18168step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18168step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18168step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18168step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18168step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18169 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18169Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18169step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw18169step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18169step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18169step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18169step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18169step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18170 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18170Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18170step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18170step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18170step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw18170step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18170step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18170step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18170step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18170step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18171Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18171step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18171step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18171step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18171step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![2, 0, -2]]
def raw18172Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18172step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18172step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18172step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18172step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18172step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18172step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18172step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18172step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18173 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18173Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18173step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18173step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18173step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw18173step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18173step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18173step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18173step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18173step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18174 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw18174Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18174step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw18174step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18174step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw18174step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18174step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw18174step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18174step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw18174step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18175 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw18175Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18175step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18175step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18175step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18175step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical142
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw18176 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw18176Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18176step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw18176step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18176step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw18176step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18176step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw18176step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18176step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw18176step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18177 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw18177Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18177step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw18177step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18177step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw18177step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18177step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw18177step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18178 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw18178Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18178step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw18178step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18178step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw18178step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18178step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw18178step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18178step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw18178step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18179 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw18179Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18179step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18179step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18179step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18179step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18180 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw18180Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18180step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw18180step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18180step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18180step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18180step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18180step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18181 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![3, -1, -2]]
def raw18181Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18181step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw18181step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18181step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![3, -1, -2]]
def raw18181step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18181step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18181step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18181step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18181step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18182 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18182Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18182step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18182step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18182step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18182step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18183 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18183Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18183step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18183step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18183step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18183step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18183step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18183step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18184 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18184Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18184step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18184step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18184step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw18184step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18184step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18184step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18184step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18184step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18185 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw18185Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18185step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw18185step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18185step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18185step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18185step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18185step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18186 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18186Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18186step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18186step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18186step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw18186step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18186step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18186step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18186step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18186step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18187 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18187Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18187step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18187step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18187step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw18187step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18187step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw18187step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18187step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw18187step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18188 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18188Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18188step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw18188step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18188step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw18188step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18189 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18189Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18189step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18189step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18189step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw18189step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18189step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw18189step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18189step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw18189step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18190 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw18190Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18190step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw18190step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18190step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18190step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18190step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18190step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18191 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18191Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18191step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18191step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18191step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18191step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18191step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18191step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18192 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18192Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18192step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw18192step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18192step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18192step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18192step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18192step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18193 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18193Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18193step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw18193step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18193step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw18193step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18194 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18194Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18194step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw18194step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18194step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18194step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18194step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18194step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18195 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw18195Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18195step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18195step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18195step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18195step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18196 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18196Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18196step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18196step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18196step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18196step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18196step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18196step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18197 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18197Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18197step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18197step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18197step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18197step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18197step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18197step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18198 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18198Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18198step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18198step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18198step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18198step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18198step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18198step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18199 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18199Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18199step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18199step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18199step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18199step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw18200Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18200step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw18200step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18200step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw18200step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18200step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18200step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18200step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18200step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18201Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18201step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18201step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18201step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18201step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18201step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18201step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw18202Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18202step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw18202step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18202step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw18202step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18202step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw18202step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18202step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw18202step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18203 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw18203Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18203step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw18203step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18203step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw18203step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18203step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw18203step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18203step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw18203step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18204 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw18204Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18204step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw18204step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18204step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18204step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18204step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18204step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18205 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 2, -1], ![2, -1, -1], ![2, -2, 0]]
def raw18205Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18205step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 2, -1], ![2, -1, -1], ![2, -2, 0]]
def raw18205step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18205step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw18205step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18205step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw18205step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18205step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw18205step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18206 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw18206Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18206step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw18206step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18206step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw18206step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18206step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18206step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18206step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18206step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18207 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw18207Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18207step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw18207step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18207step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-3, 0, 3]]
def raw18207step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18207step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw18207step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18207step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw18207step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18208 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw18208Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18208step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw18208step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18208step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw18208step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18208step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw18208step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18208step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw18208step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18209 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw18209Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18209step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw18209step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18209step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18209step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18209step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18209step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18210 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw18210Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18210step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw18210step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18210step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw18210step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18210step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw18210step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18210step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw18210step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18211 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw18211Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18211step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw18211step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18211step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18211step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18211step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18211step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18212 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18212Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18212step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18212step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18212step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18212step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18213 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18213Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18213step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw18213step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18213step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18213step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18214 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18214Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18214step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18214step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18214step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18214step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18215 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw18215Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18215step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw18215step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18215step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18215step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18215step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18215step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18216 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18216Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18216step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18216step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18216step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18216step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18217 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18217Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18217step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18217step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18217step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw18217step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18217step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18217step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18218 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18218Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18218step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18218step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18218step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18218step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18219 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw18219Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18219step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw18219step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18219step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw18219step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18219step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18219step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18219step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18219step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end


