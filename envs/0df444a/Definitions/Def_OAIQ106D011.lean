-- Prove2me | Definitions.Def_OAIQ106D011
-- name    : OAIQ106D011
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T12:02:24.490232+00:00
-- url     : https://prove2.me/theorems/a18aae91-7156-414d-914b-a9dc1784b38f
-- title:
--   Definitions bundle OAIQ106D011 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 6820 declarations of OpenAI's Lean: 6820 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSemantics.raw16504step0`, `OAI.MUB6.Certificate.MixedSemantics.raw16504step1`, `OAI.MUB6.Certificate.MixedSemantics.raw16504step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw16504step2`, `OAI.MUB6.Certificate.MixedSemantics.raw16504step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw16505`, `OAI.MUB6.Certificate.MixedSemantics.raw16505Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw16505step0`, `OAI.MUB6.Certificate.MixedSemantics.raw16505step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw16505step1`, `OAI.MUB6.Certificate.MixedSemantics.raw16505step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw16505step2`, `OAI.MUB6.Certificate.MixedSemantics.raw16505step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw16505step3`, `OAI.MUB6.Certificate.MixedSemantics.raw16505step3Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw16506`, `OAI.MUB6.Certificate.MixedSemantics.raw16506Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw16506step0`, `OAI.MUB6.Certificate.MixedSemantics.raw16506step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw16506step1`, `OAI.MUB6.Certificate.MixedSemantics.raw16506step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw16506step2`, `OAI.MUB6.Certificate.MixedSemantics.raw16506step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw16507`, `OAI.MUB6.Certificate.MixedSemantics.raw16507Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw16507step0`, `OAI.MUB6.Certificate.MixedSemantics.raw16507step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw16507step1`, `OAI.MUB6.Certificate.MixedSemantics.raw16507step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw16507step2`, `OAI.MUB6.Certificate.MixedSemantics.raw16507step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw16507step3`, `OAI.MUB6.Certificate.MixedSemantics.raw16507step3Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw16508`, `OAI.MUB6.Certificate.MixedSemantics.raw16508Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw16508step0`, `OAI.MUB6.Certificate.MixedSemantics.raw16508step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw16508step1`, `OAI.MUB6.Certificate.MixedSemantics.raw16508step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw16508step2` and 6780 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_MixedSemantics_Canonical0`, `MutuallyUnbiased_MixedSemantics_Canonical1`, `MutuallyUnbiased_MixedSemantics_Canonical12`, `MutuallyUnbiased_MixedSemantics_Canonical128`, `MutuallyUnbiased_MixedSemantics_Canonical129`, `MutuallyUnbiased_MixedSemantics_Canonical13`, `MutuallyUnbiased_MixedSemantics_Canonical130`, `MutuallyUnbiased_MixedSemantics_Canonical131`, `MutuallyUnbiased_MixedSemantics_Canonical132`, `MutuallyUnbiased_MixedSemantics_Canonical133`, `MutuallyUnbiased_MixedSemantics_Canonical134`, `MutuallyUnbiased_MixedSemantics_Canonical135`, `MutuallyUnbiased_MixedSemantics_Canonical136`, `MutuallyUnbiased_MixedSemantics_Canonical137`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound1451`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound102`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound103`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound109`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound111`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound115`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound118`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound119`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound120`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound123`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound127`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound19`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound28`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound30`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound34`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound35`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound36`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound46`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound54`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound55`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound56`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound57`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound58`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound7`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound81`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound110`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1111`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1123`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound113`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1130`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1158`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1169`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1264`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1293`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1318`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound145`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1465`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1471`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1480`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1483`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1493`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1517`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1655`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1657`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1672`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1673`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1679`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1686`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1687`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1702`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1708`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1715`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1716`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1723`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1734`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1738`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1739`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1740`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1743`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1822`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1839`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1844`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1848`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1853`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1858`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1864`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1865`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1871`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1872`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1874`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1877`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1880`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1881`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1906`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1910`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1911`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1914`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1944`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1952`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1958`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1960`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1963`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1965`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1968`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1970`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1971`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1976`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1980`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1983`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1984`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1988`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1989`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1990`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1993`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1994`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1995`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1998`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1999`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2002`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2003`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2004`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2005`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2006`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2010`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2011`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2015`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2021`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2023`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2041`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2060`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2066`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2076`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2084`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2085`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2094`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2108`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound267`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound365`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound444`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound512`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound514`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound538`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound545`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound551`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound553`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound564`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound580`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound584`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound588`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound599`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound620`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound728`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound742`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound749`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound795`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound799`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound813`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound877`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound878`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound881`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound882`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound883`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound884`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound885`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound886`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound888`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound890`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound892`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound894`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound896`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound897`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound898`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound899`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound900`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound901`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound903`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound905`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound906`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound908`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound909`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound910`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound911`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound912`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound914`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound915`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound916`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound918`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound920`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound921`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound928`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound931`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound934`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound943`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound946`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound952`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound965`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound967`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound97`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound986`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound39` and `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound40`.
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

def raw16Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![2, 0, -2], ![3, -3, 0]]
def raw16step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![2, 0, -2], ![3, -3, 0]]
def raw16step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -5, 3], ![-2, 2, 0], ![0, 3, -3]]

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

def raw165Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw165step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw165step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw166 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -4, 3], ![-2, 1, 1], ![1, 3, -4]]
def raw166Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw166step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 1, -2], ![3, -4, 1]]
def raw166step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw166step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 1, -2], ![3, -4, 1]]
def raw166step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw167 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -4, 3], ![-2, 1, 1], ![1, 3, -4]]
def raw167Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw167step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![3, 1, -4]]
def raw167step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw168 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -4, 3], ![1, 2, -3], ![-2, 2, 0]]
def raw168Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw168step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![2, -3, 1], ![2, 0, -2]]
def raw168step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw168step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![2, -3, 1], ![2, 0, -2]]
def raw168step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw169 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -4, 3], ![1, 2, -3], ![-2, 2, 0]]
def raw169Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw169step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw169step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw170 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![2, 0, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw170Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw170step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw170step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw170step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw170step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw171 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![2, 0, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw171Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw171step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw171step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw171step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw171step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw174 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![2, 0, -2], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw174Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw174step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw174step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw174step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw174step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw175 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![2, 0, -2], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw1650Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1650step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1650step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1650step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1650step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1651 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1651Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1651step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1651step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1652 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1652Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1652step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw1652step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1652step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw1652step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1652step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw1652step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1653 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![1, 1, -2], ![-1, 2, -1]]
def raw1653Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1653step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw1653step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1653step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw1653step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1654 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![1, 1, -2], ![-1, 2, -1]]
def raw1654Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1654step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw1654step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1655 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![1, 1, -2], ![-1, 2, -1]]
def raw1655Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1655step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw1655step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1655step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw1655step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1655step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw1655step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1656 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw1656Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1656step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw1656step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1656step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw1656step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1657 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw1657Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1657step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw1657step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1658 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw1658Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1658step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw1658step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1658step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw1658step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1658step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw1658step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1659 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![-2, 3, -1]]
def raw1659Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1659step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw1659step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1659step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw1659step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1660 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![-2, 3, -1]]
def raw1660Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1660step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw1660step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1661 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![-2, 3, -1]]
def raw1661Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1661step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, -2, 3], ![-2, 1, 1]]
def raw1661step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1661step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw1661step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1661step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw1661step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1662 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, 0, -1], ![-2, 2, 0], ![1, 2, -3]]
def raw1662Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1662step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw1662step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1662step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw1662step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1663 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, 0, -1], ![-2, 2, 0], ![1, 2, -3]]
def raw1663Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1663step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw1663step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical128
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw16504step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]

def raw16504step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16504step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16504step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16504step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16505 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16505Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16505step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16505step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16505step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16505step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16505step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw16505step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16505step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw16505step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16506 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw16506Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16506step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw16506step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16506step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16506step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16506step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16506step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16507 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16507Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16507step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16507step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16507step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw16507step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16507step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16507step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16507step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16507step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16508 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16508Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16508step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw16508step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16508step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16508step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16508step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16508step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16509 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16509Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16509step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16509step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16509step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16509step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16509step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw16509step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16509step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw16509step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16510 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16510Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16510step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16510step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16510step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw16510step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16510step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16510step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16510step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16510step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16511 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw16511Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16511step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw16511step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16511step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw16511step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16511step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16511step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16511step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16511step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical129
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw16512 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16512Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16512step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16512step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16512step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16512step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16512step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16512step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16513 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16513Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16513step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16513step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16513step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw16513step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16513step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw16513step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16514 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16514Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16514step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16514step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16514step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16514step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16514step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16514step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16515 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16515Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16515step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16515step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16515step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16515step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16515step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16515step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16516 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw16516Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16516step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw16516step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16516step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw16516step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16516step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw16516step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16517 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16517Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16517step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16517step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16517step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16517step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16517step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16517step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16517step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16517step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16518 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16518Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16518step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16518step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16518step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 2, -2], ![-1, -1, 2], ![-2, 1, 1]]
def raw16518step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16518step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw16518step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16518step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw16518step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16519 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16519Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16519step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16519step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16519step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16519step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16519step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16519step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16520 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16520Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16520step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16520step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16520step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16520step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16520step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16520step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16520step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16520step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16521 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw16521Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16521step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw16521step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16521step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw16521step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16521step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16521step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16521step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16521step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16522 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw16522Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16522step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw16522step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16522step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16522step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16522step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16522step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16522step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16522step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16523 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw16523Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16523step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw16523step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16523step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw16523step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16523step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw16523step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16524 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw16524Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16524step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16524step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16524step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16524step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw16525Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16525step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw16525step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16525step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw16525step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16525step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw16525step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw16526Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16526step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw16526step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16526step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16526step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16526step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16526step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16527 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw16527Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16527step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw16527step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16527step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, -1, 3]]
def raw16527step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16527step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw16527step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16527step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw16527step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16528 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw16528Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16528step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw16528step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16528step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw16528step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16528step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw16528step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16529 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw16529Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16529step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16529step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16529step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16529step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw16530Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16530step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw16530step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16530step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw16530step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16530step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw16530step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16531 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw16531Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16531step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw16531step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16531step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw16531step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16531step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw16531step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16532 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16532Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16532step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16532step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16532step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16532step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16532step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16532step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16536 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw16536Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16536step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw16536step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16536step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw16536step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16538 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![0, 0], ![-1, 1], ![2, -2], ![1, -1]]
def raw16538Labels : Fin 2 → Fin 2 := ![0, 1]

def raw16538step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![-1, 1], ![2, -2], ![1, -1]]
def raw16538step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw16538step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![1, -1]]
def raw16538step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw16538step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw16538step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw16539 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16539Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16539step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16539step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16539step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16539step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16540Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16540step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw16540step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16541 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16541Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16541step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16541step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16541step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16541step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw16542Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16542step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw16542step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16542step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw16542step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16542step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw16542step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16543 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw16543Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16543step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw16543step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16543step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw16543step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16543step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw16543step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16545 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16545Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16545step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16545step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16545step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16545step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16550 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw16550Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16550step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw16550step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16550step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16550step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16552 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16552Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16552step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16552step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16552step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16552step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16552step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16552step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16554 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw16554Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16554step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw16554step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16554step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16554step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16554step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16554step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16555 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw16555Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16555step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw16555step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16555step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16555step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16555step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16555step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16556 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16556Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16556step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16556step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16556step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16556step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16556step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16556step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16557 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16557Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16557step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16557step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16557step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw16557step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16557step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16557step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16558 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw16558Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16558step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw16558step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16558step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16558step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16558step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16558step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16560 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw16560Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16560step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw16560step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16560step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw16560step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16563 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw16563Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16563step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw16563step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16563step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw16563step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16563step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw16563step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16563step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw16563step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16566 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw16566Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16566step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw16566step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16566step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw16566step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16569 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16569Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16569step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16569step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16569step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-2, 1, 1], ![-1, -1, 2]]
def raw16569step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16569step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16569step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16570 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw16570Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16570step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw16570step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16570step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16570step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16571 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw16571Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16571step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw16571step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16571step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16571step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16572 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -2, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16572Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16572step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -2, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16572step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16572step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 2, -1], ![-1, -2, 3], ![-2, 1, 1]]
def raw16572step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16572step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw16572step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16573 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16573Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16573step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16573step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16573step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![-2, 1, 1], ![-1, -1, 2]]
def raw16573step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16573step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw16573step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16573step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw16573step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16574 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw16574Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16574step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw16574step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16574step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-3, 1, 2]]
def raw16574step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16574step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![3, -1, -2]]
def raw16574step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16575 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw16575Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16575step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw16575step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16575step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw16575step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16575step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw16575step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16576 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16576Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16576step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16576step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16576step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw16576step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16577 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw16577Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16577step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![2, -2, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw16577step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16577step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw16577step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16578 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw16578Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16578step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw16578step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16578step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw16578step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16578step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw16578step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16579 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16579Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16579step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16579step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16580 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw16580Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16580step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw16580step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16580step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw16580step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16581 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw16581Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16581step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw16581step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16581step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-2, 1, 1], ![0, -2, 2]]
def raw16581step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16581step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw16581step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16582 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw16582Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16582step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw16582step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16582step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw16582step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16583 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16583Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16583step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16583step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16583step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-2, 1, 1], ![-1, -1, 2]]
def raw16583step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16583step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw16583step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16583step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw16583step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16584 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw16584Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16584step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw16584step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16584step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16584step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16584step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16584step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16584step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16584step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16585 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw16585Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16585step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw16585step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16585step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16585step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16585step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw16585step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16585step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw16585step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16586 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -2, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16586Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16586step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -2, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16586step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16586step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![-1, 2, -1], ![-1, 0, 1], ![-2, -1, 3]]
def raw16586step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16586step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw16586step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16586step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw16586step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16587 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16587Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16587step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16587step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16587step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![-2, 1, 1], ![-1, -1, 2]]
def raw16587step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16587step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16587step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16587step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16587step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16588 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw16588Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16588step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw16588step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16588step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, -1, 3]]
def raw16588step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16588step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw16588step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16588step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw16588step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16589 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw16589Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16589step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw16589step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16589step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw16589step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16589step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw16589step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16590 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16590Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16590step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16590step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16590step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw16590step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16590step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw16590step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16590step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw16590step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16591 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw16591Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16591step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![2, -2, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw16591step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16591step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw16591step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16591step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw16591step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16591step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw16591step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16592 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw16592Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16592step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw16592step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16592step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw16592step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16592step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw16592step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16593 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw16593Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16593step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw16593step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16593step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16593step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16593step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16593step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16593step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16593step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16594 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw16594Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16594step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw16594step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16594step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-2, 1, 1], ![0, -2, 2]]
def raw16594step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16594step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw16594step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16594step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw16594step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16595 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw16595Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16595step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw16595step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16595step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16595step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16595step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16595step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16595step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16595step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16596 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16596Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16596step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16596step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16596step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-2, 1, 1], ![-1, -1, 2]]
def raw16596step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16596step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw16596step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16597 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw16597Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16597step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw16597step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16597step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw16597step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16598 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw16598Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16598step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw16598step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16598step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw16598step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16599 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw16599Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16599step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw16599step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16599step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw16599step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16600 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw16600Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16600step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![2, -2, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw16600step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16600step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw16600step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16601 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw16601Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16601step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw16601step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16601step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16601step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16632 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16632Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16632step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16632step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16632step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16632step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16633 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16633Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16633step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16633step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16633step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16633step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16634 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16634Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16634step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16634step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16634step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw16634step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16634step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw16634step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16635 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]
def raw16635Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16635step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0]]
def raw16635step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16635step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0]]
def raw16635step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16635step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2]]
def raw16635step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16635step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw16635step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16636 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw16636Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16636step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw16636step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16636step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16636step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16636step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16636step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16637 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16637Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16637step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16637step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16637step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16638 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16638Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16638step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw16638step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16638step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw16638step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16639 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16639Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16639step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16639step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16639step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16639step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16639step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16639step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

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

def raw1664 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, 0, -1], ![-2, 2, 0], ![1, 2, -3]]
def raw1664Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw1664step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1664step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw1664step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1664step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw1664step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1665 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, 0, -2], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1665Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1665step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1665step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1665step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1665step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1666 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, 0, -2], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1666Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1666step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1666step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1667 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, 0, -2], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1667Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1667step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw1667step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1667step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1667step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1667step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1667step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1668 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, 0, -2], ![0, 1, -1], ![-2, 3, -1]]
def raw1668Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1668step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw1668step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1668step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw1668step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1669 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, 0, -2], ![0, 1, -1], ![-2, 3, -1]]
def raw1669Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1669step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw1669step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1670 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, 0, -2], ![0, 1, -1], ![-2, 3, -1]]
def raw1670Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1670step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, 0, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw1670step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1670step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw1670step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1670step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw1670step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1671 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, 0, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw1671Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1671step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw1671step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1671step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw1671step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1672 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, 0, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw1672Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1672step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw1672step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1673 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, 0, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw1673Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1673step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw1673step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1673step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw1673step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1673step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw1673step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1674 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, 0, -2], ![-1, 2, -1], ![-1, 2, -1]]
def raw1674Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1674step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw1674step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1674step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw1674step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1675 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, 0, -2], ![-1, 2, -1], ![-1, 2, -1]]
def raw1675Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1675step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw1675step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1676 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, 0, -2], ![-1, 2, -1], ![-1, 2, -1]]
def raw1676Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1676step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, -1, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw1676step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1676step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw1676step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1676step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw1676step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1677 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, 1, -3], ![-2, 3, -1]]
def raw1677Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1677step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 2, -3], ![3, -2, -1]]
def raw1677step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1677step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 2, -3], ![3, -2, -1]]
def raw1677step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1678 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, 1, -3], ![-2, 3, -1]]
def raw1678Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1678step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 2, -3], ![3, -2, -1]]
def raw1678step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1679 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, 1, -3], ![-2, 3, -1]]
def raw1679Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1679step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, -2, 3], ![-3, 2, 1]]
def raw1679step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1679step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 2, -3], ![3, -2, -1]]
def raw1679step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1679step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 2, -3], ![3, -2, -1]]
def raw1679step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1686 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw1686Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1686step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw1686step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1686step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw1686step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1687 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw1687Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1687step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw1687step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1688 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw1688Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1688step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw1688step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1688step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw1688step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1689 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw1689Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1689step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw1689step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1689step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw1689step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1690 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw1690Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1690step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw1690step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1691 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw1691Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1691step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw1691step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1691step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw1691step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1691step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw1691step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1692 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw1692Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1692step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw1692step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1692step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw1692step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1693 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw1693Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1693step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw1693step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1694 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw1694Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1694step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw1694step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1694step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw1694step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1694step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw1694step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1695 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1695Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1695step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1695step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1695step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1695step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1696 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1696Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1696step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1696step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1697 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1697Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1697step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw1697step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1697step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw1697step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1697step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw1697step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1698 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1698Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1698step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1698step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1698step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1698step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1699 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1699Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1699step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1699step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1700 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1700Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1700step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw1700step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1700step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw1700step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1700step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw1700step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1701 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1701Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1701step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1701step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1701step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1701step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1702 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1702Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1702step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1702step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1703 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1703Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1703step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw1703step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1703step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw1703step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1703step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw1703step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1704 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![-1, 2, -1], ![-1, 3, -2]]
def raw1704Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1704step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw1704step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1704step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw1704step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1705 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![-1, 2, -1], ![-1, 3, -2]]
def raw1705Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1705step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw1705step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1706 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![-1, 2, -1], ![-1, 3, -2]]
def raw1706Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1706step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![-1, -1, 2], ![-2, -1, 3]]
def raw1706step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1706step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw1706step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1706step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw1706step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1707 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2], ![-2, 3, -1]]
def raw1707Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1707step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw1707step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1707step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw1707step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1708 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2], ![-2, 3, -1]]
def raw1708Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1708step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw1708step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1709 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2], ![-2, 3, -1]]
def raw1709Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1709step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![-1, -2, 3], ![-2, 0, 2]]
def raw1709step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1709step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw1709step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1709step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw1709step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1710 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 3, -3]]
def raw1710Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1710step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw1710step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1710step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw1710step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1711 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 3, -3]]
def raw1711Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1711step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw1711step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1712 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 3, -3]]
def raw1712Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1712step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw1712step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1712step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw1712step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1713 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw1713Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1713step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw1713step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1713step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw1713step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1714 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw1714Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1714step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw1714step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1715 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw1715Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1715step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw1715step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1715step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw1715step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1715step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw1715step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1716 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw1716Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1716step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1716step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1716step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1716step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1717 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw1717Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1717step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1717step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1718 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw1718Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1718step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw1718step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1718step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw1718step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1718step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw1718step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1719 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw1719Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1719step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw1719step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1719step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw1719step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1720 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw1720Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1720step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw1720step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1721 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw1721Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1721step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw1721step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1721step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw1721step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1721step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw1721step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1722 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![-1, 3, -2]]
def raw1722Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1722step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw1722step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1722step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw1722step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1723 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![-1, 3, -2]]
def raw1723Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1723step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw1723step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1724 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![-1, 3, -2]]
def raw1724Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-2, 1, 1], ![-2, -1, 3]]
def raw1724step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1724step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw1724step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1724step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw1724step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1725 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2]]
def raw1725Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1725step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw1725step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1725step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw1725step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1726 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2]]
def raw1726Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1726step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw1726step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1727 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2]]
def raw1727Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1727step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw1727step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1727step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw1727step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1727step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw1727step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1728 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-2, 1, 1], ![0, 3, -3]]
def raw1728Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1728step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw1728step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1728step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw1728step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1729 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-2, 1, 1], ![0, 3, -3]]
def raw1729Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw1729step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1730 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-2, 1, 1], ![0, 3, -3]]
def raw1730Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1730step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw1730step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1730step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw1730step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1731 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw1731Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1731step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw1731step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1731step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw1731step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1732 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw1732Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1732step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw1732step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1733 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw1733Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1733step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw1733step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1733step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw1733step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1733step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw1733step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1734 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw1734Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1734step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw1734step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1734step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw1734step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1735 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw1735Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1735step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw1735step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1736 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw1736Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1736step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw1736step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1736step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw1736step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1736step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw1736step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1737 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw1737Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1737step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw1737step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1737step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw1737step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1738 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw1738Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1738step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw1738step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1739 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw1739Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1739step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw1739step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1739step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw1739step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1739step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw1739step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1740 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1740Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1740step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1740step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1740step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1740step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1741 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1741Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1741step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1741step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1742 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1742Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1742step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw1742step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1742step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw1742step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1742step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw1742step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1743 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1743Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1743step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1743step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1743step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1743step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1744 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1744Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1744step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1744step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1745 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1745Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1745step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw1745step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1745step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw1745step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1745step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw1745step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1746 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1746Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1746step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1746step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1746step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1746step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1747 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1747Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1747step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1747step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1748 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1748Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1748step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw1748step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1748step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw1748step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1748step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw1748step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1749 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1749Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1749step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1749step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1749step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1749step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1750 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1750Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1750step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1750step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1751 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1751Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1751step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw1751step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1751step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw1751step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1751step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw1751step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1752 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]
def raw1752Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1752step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw1752step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1752step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw1752step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1753 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]
def raw1753Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1753step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw1753step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1754 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]
def raw1754Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1754step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw1754step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1754step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1754step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1754step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1754step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1755 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-2, 1, 1], ![0, 1, -1], ![1, 2, -3]]
def raw1755Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1755step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw1755step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1755step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw1755step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1756 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-2, 1, 1], ![0, 1, -1], ![1, 2, -3]]
def raw1756Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1756step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw1756step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1757 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-2, 1, 1], ![0, 1, -1], ![1, 2, -3]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical130
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw16640 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]
def raw16640Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16640step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0]]
def raw16640step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16640step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw16640step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16640step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0]]
def raw16640step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16640step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw16640step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16641 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw16641Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16641step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw16641step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16641step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16641step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16642 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16642Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16642step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw16642step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16643 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16643Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16643step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw16643step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16644 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16644Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16644step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, 0, -1], ![-1, -1, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw16644step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16644step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw16644step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16645 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]
def raw16645Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16645step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw16645step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16645step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16645step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16645step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16645step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16646 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw16646Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16646step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw16646step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16647 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16647Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16647step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16647step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16647step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw16647step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16648 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16648Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16648step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16648step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16648step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw16648step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16649 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16649Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16649step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16649step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16649step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16649step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16650 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0]]
def raw16650Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16650step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw16650step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16650step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw16650step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16650step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw16650step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16650step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16650step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16651 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw16651Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16651step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw16651step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16651step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16651step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16652 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw16652Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16652step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw16652step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16652step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw16652step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16653 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw16653Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16653step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw16653step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16653step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw16653step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16654 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw16654Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16654step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16654step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16654step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16654step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16655 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -2, 0]]
def raw16655Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16655step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 2, -1], ![2, -2, 0], ![2, -2, 0]]
def raw16655step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16655step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![-1, -1, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw16655step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16655step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw16655step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16656 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw16656Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16656step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw16656step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16656step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16656step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16656step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16656step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16657 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw16657Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16657step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw16657step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16657step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw16657step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16657step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw16657step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16658 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw16658Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16658step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw16658step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16658step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, -1, 3]]
def raw16658step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16658step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw16658step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16659 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw16659Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16659step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16659step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16659step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16659step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16660 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![3, -3, 0]]
def raw16660Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16660step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 2, -1], ![1, -1, 0], ![3, -3, 0]]
def raw16660step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16660step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, -1, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw16660step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16660step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw16660step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16661 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw16661Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16661step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0]]
def raw16661step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16661step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![3, -3, 0]]
def raw16661step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16661step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16661step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16661step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16661step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16662 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16662Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16662step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16662step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16662step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw16662step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16662step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw16662step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16663 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16663Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16663step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16663step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw16663step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16663step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16664 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16664Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16664step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16664step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16664step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw16664step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16664step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16665 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw16665Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16665step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw16665step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16665step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16665step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw16665step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16665step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16666 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16666Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16666step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16666step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16666step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw16666step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw16666step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16666step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw16666step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16666step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16667 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16667Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16667step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16667step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16667step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw16667step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16667step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw16667step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16668 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16668Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16668step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw16668step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16668step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw16668step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16669 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16669Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16669step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16669step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16669step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw16669step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16669step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw16669step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16670 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw16670Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16670step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw16670step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16670step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw16670step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16670step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw16670step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16671 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16671Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16671step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16671step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16671step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16671step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16671step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16671step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16672 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16672Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16672step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw16672step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16672step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw16672step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16673 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16673Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16673step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw16673step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16674 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16674Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16674step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16674step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16674step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16674step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16675 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw16675Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16675step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16675step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16675step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16675step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16676 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16676Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16676step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw16676step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16676step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw16676step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16677 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16677Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16677step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16677step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16677step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16677step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16677step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16678 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16678Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16678step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16678step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16678step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16678step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16679 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16679Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16679step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw16679step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16679step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16679step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16680 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![2, 0, -2]]
def raw16680Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16680step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -2, 1], ![0, 1, -1], ![2, 0, -2]]
def raw16680step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16680step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw16680step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16680step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw16680step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16680step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw16680step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16681 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16681Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16681step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16681step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16681step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw16681step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16681step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16681step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16681step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16681step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16682 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw16682Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16682step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw16682step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16682step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16682step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16682step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16682step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16683 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw16683Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16683step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw16683step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16683step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw16683step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16683step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw16683step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16684 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw16684Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16684step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw16684step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16684step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16684step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16685 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw16685Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16685step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw16685step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16685step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16685step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16685step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16685step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16686 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 1, -2]]
def raw16686Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16686step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![2, -1, -1], ![1, 1, -2]]
def raw16686step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16686step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16686step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16686step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16686step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16687 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw16687Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16687step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw16687step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16687step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw16687step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16687step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw16687step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16688 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw16688Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16688step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw16688step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16688step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw16688step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16688step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw16688step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16689 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw16689Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16689step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw16689step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16689step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16689step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16690 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw16690Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16690step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw16690step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16690step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16690step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16690step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16690step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16691 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw16691Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16691step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw16691step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16691step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16691step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16691step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16691step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16692 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16692Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16692step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16692step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16692step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw16692step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16692step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw16692step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16693 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16693Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16693step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16693step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16693step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16693step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16694 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16694Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16694step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16694step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16694step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16694step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16694step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16694step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16695 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw16695Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16695step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw16695step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16695step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16695step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16695step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16695step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16696 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16696Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16696step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16696step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16696step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16696step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16696step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16696step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16697 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16697Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16697step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16697step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw16697step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16697step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw16697step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16697step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw16697step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16698 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16698Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16698step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw16698step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16698step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw16698step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16698step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw16698step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16699 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16699Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16699step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16699step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16699step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw16699step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16699step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw16699step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16700 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw16700Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16700step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw16700step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16700step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw16700step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16700step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw16700step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16700step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw16700step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16701 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16701Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16701step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16701step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16701step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw16701step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16701step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16701step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16701step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16701step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16702 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16702Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16702step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw16702step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16702step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw16702step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16702step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw16702step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16703 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16703Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16703step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw16703step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16703step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw16703step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16704 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16704Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16704step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw16704step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16704step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw16704step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16705 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw16705Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16705step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16705step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16705step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16705step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16706 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16706Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16706step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw16706step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16706step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw16706step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16706step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw16706step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16707 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16707Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16707step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16707step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16707step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw16707step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16707step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw16707step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16707step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw16707step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16708 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16708Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16708step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16708step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16708step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw16708step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16708step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw16708step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16709 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16709Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16709step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw16709step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16709step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw16709step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16709step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw16709step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16710 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![2, 0, -2]]
def raw16710Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16710step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -2, 1], ![0, 1, -1], ![2, 0, -2]]
def raw16710step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16710step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw16710step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16710step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw16710step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16710step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw16710step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16711 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16711Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16711step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16711step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16711step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw16711step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16711step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16711step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16711step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16711step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16712 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw16712Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16712step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw16712step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16712step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16712step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16712step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16712step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16712step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16712step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16713 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw16713Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16713step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw16713step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16713step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw16713step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16713step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw16713step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16714 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw16714Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16714step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16714step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16714step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16714step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16715 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw16715Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16715step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw16715step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16715step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw16715step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16715step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw16715step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16716 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 1, -2]]
def raw16716Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16716step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![2, -1, -1], ![1, 1, -2]]
def raw16716step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16716step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16716step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16716step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16716step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16716step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16716step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16717 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw16717Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16717step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw16717step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16717step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -2, 3]]
def raw16717step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16717step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw16717step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16717step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw16717step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16718 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw16718Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16718step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw16718step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16718step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw16718step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16718step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw16718step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16719 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw16719Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16719step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16719step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16719step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16719step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16720 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw16720Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16720step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw16720step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16720step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw16720step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16720step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw16720step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16721 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw16721Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16721step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw16721step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16721step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16721step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16721step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16721step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16722 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw16722Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16722step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw16722step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16722step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw16722step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -2, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16723Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16723step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -2, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16723step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16723step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, -2, 3], ![-2, 2, 0]]
def raw16723step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16723step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw16723step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16723step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw16723step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16724 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw16724Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw16724step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16724step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw16724step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16725 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16725Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16725step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16725step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16725step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 2, 0]]
def raw16725step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16725step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw16725step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16725step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw16725step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16726 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw16726Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16726step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![2, -2, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw16726step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16726step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw16726step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16727 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16727Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16727step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16727step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16727step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw16727step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16727step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16727step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16727step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16727step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16727step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16727step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16728 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw16728Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16728step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw16728step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16728step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16728step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16728step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw16728step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16728step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw16728step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16729 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -2, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16729Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -2, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16729step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16729step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, 1, -1], ![-1, 0, 1], ![-2, -1, 3]]
def raw16729step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16729step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw16729step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16729step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw16729step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16730 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16730Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16730step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16730step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16730step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw16730step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16730step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw16730step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16730step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw16730step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16731 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw16731Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16731step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw16731step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16731step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw16731step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16731step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw16731step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16732 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16732Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16732step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16732step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16732step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw16732step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16732step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw16732step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16732step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw16732step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16733 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw16733Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16733step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![2, -2, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw16733step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16733step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw16733step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16733step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw16733step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16733step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw16733step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16734 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw16734Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16734step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw16734step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16734step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16734step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16734step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16734step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16734step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16734step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16735 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw16735Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16735step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw16735step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16735step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16735step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16735step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16735step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16735step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16735step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16736Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16736step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16736step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16737 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16737Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16737step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16737step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16737step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16737step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16737step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16737step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16738 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16738Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16738step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16738step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16738step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16738step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16738step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16738step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16739 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw16739Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16739step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw16739step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16739step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw16739step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw16739step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16739step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw16739step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16739step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16740 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw16740Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16740step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw16740step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw16740step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16740step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw16740step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16740step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16741Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16741step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw16741step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16741step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw16741step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16742 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16742Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16742step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16742step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16742step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16742step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16743Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16743step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16743step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16743step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16743step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16744 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw16744Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16744step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw16744step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16744step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16744step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16744step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16744step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw16745Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16745step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16745step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16745step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16745step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16746Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16746step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16746step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16746step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16746step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16747 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16747Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16747step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16747step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16748 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16748Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16748step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16748step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16749 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw16749Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16749step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw16749step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16749step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16749step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16750 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw16750Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16750step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16750step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16751Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16751step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16751step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16751step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16751step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16752 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16752Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16752step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16752step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16753 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16753Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16753step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16753step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16754 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw16754Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16754step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16754step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw16755Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16755step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16755step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16756Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16756step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw16756step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16756step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw16756step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16757Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16757step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16757step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16758 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16758Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16758step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16758step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16758step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16758step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16758step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16758step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16759 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16759Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16759step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16759step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16759step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16759step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16759step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16759step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw16760Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16760step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw16760step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16760step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16760step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16760step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16760step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw16761Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16761step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-3, 1, 2]]
def raw16761step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16761step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw16761step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16761step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw16761step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw16762Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16762step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw16762step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16762step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16762step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16762step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16762step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw16763Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16763step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16763step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16763step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16763step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16763step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16763step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16764 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw16764Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16764step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16764step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16764step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16764step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16764step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16764step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw16765Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16765step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw16765step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16765step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw16765step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16765step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16765step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16765step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16765step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16766 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16766Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16766step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw16766step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16766step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16766step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16767 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16767Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16767step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16767step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16767step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16767step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical131
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw16768 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16768Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16768step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16768step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16768step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16768step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16769 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw16769Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16769step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw16769step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16769step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw16769step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16769step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16769step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16770 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw16770Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16770step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw16770step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16770step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16770step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16771 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16771Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16771step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw16771step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16772 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16772Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16772step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16772step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16772step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16772step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16773 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16773Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16773step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16773step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16773step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16773step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16774 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw16774Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16774step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw16774step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16774step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw16774step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16774step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16774step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16775 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw16775Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16775step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw16775step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16775step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16775step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16776 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16776Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16776step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16776step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16777 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16777Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16777step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16777step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16778Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16778step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16778step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16779 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw16779Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16779step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw16779step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16779step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw16779step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16779step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16779step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16780 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw16780Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16780step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16780step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16781 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16781Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16781step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16781step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16782 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16782Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16782step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16782step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16783 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16783Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16783step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16783step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw16784Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16784step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16784step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16784step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw16784step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16784step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16784step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16785 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw16785Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16785step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16785step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16786Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16786step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw16786step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16787Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16787step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw16787step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16787step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16787step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16788 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16788Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16788step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16788step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16788step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16788step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16789 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16789Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16789step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16789step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16789step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16789step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16790 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw16790Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16790step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw16790step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16790step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16790step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw16791Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16791step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-3, 1, 2]]
def raw16791step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16791step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw16791step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw16792Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16792step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw16792step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16792step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16792step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw16793Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16793step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16793step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16793step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16793step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16794 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw16794Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16794step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16794step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16794step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16794step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16795 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw16795Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16795step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw16795step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16795step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw16795step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16795step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16795step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16796 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16796Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16796step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw16796step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16796step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16796step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16796step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16796step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16797 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16797Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16797step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16797step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16797step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16797step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16797step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16797step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16798 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16798Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16798step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16798step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16798step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16798step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16798step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16798step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16799 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw16799Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16799step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw16799step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16799step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw16799step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16799step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16799step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16799step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16799step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16800 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw16800Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16800step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw16800step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16800step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16800step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16800step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16800step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16801 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16801Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16801step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16801step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16801step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16801step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16801step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16801step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16802 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16802Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16802step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16802step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16802step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16802step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16802step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16802step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16803Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16803step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16803step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16803step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16803step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16803step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16803step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16804 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw16804Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16804step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw16804step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16804step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16804step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16804step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16804step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16805 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw16805Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16805step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw16805step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16805step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16805step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16805step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16805step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16806 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16806Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16806step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16806step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16806step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16806step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16806step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16806step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16807 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16807Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16807step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16807step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16807step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16807step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16807step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16807step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16808 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16808Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16808step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16808step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16808step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16808step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16808step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16808step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16809 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw16809Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16809step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw16809step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16809step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16809step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16809step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16809step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16809step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16809step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16810 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw16810Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16810step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw16810step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16810step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16810step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16810step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16810step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16811Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16811step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16811step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16811step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16811step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16811step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16811step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16812 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16812Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16812step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16812step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16812step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16812step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16812step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16812step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16813 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16813Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16813step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16813step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16813step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16813step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16813step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16813step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16814 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw16814Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16814step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16814step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16814step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16814step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16814step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16814step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16814step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16814step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16815 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw16815Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16815step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw16815step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16815step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16815step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16815step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16815step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16816 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16816Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16816step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw16816step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16816step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw16816step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16816step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw16816step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16817 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16817Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16817step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16817step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16817step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16817step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16818 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16818Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16818step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw16818step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16818step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw16818step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16819 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16819Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16819step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw16819step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16819step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw16819step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16820 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw16820Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16820step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16820step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16820step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16820step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16821 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw16821Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16821step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw16821step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16821step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw16821step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16822 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw16822Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16822step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16822step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16822step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16822step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16823 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw16823Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16823step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw16823step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16823step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw16823step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16824 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw16824Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16824step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw16824step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16824step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw16824step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16825 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw16825Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16825step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw16825step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16825step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16825step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16825step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16825step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16826 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16826Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16829 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16829Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16829step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16829step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16832 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![0, 0], ![1, -1]]
def raw16832Labels : Fin 2 → Fin 2 := ![0, 1]

def raw16832step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![1, -1]]
def raw16832step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw16832step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw16832step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw16833 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16833Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16833step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16833step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16834 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16834Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16834step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16834step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16835 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16835Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16835step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16835step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16836 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16836Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16836step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16836step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16837 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw16837Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16837step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw16837step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16837step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw16837step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16838 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16838Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16838step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw16838step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16838step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16838step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16838step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16838step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16839 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16839Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16839step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16839step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16839step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16839step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16839step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16839step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16840 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16840Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16840step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16840step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16840step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16840step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16840step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16840step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16841 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16841Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16841step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16841step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16841step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16841step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16842 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16842Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16842step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw16842step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16843 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16843Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16843step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16843step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16843step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16843step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw16843step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16843step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16844 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16844Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16844step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw16844step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16844step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16844step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16844step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16844step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16845 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 3, -1], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16845Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16845step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw16845step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16845step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16845step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16845step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16845step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16846 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16846Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16846step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16846step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16846step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16846step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16846step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16846step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16847 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16847Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16847step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16847step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16847step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16847step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16847step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16847step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16848 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16848Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16848step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16848step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16849 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16849Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16849step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw16849step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16849step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16849step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16849step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16849step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16850 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 3, -1], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16850Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16850step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw16850step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16850step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16850step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16850step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16850step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16851 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16851Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16851step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16851step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16851step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16851step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16851step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16851step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16852 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16852Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16852step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16852step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16852step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16852step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16852step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16852step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16853 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16853Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16853step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16853step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16854 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16854Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16854step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16854step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16854step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16854step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16854step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16854step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16855 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16855Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16855step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw16855step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16855step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16855step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16855step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16855step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16856 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16856Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16856step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16856step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16856step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16856step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw16856step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16856step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16857 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16857Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16857step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16857step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16857step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16857step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw16857step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16857step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16858 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw16858Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16858step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw16858step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw16858step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16858step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw16858step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16858step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16859 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16859Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16859step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw16859step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16859step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw16859step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16859step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw16859step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16860 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16860Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16860step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw16860step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16860step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw16860step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16860step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw16860step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16861 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16861Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16861step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16861step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16861step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16861step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16861step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16861step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16862 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16862Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16862step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16862step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16862step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16862step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16862step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16862step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16863 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw16863Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16863step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16863step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16863step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16863step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16864 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16864Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16864step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw16864step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16865 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16865Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16865step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16865step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16865step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16865step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16865step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw16865step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16866 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16866Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16866step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16866step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16866step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16866step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16866step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw16866step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16867 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16867Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16867step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw16867step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16868 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16868Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16868step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw16868step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16869 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16869Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16869step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16869step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16869step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16869step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16870 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16870Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16870step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16870step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16870step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16870step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16871 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16871Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16871step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16871step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16872 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 3, -1], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16872Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16872step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16872step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16873 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16873Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16873step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16873step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16873step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16873step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16873step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16873step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16874 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16874Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16874step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16874step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16874step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16874step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16875 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16875Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16875step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw16875step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16875step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16875step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16876 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16876Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16876step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16876step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16877 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 3, -1], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16877Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16877step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16877step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16878 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16878Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16878step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16878step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16878step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16878step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16878step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16878step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16879 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16879Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16879step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16879step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16879step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16879step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16880 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16880Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16880step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw16880step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16880step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16880step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16881 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16881Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16881step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16881step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16882 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16882Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16882step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16882step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16883 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16883Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16883step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16883step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16883step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16883step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16884 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16884Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16884step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16884step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16884step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16884step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16885 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw16885Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16885step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw16885step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16886 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16886Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16886step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw16886step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16887 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16887Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16887step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16887step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16888 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16888Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16888step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16888step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16888step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16888step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16888step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16888step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16889 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16889Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16889step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16889step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16889step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16889step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16889step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16889step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16890 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw16890Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16890step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16890step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16890step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16890step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16891 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16891Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16891step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw16891step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16891step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16891step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16891step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16891step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16892 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16892Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16892step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16892step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16892step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16892step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16892step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16892step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16893 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16893Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16893step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16893step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16893step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16893step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16893step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16893step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16894 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16894Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16894step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16894step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16894step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16894step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16895 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16895Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16895step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw16895step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16895step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw16895step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16895step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw16895step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical132
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw16896 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16896Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16896step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16896step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16896step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw16896step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16896step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16896step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16896step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16896step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16897 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16897Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16897step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16897step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16897step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16897step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16898 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 3, -1], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16898Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16898step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw16898step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16898step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16898step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16898step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16898step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16899 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16899Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16899step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16899step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16899step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16899step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16899step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16899step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16900 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16900Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16900step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16900step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16900step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16900step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16901 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16901Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16901step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw16901step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16901step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw16901step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16902 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16902Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16902step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16902step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16902step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16902step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16903 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 3, -1], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16903Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16903step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw16903step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16903step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16903step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16903step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16903step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16904 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16904Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16904step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16904step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16904step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16904step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16904step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16904step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16905 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16905Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16905step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16905step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16905step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16905step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16906 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16906Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16906step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw16906step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16906step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw16906step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16907 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16907Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16907step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![2, -2, 0], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw16907step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16907step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16907step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16907step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16907step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16908 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16908Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16908step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw16908step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16908step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16908step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16908step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16908step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16909 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16909Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16909step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16909step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16909step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw16909step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16909step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16909step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16909step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16909step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16910 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16910Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16910step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16910step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16910step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw16910step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16910step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16910step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16910step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16910step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16911 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw16911Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16911step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw16911step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16911step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16911step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16911step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16911step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16912 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16912Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16912step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw16912step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16912step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw16912step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16912step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw16912step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16913 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16913Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16913step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw16913step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16913step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw16913step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16913step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw16913step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16914 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16914Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16914step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16914step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16914step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 2, 0]]
def raw16914step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16914step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw16914step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16914step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw16914step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16915 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16915Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16915step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16915step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16915step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 2, 0]]
def raw16915step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16915step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw16915step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16915step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw16915step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16916 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw16916Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16916step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw16916step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16916step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw16916step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16916step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw16916step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16917 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16917Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16917step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw16917step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16917step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16917step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16918 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16918Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16918step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw16918step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16918step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16918step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16919 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16919Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16919step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw16919step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16919step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16919step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16920 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16920Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16920step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16920step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16920step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16920step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16921 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16921Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16921step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw16921step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16921step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw16921step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16957Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16957step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw16957step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16958Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16958step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw16958step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![-1, 3, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16959Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16959step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16959step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![0, 0, 0], ![2, -1, -1]]
def raw16960Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16960step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16960step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16960step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16960step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw16961Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16961step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16961step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16962Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16962step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16962step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16963Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16963step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw16963step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 3, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16964Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16964step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16964step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![0, 0, 0], ![2, -1, -1]]
def raw16965Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16965step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16965step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16965step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16965step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw16966Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16966step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16966step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16967Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16967step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw16967step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16968Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16968step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![1, 1, -2]]
def raw16968step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16969 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![-1, 3, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16969Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16969step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16969step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![0, 2, -2], ![0, 0, 0], ![2, -1, -1]]
def raw16970Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16970step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16970step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16970step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16970step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw16971Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16971step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16971step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16972Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16972step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16972step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16973Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16973step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16973step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16974Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16974step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw16974step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16974step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16974step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![0, 0, 0], ![2, -1, -1]]
def raw16975Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16975step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16975step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16975step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16975step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw16976Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16976step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw16976step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw16977Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16977step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw16977step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw16978Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16978step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, 1, -1], ![0, -2, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw16978step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16978step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw16978step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw16979Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16979step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw16979step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16979step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16979step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def raw16980Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16980step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw16980step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![1, 0, -1]]
def raw16981Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16981step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw16981step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16981step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16981step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw16982Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16982step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw16982step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16982step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw16982step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw16983Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16983step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw16983step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16983step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw16983step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw16984Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16984step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw16984step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16984step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16984step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw16985Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16985step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, -2, 3], ![-2, 1, 1]]
def raw16985step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16985step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw16985step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![0, 0, 0], ![3, -2, -1]]
def raw16986Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16986step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw16986step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16986step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw16986step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16986step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16986step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17017Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17017step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw17017step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17017step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw17017step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17020Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17020step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17020step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17023 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![2, -2], ![0, 0], ![1, -1]]
def raw17023Labels : Fin 2 → Fin 2 := ![0, 1]

def raw17023step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![2, -2], ![1, -1]]
def raw17023step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw17023step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw17023step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw17023step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw17023step2Labels : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical133
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw17024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17024Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17024step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0]]
def raw17024step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17024step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0]]
def raw17024step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17025Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17025step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw17025step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17025step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw17025step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17026Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17026step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17026step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17026step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17026step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw17027Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17027step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 2, 0]]
def raw17027step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17027step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0]]
def raw17027step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17028 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw17028Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17028step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17028step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17028step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17028step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17029 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17029Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17029step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17029step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17029step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17029step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17030 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-2, 2, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17030Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17030step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw17030step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17030step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17030step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17031 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17031Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17031step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17031step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17031step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17031step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17032 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw17032Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17032step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw17032step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17032step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17032step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17033 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17033Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17033step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17033step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17033step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw17033step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17034 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-2, 2, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17034Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17034step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17034step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17034step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17034step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17035 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw17035Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17035step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17035step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17035step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17035step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17035step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17035step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17036 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17036Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17036step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17036step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17037 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw17037Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17037step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw17037step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17037step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw17037step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17037step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17037step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17037step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17037step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17038 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17038Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17038step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17038step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17038step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17038step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17039 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17039Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17039step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17039step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17039step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17039step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17040 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17040Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17040step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17040step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17040step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17040step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17041 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-2, 2, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17041Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17041step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw17041step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17041step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17041step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17041step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17041step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17042 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![3, -3, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw17042Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17042step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17042step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17042step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17042step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17042step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17042step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17043 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17043Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17043step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw17043step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17043step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17043step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17043step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17043step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17044 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17044Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17044step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw17044step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17044step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17044step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17044step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17044step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17045 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17045Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17045step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17045step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17045step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17045step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17046 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-2, 2, 0], ![2, -2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17046Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17046step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17046step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17046step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17046step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17047 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17047Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17047step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17047step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17047step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17047step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17048 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw17048Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17048step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17048step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17049 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17049Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17049step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw17049step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17049step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw17049step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17050 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17050Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17050step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17050step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17050step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17050step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17051 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-2, 2, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17051Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17051step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17051step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17051step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17051step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17052 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17052Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17052step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17052step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17052step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17052step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17052step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17052step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17053 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17053Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17053step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17053step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17053step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17053step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17054 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17054Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17054step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17054step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17054step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17054step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17055 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-2, 2, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17055Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17055step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw17055step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17055step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17055step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17056 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17056Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17056step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw17056step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17056step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17056step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17057 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw17057Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17057step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17057step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17057step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17057step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17058 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17058Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17058step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw17058step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17058step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17058step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17059 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-2, 2, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17059Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17059step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17059step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17060 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw17060Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17060step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17060step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17060step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17060step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17061 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17061Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17061step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw17061step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17061step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17061step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17062 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17062Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17062step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17062step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17062step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17062step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17063 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw17063Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17063step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw17063step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17063step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw17063step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17063step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17063step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17064 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17064Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17064step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17064step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17064step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw17064step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17064step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw17064step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17065 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17065Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17065step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw17065step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17065step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw17065step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17066 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17066Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17066step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17066step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17066step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17066step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17067 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-2, 2, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17067Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17067step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw17067step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17067step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17067step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17068 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![3, -3, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw17068Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17068step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17068step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17068step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17068step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17069 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17069Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17069step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw17069step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17069step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17069step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17070 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17070Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17070step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw17070step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17071 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17071Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17071step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw17071step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17071step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17071step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17072 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-2, 2, 0], ![2, -2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17072Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17072step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17072step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17073 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17073Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17073step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17073step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17074 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw17074Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17074step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw17074step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17074step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17074step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17075 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17075Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17075step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw17075step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17076 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17076Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17076step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17076step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17076step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17076step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17077 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-2, 2, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17077Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17077step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw17077step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17077step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw17077step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17078 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17078Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17078step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17078step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17078step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17078step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17079 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17079Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17079step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17079step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17079step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17079step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17086 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17086Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17086step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17086step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17086step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17086step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17087 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17087Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17087step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw17087step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17087step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17087step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17087step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17087step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17088 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17088Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17088step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17088step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17088step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw17088step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17088step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17088step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17088step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17088step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17089 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw17089Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17089step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw17089step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17089step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1]]
def raw17089step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17089step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw17089step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17089step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17089step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17090 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17090Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17090step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17090step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17090step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17090step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17091 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17091Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17091step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17091step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17091step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17091step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17092 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw17092Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17092step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw17092step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17092step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17092step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17093 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17093Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17093step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17093step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17093step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17093step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17094 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17094Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17094step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17094step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17095 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw17095Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17095step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17095step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17095step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17095step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17096 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17096Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17096step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17096step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17096step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw17096step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17096step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw17096step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17096step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw17096step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17097 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17097Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17097step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17097step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17097step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17097step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17097step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17097step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17098 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17098Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17098step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17098step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17098step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw17098step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17098step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17098step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17098step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17098step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17099 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw17099Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17099step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw17099step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17099step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw17099step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17099step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw17099step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17099step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw17099step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17100 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw17100Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17100step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17100step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17100step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17100step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17100step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17100step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17101 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw17101Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17101step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw17101step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17101step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw17101step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17101step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17101step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17101step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17101step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17102 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw17102Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17102step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw17102step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17102step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![3, -2, -1]]
def raw17102step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17102step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17102step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17102step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17102step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17102step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17102step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17103 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17103Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17103step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17103step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17103step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17103step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17103step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17103step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17104Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17104step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw17104step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17104step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17104step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17105Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17105step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17105step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17105step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw17105step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17105step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17105step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17106 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw17106Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17106step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw17106step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17106step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1]]
def raw17106step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17106step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0]]
def raw17106step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17106step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw17106step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17107 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17107Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17107step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17107step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17108Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17108step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17108step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17109 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw17109Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17109step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw17109step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17109step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17109step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17109step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17109step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17110 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17110Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17110step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17110step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17110step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17110step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17111 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17111Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17111step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17111step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw17112Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17112step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17112step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17112step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17112step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17112step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw17112step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17113 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17113Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17113step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17113step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17113step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw17113step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17113step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw17113step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17114Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17114step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17114step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17114step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17114step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17115 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17115Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17115step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17115step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17115step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw17115step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17115step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17115step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17116 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw17116Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17116step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw17116step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17116step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw17116step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17116step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw17116step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17117 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw17117Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17117step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17117step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17117step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17117step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17118 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw17118Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17118step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw17118step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17118step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw17118step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17118step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17118step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17119 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw17119Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17119step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw17119step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17119step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![3, -2, -1]]
def raw17119step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17119step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17119step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17119step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17119step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17120 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17120Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17120step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17120step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17120step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw17120step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17120step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17120step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17120step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17120step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17121 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw17121Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17121step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw17121step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17121step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17121step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17121step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17121step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17122 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17122Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17122step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17122step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17122step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17122step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17123 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17123Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17123step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17123step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17123step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17123step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17124 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17124Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17124step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw17124step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17124step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw17124step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17124step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw17124step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17125 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17125Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17125step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17125step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17125step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2]]
def raw17125step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17125step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17125step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17125step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17125step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17126 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17126Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17126step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17126step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17126step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 0, 1], ![0, -2, 2]]
def raw17126step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17126step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17126step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17126step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17126step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17126step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17126step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17127 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17127Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17127step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17127step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17127step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17127step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17127step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17127step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17132 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw17132Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17132step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw17132step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17132step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw17132step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17136 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw17136Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17136step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw17136step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17136step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw17136step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical134
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw17178 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw17178Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17178step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw17178step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17178step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17178step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17178step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17178step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17179 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17179Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17179step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw17179step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17179step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17179step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17180 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17180Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17180step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw17180step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17180step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17180step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17181 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17181Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17181step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw17181step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17181step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17181step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17182 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw17182Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17182step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17182step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17182step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17182step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17183 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17183Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17183step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17183step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17183step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17183step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17184 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17184Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17184step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17184step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17184step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw17184step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17184step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw17184step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17185 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17185Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17185step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17185step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17185step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17185step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17186 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17186Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17186step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17186step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17186step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17186step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17187 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw17187Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17187step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17187step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17187step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17187step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17188 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17188Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17188step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17188step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17188step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17188step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17189 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17189Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17189step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17189step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17189step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17189step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17190 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17190Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17190step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17190step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17190step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17190step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17191 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![0, 1, -1], ![2, 0, -2]]
def raw17191Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17191step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17191step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17191step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17191step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17192 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17192Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17192step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17192step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17192step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17192step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17193 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw17193Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17193step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw17193step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17193step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17193step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17194 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw17194Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17194step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17194step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17194step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17194step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17195 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw17195Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17195step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17195step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17195step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17195step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17196 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![1, 1, -2]]
def raw17196Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17196step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17196step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17196step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17196step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17197 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw17197Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17197step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw17197step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17197step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17197step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17198 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw17198Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17198step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17198step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17198step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17198step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17199 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw17199Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17199step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17199step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17199step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17199step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw17200Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17200step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17200step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17200step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17200step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17201Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17201step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17201step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17201step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17201step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17202Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17202step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17202step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17202step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17202step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17203 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17203Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17203step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17203step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17203step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17203step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17204 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw17204Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17204step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17204step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17204step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17204step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17205 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17205Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17205step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17205step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17205step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17205step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17206 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17206Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17206step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17206step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17206step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0]]
def raw17206step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17206step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw17206step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17206step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw17206step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17207 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17207Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17207step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw17207step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17207step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17207step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17207step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17207step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17208 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17208Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17208step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17208step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17208step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17208step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17209 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw17209Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17209step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17209step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17209step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17209step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17210 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17210Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17210step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17210step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17210step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17210step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17211 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17211Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17211step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw17211step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17211step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17211step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17211step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17211step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17212 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17212Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17212step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17212step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17212step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17212step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17213 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![0, 1, -1], ![2, 0, -2]]
def raw17213Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17213step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17213step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17213step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17213step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17214 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17214Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17214step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17214step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17214step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17214step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17215 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw17215Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17215step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw17215step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17215step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17215step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17215step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17215step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17216 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw17216Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17216step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17216step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17216step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17216step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17217 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw17217Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17217step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17217step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17217step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17217step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17218 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![1, 1, -2]]
def raw17218Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17218step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17218step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17218step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17218step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17219 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw17219Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17219step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17219step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17219step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17219step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17220 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw17220Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17220step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17220step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17220step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17220step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw17221Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17221step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17221step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17221step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17221step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17222 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw17222Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17222step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17222step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17222step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17222step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17223 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17223Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17223step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17223step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17223step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17223step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17224 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw17224Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17224step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17224step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17225 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw17225Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17225step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17225step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17226 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17226Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17226step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17226step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17226step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17226step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17227 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw17227Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17227step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17227step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17228 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw17228Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17228step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17228step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17229 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw17229Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17229step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17229step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17230 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw17230Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17230step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17230step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17231 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw17231Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17231step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw17231step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17231step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17231step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17231step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17231step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17231step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17231step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17232 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw17232Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17232step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17232step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17233 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17233Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17233step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17233step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17233step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw17233step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17233step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17233step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17233step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17233step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17234 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17234Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17234step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17234step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17234step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw17234step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17234step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17234step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17234step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17234step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17235 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw17235Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17235step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw17235step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17235step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17235step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17235step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17235step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17236 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw17236Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17236step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw17236step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17236step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17236step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17236step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17236step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17237 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17237Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17237step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17237step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17237step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw17237step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17237step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17237step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17237step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17237step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17238 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw17238Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17238step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw17238step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17238step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17238step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17238step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17238step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17239 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw17239Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17239step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw17239step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17239step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17239step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17239step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17239step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17240 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17240Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17240step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17240step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17240step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw17240step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17240step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17240step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17240step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17240step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17241 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw17241Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17241step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw17241step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17241step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17241step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17241step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17241step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17242 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw17242Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17242step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw17242step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17242step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17242step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17242step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17242step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17243 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw17243Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17243step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw17243step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17243step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17243step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17243step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17243step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17243step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17243step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17244 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw17244Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17244step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw17244step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17244step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17244step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17244step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17244step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17244step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17244step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17245 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw17245Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17245step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17245step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17245step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17245step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17245step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17245step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17246 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17246Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17246step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw17246step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17246step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17246step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17246step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17246step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17247 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17247Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17247step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17247step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17247step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17247step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17247step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17247step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17248Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17248step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17248step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17248step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw17248step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17248step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17248step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17249 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17249Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17249step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17249step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17249step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17249step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw17250Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17250step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw17250step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17250step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17250step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17250step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17250step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17251 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw17251Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17251step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw17251step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17251step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17251step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17251step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17251step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17252 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17252Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17252step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17252step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17252step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17252step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17252step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17252step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17253 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17253Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17253step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17253step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17253step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw17253step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17253step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17253step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17254 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17254Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17254step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17254step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17254step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17254step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17255 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw17255Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17255step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw17255step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17255step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17255step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17255step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17255step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17256 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw17256Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17256step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw17256step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17256step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17256step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17256step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17256step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17257 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17257Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17257step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17257step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17257step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17257step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17257step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17257step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17258 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17258Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17258step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17258step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17258step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw17258step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17258step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw17258step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17259 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17259Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17259step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17259step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17259step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17259step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17260 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw17260Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17260step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw17260step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17260step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17260step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17260step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17260step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17261 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw17261Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17261step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw17261step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17261step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17261step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17262 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17262Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17262step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17262step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17262step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17262step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17263 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17263Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17263step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![0, 1, -1], ![-2, 1, 1], ![-2, 1, 1]]
def raw17263step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17263step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw17263step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17264 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17264Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17264step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17264step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17264step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17264step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17265 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw17265Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17265step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17265step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17265step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17265step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17266 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw17266Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17266step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17266step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17267 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw17267Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17267step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw17267step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17267step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw17267step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17267step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw17267step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17268 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw17268Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17268step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw17268step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17268step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw17268step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17268step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw17268step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17269 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw17269Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17269step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw17269step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17269step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17269step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17269step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17269step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17270 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw17270Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17270step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17270step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17270step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17270step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17271 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw17271Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17271step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![1, 1, -2]]
def raw17271step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17271step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17271step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17271step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17271step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17272 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw17272Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17272step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw17272step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17272step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw17272step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17272step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw17272step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17273 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw17273Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17273step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw17273step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17273step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-2, 1, 1], ![-2, 1, 1]]
def raw17273step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17273step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw17273step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17274 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw17274Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17274step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![3, -1, -2]]
def raw17274step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17274step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17274step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17274step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17274step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17275 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw17275Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17275step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17275step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17275step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17275step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17276 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw17276Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17276step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![3, -1, -2]]
def raw17276step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17276step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17276step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17276step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17276step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17277 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17277Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17277step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17277step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17277step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17277step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17277step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17277step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17278 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17278Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17278step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17278step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17278step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17278step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17278step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17278step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17279 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17279Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17279step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17279step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17279step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17279step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical135
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw17280 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw17280Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17280step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw17280step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17280step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17280step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17280step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17280step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17281 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw17281Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17281step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw17281step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17281step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17281step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17281step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17281step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17282 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17282Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17282step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17282step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17282step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw17282step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17282step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17282step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17282step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17282step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17283 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17283Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17283step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17283step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17283step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17283step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17283step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17283step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17284 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17284Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17284step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17284step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17284step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17284step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17285 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw17285Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17285step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw17285step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17285step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17285step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17285step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17285step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17286 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw17286Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17286step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw17286step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17286step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17286step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17286step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17286step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17287 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17287Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17287step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17287step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17287step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-2, 1, 1]]
def raw17287step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17287step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]
def raw17287step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17287step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]
def raw17287step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17288 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17288Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17288step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17288step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17288step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw17288step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17288step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw17288step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17289 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17289Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17289step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17289step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17289step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17289step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17290 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw17290Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17290step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw17290step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17290step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17290step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17290step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17290step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17291 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw17291Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17291step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw17291step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17291step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17291step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17291step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17291step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17292 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17292Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17292step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw17292step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17292step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw17292step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17292step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw17292step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17293 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17293Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17293step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw17293step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17293step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw17293step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17294 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17294Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17294step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17294step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17294step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17294step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17295 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw17295Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17295step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17295step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17295step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17295step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17296 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw17296Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17296step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17296step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17296step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17296step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17297 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw17297Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17297step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw17297step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17297step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw17297step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17297step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw17297step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17298 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw17298Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17298step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw17298step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17298step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw17298step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17298step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw17298step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17299 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw17299Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17299step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw17299step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17299step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17299step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17299step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17299step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17300 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw17300Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17300step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17300step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17300step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17300step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17301 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw17301Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17301step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![1, 1, -2]]
def raw17301step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17301step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17301step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17301step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17301step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17302 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw17302Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17302step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw17302step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17302step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -2, 3], ![-2, 1, 1]]
def raw17302step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17302step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw17302step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17302step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw17302step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17303 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw17303Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17303step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw17303step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17303step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw17303step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17303step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw17303step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17304 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw17304Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17304step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![3, -1, -2]]
def raw17304step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17304step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17304step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17304step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17304step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17305 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw17305Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17305step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17305step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17305step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17305step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17306 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw17306Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17306step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![3, -1, -2]]
def raw17306step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17306step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17306step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17306step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17306step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17307 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17307Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17307step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17307step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17307step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17307step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17307step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17307step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17308 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17308Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17308step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17308step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17308step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17308step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17308step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17308step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17309 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17309Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17309step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17309step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17309step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw17309step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17309step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw17309step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17310 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17310Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17310step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![0, 1, -1], ![-2, 1, 1], ![-2, 1, 1]]
def raw17310step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17310step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw17310step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17311 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw17311Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17311step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw17311step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17311step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 2, -2], ![1, -2, 1], ![1, -2, 1], ![1, 0, -1]]
def raw17311step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17312 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw17312Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17312step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw17312step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17312step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-2, 1, 1], ![-2, 1, 1]]
def raw17312step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17312step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw17312step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17313 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![0, 0], ![-1, 1], ![2, -2]]
def raw17313Labels : Fin 2 → Fin 2 := ![0, 1]

def raw17313step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![-1, 1], ![2, -2]]
def raw17313step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw17313step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw17313step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw17313step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw17313step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw17314 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17314Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17314step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw17314step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17314step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17314step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17314step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17314step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17315 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17315Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17315step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw17315step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17315step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw17315step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17315step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17315step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17315step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17315step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17316 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17316Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17316step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17316step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17316step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17316step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17317 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw17317Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17317step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0]]
def raw17317step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17317step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw17317step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17317step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17317step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17317step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17317step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17318 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw17318Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17318step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0]]
def raw17318step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17318step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw17318step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17318step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw17318step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17319 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17319Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17319step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw17319step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17319step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw17319step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17319step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17319step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17319step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17319step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17320 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17320Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17320step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw17320step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17320step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw17320step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17320step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17320step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17320step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17320step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17320step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17320step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17321 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17321Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17321step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17321step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17321step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17321step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17321step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17321step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw17322Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17322step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0]]
def raw17322step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17322step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0]]
def raw17322step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17322step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17322step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17322step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17322step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17323 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw17323Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17323step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0]]
def raw17323step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17323step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0]]
def raw17323step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17323step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17323step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17324 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17324Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17324step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def raw17324step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17324step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw17324step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17324step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw17324step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17325 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17325Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17325step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def raw17325step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17325step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw17325step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17325step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw17325step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17326 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17326Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17326step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw17326step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17326step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw17326step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17327 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw17327Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17327step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 2, -2], ![2, -2, 0]]
def raw17327step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17327step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17327step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17327step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17327step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17328 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw17328Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17328step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![1, -1, 0]]
def raw17328step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17328step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17328step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17328step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17328step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17329 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17329Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17329step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17329step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17329step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17329step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17330 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17330Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17330step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17330step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17330step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17330step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17331 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17331Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17331step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17331step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17331step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17331step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17331step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17331step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17332 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw17332Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17332step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17332step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17332step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17332step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17333 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw17333Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17333step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17333step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17333step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17333step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17334 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw17334Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17334step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -2, 0]]
def raw17334step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17334step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw17334step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17334step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw17334step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17335 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw17335Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17335step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![2, -2, 0]]
def raw17335step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17335step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw17335step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17335step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw17335step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17336 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw17336Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17336step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -2, 0]]
def raw17336step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17336step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17336step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17336step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17336step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17337 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw17337Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17337step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17337step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17337step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17337step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17337step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17337step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17338 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw17338Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17338step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![1, -1, 0]]
def raw17338step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17338step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17338step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17338step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17338step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17339 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw17339Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17339step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -3, 0]]
def raw17339step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17339step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw17339step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17339step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw17339step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17340 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw17340Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17340step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, 1, -2], ![3, -3, 0]]
def raw17340step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17340step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw17340step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17340step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw17340step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17341 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw17341Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17341step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, 1, -2], ![3, -3, 0]]
def raw17341step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17341step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17341step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17341step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17341step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17341step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17341step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17342 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw17342Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17342step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw17342step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17342step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw17342step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17343 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw17343Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17343step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![3, -3, 0]]
def raw17343step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17343step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17343step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17343step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17343step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17344 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17344Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17344step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw17344step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17344step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17344step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17345 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17345Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17345step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw17345step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17345step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw17345step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17345step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17345step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17346 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17346Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17346step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw17346step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17346step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17346step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17347 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw17347Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17347step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0]]
def raw17347step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17347step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1]]
def raw17347step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17347step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw17347step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17348 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw17348Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17348step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0]]
def raw17348step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17348step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw17348step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17349 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17349Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17349step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw17349step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17349step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw17349step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17349step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17349step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17350 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17350Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17350step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw17350step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17350step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw17350step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17350step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17350step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17350step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17350step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17351 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17351Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17351step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17351step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17351step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17351step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17351step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17351step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17352 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw17352Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17352step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0]]
def raw17352step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17352step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0]]
def raw17352step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17352step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -2, 2], ![-2, 1, 1]]
def raw17352step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17352step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw17352step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17353 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw17353Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17353step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0]]
def raw17353step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17353step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0]]
def raw17353step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17353step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw17353step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17354 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17354Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17354step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def raw17354step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17354step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw17354step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17355 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17355Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17355step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def raw17355step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17355step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw17355step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17356 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17356Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17356step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17356step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17356step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17356step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17357 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw17357Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17357step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 2, -2], ![2, -2, 0]]
def raw17357step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17357step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw17357step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17357step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw17357step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17358 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw17358Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17358step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![1, -1, 0]]
def raw17358step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17358step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17358step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17359 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17359Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17359step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17359step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17360 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17360Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17360step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17360step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17361 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17361Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17361step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17361step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17361step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17361step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17362 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw17362Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17362step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw17362step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17362step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw17362step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17363 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw17363Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17363step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17363step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17364 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw17364Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17364step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -2, 0]]
def raw17364step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17364step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw17364step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17365 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw17365Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17365step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![2, -2, 0]]
def raw17365step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17365step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw17365step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17366 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw17366Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17366step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -2, 0]]
def raw17366step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17366step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17366step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17366step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17366step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17367 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw17367Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17367step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17367step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17367step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17367step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17368 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw17368Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17368step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![1, -1, 0]]
def raw17368step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17368step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17368step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17369 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw17369Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17369step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -3, 0]]
def raw17369step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17369step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-3, 1, 2]]
def raw17369step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17369step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw17369step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17370 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw17370Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17370step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, 1, -2], ![3, -3, 0]]
def raw17370step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17370step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw17370step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17370step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw17370step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17371 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw17371Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17371step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, 1, -2], ![3, -3, 0]]
def raw17371step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17371step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17371step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17371step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17371step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17372 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw17372Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17372step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17372step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17372step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17372step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17373 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw17373Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17373step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![3, -3, 0]]
def raw17373step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17373step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw17373step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17373step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw17373step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17374 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17374Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17374step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17374step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17374step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw17374step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17374step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw17374step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17375 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17375Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17375step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17375step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17375step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-2, 1, 1], ![0, -2, 2]]
def raw17375step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17375step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17375step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17375step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17375step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17376 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17376Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17376step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17376step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17376step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17376step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17377 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw17377Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17377step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw17377step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17377step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw17377step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17377step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw17377step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17378 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw17378Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17378step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw17378step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17378step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17378step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17378step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17378step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17379 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17379Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17379step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17379step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17379step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-2, 1, 1], ![0, -2, 2]]
def raw17379step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17379step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17379step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17379step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17379step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17379step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17379step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17380 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17380Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17380step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17380step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17380step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17380step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17381 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw17381Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17381step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw17381step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17381step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw17381step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17381step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw17381step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17382 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17382Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17382step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![2, -2, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17382step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17382step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17382step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17382step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17382step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17383 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, -2, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17383Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17383step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, -2, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17383step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17383step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17383step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17383step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17383step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17384 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17384Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17384step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17384step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17384step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17384step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17385 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw17385Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17385step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw17385step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17385step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw17385step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17385step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw17385step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17386 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw17386Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17386step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw17386step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17386step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw17386step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17386step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17386step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17386step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17386step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17387 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw17387Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17387step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17387step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17387step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17387step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17388 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17388Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17388step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17388step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17388step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw17388step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17388step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17388step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17388step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17388step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17389 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17389Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17389step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17389step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17389step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17389step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17389step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17389step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17390 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw17390Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17390step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw17390step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17390step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17390step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17390step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17390step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17391 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw17391Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17391step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw17391step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17391step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17391step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17391step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17391step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17392 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw17392Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17392step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw17392step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17392step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-2, 1, 1], ![1, -3, 2]]
def raw17392step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17392step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17392step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17392step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17392step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17393 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw17393Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17393step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17393step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17393step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17393step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17394 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-3, 2, 1], ![1, -3, 2]]
def raw17394Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17394step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-3, 2, 1], ![1, -3, 2]]
def raw17394step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17394step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw17394step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17394step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw17394step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17395 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17395Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17395step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17395step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17395step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw17395step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17395step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw17395step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17396 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17396Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17396step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17396step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17396step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-2, 1, 1], ![0, -2, 2]]
def raw17396step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17396step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw17396step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17396step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17396step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17397 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17397Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17397step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw17397step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17397step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17397step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17398 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw17398Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17398step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw17398step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17398step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw17398step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17399 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw17399Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17399step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw17399step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17399step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw17399step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17400 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17400Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17400step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17400step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17400step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-2, 1, 1], ![0, -2, 2]]
def raw17400step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17400step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17400step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17400step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17400step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17401 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17401Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17401step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17401step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17401step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17401step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17402 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw17402Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17402step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw17402step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17402step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw17402step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17403 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17403Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17403step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![2, -2, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17403step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17403step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw17403step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17404 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, -2, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17404Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17404step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, -2, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17404step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17404step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 2, -2], ![-1, -1, 2], ![-2, 1, 1]]
def raw17404step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17404step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw17404step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17405 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17405Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17405step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17405step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17405step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17405step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17406 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw17406Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17406step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw17406step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17406step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw17406step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17407 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw17407Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17407step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw17407step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17407step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw17407step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17407step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17407step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical136
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw17408 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17408Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17408step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17408step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17408step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17408step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17408step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17408step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17409 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw17409Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17409step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17409step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17410 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17410Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17410step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17410step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17410step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17410step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17411 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17411Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17411step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17411step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17411step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 0, 1], ![0, -2, 2]]
def raw17411step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17411step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17411step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17411step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17411step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17412 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17412Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17412step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17412step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17412step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17412step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17413 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw17413Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17413step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw17413step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17413step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw17413step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17413step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17413step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17414 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw17414Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17414step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw17414step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17414step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17414step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17414step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17414step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17415 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw17415Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17415step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw17415step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17415step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-2, 1, 1], ![1, -3, 2]]
def raw17415step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17415step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17415step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17415step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17415step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17416 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw17416Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17416step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17416step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17416step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17416step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17417 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-3, 2, 1], ![1, -3, 2]]
def raw17417Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17417step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-3, 2, 1], ![1, -3, 2]]
def raw17417step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17417step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw17417step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17418 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17418Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17418step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17418step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17418step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17418step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17418step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17418step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17419 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17419Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17419step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17419step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17420 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17420Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17420step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17420step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17420step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17420step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17420step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17420step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17421 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw17421Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17421step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw17421step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17421step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw17421step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17422 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17422Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17422step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17422step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17422step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17422step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17423 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17423Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17423step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17423step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17423step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17423step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17424 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17424Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17424step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17424step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17424step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17424step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17425 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw17425Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17425step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw17425step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17425step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17425step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17425step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17425step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17425step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17425step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17426 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17426Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17426step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17426step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17426step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17426step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17427 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17427Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17427step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17427step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17427step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17427step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17428Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17428step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17428step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17429 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw17429Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17429step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17429step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17429step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17429step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17429step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17429step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17430 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17430Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17430step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17430step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17430step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17430step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17431 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17431Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17431step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17431step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17431step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17431step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17432 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17432Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17432step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17432step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17432step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17432step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17432step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17432step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17433 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17433Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17433step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17433step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17433step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17433step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17433step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17433step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17434 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw17434Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17434step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw17434step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17434step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw17434step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17435 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw17435Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17435step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw17435step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17435step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17435step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17435step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17435step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17436 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw17436Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17436step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17436step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17436step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17436step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17436step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17436step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17437 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw17437Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17437step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17437step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17437step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17437step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17437step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17437step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17438 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw17438Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17438step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw17438step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17438step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17438step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17438step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17438step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17438step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17438step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17439 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17439Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17439step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17439step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17440 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17440Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17440step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw17440step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17440step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17440step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17441 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17441Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17441step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17441step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17441step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17441step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17442 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw17442Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17442step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw17442step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17442step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw17442step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17442step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw17442step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17443 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw17443Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17443step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw17443step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17444 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17444Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17444step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17444step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17444step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17444step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17445 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17445Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17445step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17445step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17445step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17445step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17445step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17445step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17446 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17446Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17446step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17446step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17446step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17446step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17447 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw17447Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17447step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw17447step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17447step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw17447step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17447step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw17447step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17448 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw17448Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17448step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw17448step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17448step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw17448step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17449 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17449Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17449step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17449step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17450 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17450Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17450step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17450step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17451 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17451Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17451step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17451step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17452 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw17452Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17452step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw17452step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17452step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17452step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17452step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17452step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17453 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw17453Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17453step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17453step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17454 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17454Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17454step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17454step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17455 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17455Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17455step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17455step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17456 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17456Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17456step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17456step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17457 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw17457Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17457step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17457step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17457step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17457step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw17458Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17458step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17458step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17459Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17459step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17459step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17460Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17460step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17460step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17461 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17461Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17461step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17461step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17461step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17461step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17462Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17462step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17462step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17462step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17462step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw17463Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17463step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17463step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17463step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17463step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw17464Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17464step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw17464step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17465 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw17465Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17465step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw17465step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17465step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17465step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17466 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw17466Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17466step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17466step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17466step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17466step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw17467Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17467step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17467step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17467step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17467step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17468 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw17468Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17468step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw17468step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17468step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17468step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17468step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17468step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17469 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17469Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17469step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw17469step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17469step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17469step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17470 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17470Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17470step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17470step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17470step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17470step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17470step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17470step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17471 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17471Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17471step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw17471step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17471step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17471step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17472 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17472Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17472step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17472step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17472step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17472step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17473 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw17473Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17473step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17473step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17474 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17474Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17474step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17474step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17474step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17474step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17475 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17475Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17475step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17475step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17475step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17475step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17475step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17475step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17475step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17475step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17476 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17476Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17476step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw17476step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17476step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw17476step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17477 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17477Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17477step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17477step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17477step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17477step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17478 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw17478Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17478step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17478step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17478step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17478step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17478step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17478step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17479 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17479Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17479step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw17479step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17479step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17479step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17479step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17479step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17480 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17480Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17480step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17480step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17480step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17480step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17481 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17481Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17481step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17481step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17481step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17481step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17482 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17482Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17482step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw17482step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17482step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw17482step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17482step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw17482step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17483 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw17483Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17483step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17483step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17484 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17484Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17484step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17484step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17484step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17484step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17484step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17484step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17485 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17485Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17485step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw17485step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17485step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17485step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17485step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17485step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17486 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17486Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17486step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17486step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17486step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17486step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17487 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17487Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17487step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17487step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17487step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17487step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17487step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17487step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17487step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17487step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17488 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-2, 2, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17488Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17488step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17488step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17488step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17488step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17488step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17488step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17489 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw17489Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17489step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17489step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17490 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17490Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17490step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw17490step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17490step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw17490step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17491 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17491Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17491step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17491step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17491step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17491step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17492 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17492Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17492step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17492step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17492step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17492step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17492step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17492step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17492step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17492step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17493 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17493Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17493step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17493step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17493step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17493step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17494 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17494Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17494step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw17494step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17494step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17494step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17495 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17495Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17495step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17495step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17495step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw17495step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17495step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17495step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17496 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17496Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17496step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17496step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17497 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17497Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17497step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw17497step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17497step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17497step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17498 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw17498Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17498step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17498step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17499 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17499Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17499step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17499step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17500 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17500Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17500step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17500step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17500step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17500step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17500step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17500step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17501 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17501Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17501step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw17501step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17502 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17502Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17502step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17502step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17503 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw17503Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17503step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17503step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17504 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17504Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17504step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw17504step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17505 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17505Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17505step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw17505step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17505step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17505step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17506 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17506Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17506step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17506step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17507 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17507Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17507step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw17507step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17507step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw17507step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17508 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw17508Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17508step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw17508step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17508step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17508step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17509 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17509Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17509step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17509step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17509step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17509step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17510 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17510Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17510step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17510step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17510step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2]]
def raw17510step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17510step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17510step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17511 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw17511Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17511step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw17511step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17511step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17511step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17512 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17512Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17512step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17512step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17513 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17513Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17513step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17513step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17514 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17514Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17514step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17514step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17514step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17514step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17514step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17514step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17515 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-2, 2, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17515Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17515step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17515step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17516 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw17516Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17516step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17516step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17517 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17517Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17517step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw17517step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17518 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17518Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17518step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17518step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17518step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17518step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17519 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17519Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17519step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17519step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17519step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17519step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17519step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17519step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17520 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17520Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17520step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw17520step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17520step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw17520step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17521 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17521Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17521step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17521step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17521step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17521step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17522 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17522Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17522step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw17522step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17522step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17522step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17523 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17523Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17523step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw17523step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17523step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw17523step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17524 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw17524Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17524step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw17524step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17524step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17524step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17524step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17524step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17525Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17525step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17525step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17525step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17525step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17526Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17526step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17526step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17526step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17526step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17527 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17527Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17527step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw17527step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17527step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17527step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17528 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17528Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17528step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17528step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17528step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17528step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17529 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw17529Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17529step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw17529step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17529step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17529step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17529step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17529step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17530Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17530step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17530step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17530step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17530step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17531 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17531Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17531step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17531step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17531step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17531step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17532 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17532Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17532step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw17532step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17532step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw17532step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17533 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17533Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17533step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17533step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17533step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17533step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17534 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw17534Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17534step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw17534step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17534step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17534step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17534step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17534step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17535 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17535Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17535step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17535step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

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

def raw17536 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17536Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17536step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17536step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17536step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17536step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17537 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17537Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17537step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![0, 1, -1], ![-2, 1, 1], ![-2, 1, 1]]
def raw17537step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17537step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw17537step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17538 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17538Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17538step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17538step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17538step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17538step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17539 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![2, 0, -2]]
def raw17539Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17539step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17539step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17539step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17539step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17539step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17539step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17540Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17541 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw17541Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17541step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw17541step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17541step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw17541step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw17542Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17542step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw17542step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17542step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw17542step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17543 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw17543Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17543step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw17543step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17543step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17543step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17543step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17543step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17544 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw17544Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17544step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17544step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17544step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17544step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17545 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw17545Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17545step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17545step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17545step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17545step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17546 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw17546Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17546step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw17546step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17546step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw17546step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17547 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw17547Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17547step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw17547step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17547step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw17547step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17548 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw17548Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17548step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17548step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17548step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17548step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17549 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw17549Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17549step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17549step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17549step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17549step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17550 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![0, 0, 0], ![3, -1, -2]]
def raw17550Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17550step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![3, -1, -2]]
def raw17550step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17550step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17550step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17550step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17550step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17551 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17551Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17551step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17551step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17551step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17551step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17552 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17552Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17552step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17552step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17552step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17552step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17553 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17553Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17553step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw17553step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17553step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw17553step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17554 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw17554Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17554step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw17554step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17554step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17554step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17554step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17554step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17555 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17555Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17555step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17555step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17555step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17555step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17556 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17556Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17556step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw17556step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17556step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17556step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17556step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17556step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17557 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17557Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17557step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17557step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17557step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17557step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17558 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17558Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17558step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17558step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17558step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17558step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17559 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw17559Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17559step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw17559step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17559step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17559step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17559step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17559step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17560 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17560Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17560step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17560step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17560step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17560step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17561 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17561Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17561step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1]]
def raw17561step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17561step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw17561step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17561step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw17561step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17562 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17562Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17562step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw17562step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17562step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw17562step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17563 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17563Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17563step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw17563step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17563step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw17563step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17564 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw17564Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17564step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw17564step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17564step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17564step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17564step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17564step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17565 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17565Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17565step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17565step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17565step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17565step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17566 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17566Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17566step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw17566step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17566step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw17566step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17566step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw17566step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17567 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17567Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17567step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw17567step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17567step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw17567step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17568 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17568Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17568step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17568step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17568step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17568step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17569 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![2, 0, -2]]
def raw17569Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17569step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17569step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17569step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17569step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17569step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17569step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17570 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17570Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17570step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17570step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17570step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17570step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17571 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw17571Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17571step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw17571step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17571step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw17571step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17571step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw17571step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17572Labels : Fin 3 → Fin 2 := ![0, 1, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end


