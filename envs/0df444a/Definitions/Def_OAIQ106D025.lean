-- Prove2me | Definitions.Def_OAIQ106D025
-- name    : OAIQ106D025
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T12:11:30.277209+00:00
-- url     : https://prove2.me/theorems/ea13cee2-bf21-4760-8d06-d4fda7adadba
-- title:
--   Definitions bundle OAIQ106D025 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 7542 declarations of OpenAI's Lean: 7542 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSemantics.raw28551Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw28551step0`, `OAI.MUB6.Certificate.MixedSemantics.raw28551step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw28551step1`, `OAI.MUB6.Certificate.MixedSemantics.raw28551step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw28552`, `OAI.MUB6.Certificate.MixedSemantics.raw28552Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw28552step0`, `OAI.MUB6.Certificate.MixedSemantics.raw28552step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw28553`, `OAI.MUB6.Certificate.MixedSemantics.raw28553Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw28554`, `OAI.MUB6.Certificate.MixedSemantics.raw28554Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw28554step0`, `OAI.MUB6.Certificate.MixedSemantics.raw28554step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw28555`, `OAI.MUB6.Certificate.MixedSemantics.raw28555Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw28555step0`, `OAI.MUB6.Certificate.MixedSemantics.raw28555step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw28555step1`, `OAI.MUB6.Certificate.MixedSemantics.raw28555step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw28556`, `OAI.MUB6.Certificate.MixedSemantics.raw28556Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw28556step0`, `OAI.MUB6.Certificate.MixedSemantics.raw28556step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw28556step1`, `OAI.MUB6.Certificate.MixedSemantics.raw28556step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw28557`, `OAI.MUB6.Certificate.MixedSemantics.raw28557Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw28557step0`, `OAI.MUB6.Certificate.MixedSemantics.raw28557step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw28557step1`, `OAI.MUB6.Certificate.MixedSemantics.raw28557step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw28558`, `OAI.MUB6.Certificate.MixedSemantics.raw28558Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw28558step0`, `OAI.MUB6.Certificate.MixedSemantics.raw28558step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw28558step1`, `OAI.MUB6.Certificate.MixedSemantics.raw28558step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw28559` and 7502 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_MixedSemantics_Canonical0`, `MutuallyUnbiased_MixedSemantics_Canonical2`, `MutuallyUnbiased_MixedSemantics_Canonical22`, `MutuallyUnbiased_MixedSemantics_Canonical223`, `MutuallyUnbiased_MixedSemantics_Canonical224`, `MutuallyUnbiased_MixedSemantics_Canonical225`, `MutuallyUnbiased_MixedSemantics_Canonical226`, `MutuallyUnbiased_MixedSemantics_Canonical227`, `MutuallyUnbiased_MixedSemantics_Canonical228`, `MutuallyUnbiased_MixedSemantics_Canonical229`, `MutuallyUnbiased_MixedSemantics_Canonical23`, `MutuallyUnbiased_MixedSemantics_Canonical230`, `MutuallyUnbiased_MixedSemantics_Canonical231`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound1166`, `OAI.MUB6.Certificate.MixedSemantics.sound2828`, `OAI.MUB6.Certificate.MixedSemantics.sound5310`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound0`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound106`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound107`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound108`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound109`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound110`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound111`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound112`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound113`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound115`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound118`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound121`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound122`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound125`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound126`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound127`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound128`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound131`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound64`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound77`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound83`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound96`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1780`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound10`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound101`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound11`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1194`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound152`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1702`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1703`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1708`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1709`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1710`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1715`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1716`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1717`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1723`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1734`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1738`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1739`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1740`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1741`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1743`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1744`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1781`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1782`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1783`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1785`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1786`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1787`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1788`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1789`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1816`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1822`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1872`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1881`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1882`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1904`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1905`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1906`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1907`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1908`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1909`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1910`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1911`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1944`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1958`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2006`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2014`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2033`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2034`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2036`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2037`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2040`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2046`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2048`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2049`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2059`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2062`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2076`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2077`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound21`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2107`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound25`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound29`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound341`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound368`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound370`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound444`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound485`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound521`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound534`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound548`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound590`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound734`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound750`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound864`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound9`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound92`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound949`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound991`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound26` and `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound35`.
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

def raw28Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw28step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw28step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![-2, 2, 0]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw285Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw285step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw285step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw286 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw286Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw286step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw286step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw286step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw286step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw287 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw287Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw287step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw287step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw288 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![0, 1, -1], ![0, 2, -2], ![-2, 2, 0]]
def raw288Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw288step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw288step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw288step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw288step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw289 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![0, 1, -1], ![0, 2, -2], ![-2, 2, 0]]
def raw289Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw289step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw289step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw292 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![-2, 2, 0], ![0, 3, -3]]
def raw292Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw292step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![2, 0, -2], ![3, -3, 0]]
def raw292step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw292step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![2, 0, -2], ![3, -3, 0]]
def raw292step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw293 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![-2, 2, 0], ![0, 3, -3]]
def raw293Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw293step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-2, 1, 1], ![-3, 1, 2]]
def raw293step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw293step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def raw293step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw294 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw294Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw294step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw294step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw294step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw294step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw295 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw295Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw295step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw295step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw295step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw295step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw296 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![-1, 2, -1]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw2855Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2855step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2]]
def raw2855step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2855step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2]]
def raw2855step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2855step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![1, 1, -2]]
def raw2855step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2855step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw2855step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2855step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw2855step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2856Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2856step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2856step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2856step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2856step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2856step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2856step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2856step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2856step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2857Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2857step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2857step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2857step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw2857step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2857step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2857step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2858 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2858Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2858step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2858step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2858step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw2858step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2858step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2858step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2]]
def raw2859Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2859step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2]]
def raw2859step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2859step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2]]
def raw2859step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2859step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw2859step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2859step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2859step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2]]
def raw2860Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2860step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2]]
def raw2860step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2860step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2]]
def raw2860step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2860step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw2860step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2861Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2861step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2861step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2861step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2861step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2861step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2861step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2861step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2861step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2862Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2862step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2862step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2862step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw2862step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2862step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2862step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2863Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2863step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2863step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2863step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw2863step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2863step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2863step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2]]
def raw2864Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2864step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2]]
def raw2864step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2864step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2]]
def raw2864step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2864step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw2864step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2864step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2864step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2]]
def raw2865Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2865step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2]]
def raw2865step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2865step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2]]
def raw2865step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2865step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw2865step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2866Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2866step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2866step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2866step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2866step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2866step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2866step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2866step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2866step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2867Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2867step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2867step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2867step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw2867step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2867step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2867step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2868Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2868step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2868step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2868step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw2868step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2868step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2868step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2]]
def raw2869Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2869step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2]]
def raw2869step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2869step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2]]
def raw2869step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2869step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw2869step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2869step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2869step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2]]
def raw2870Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2870step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2]]
def raw2870step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2870step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2]]
def raw2870step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2870step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw2870step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw2871Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2871step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw2871step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2871step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw2871step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2871step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw2871step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2871step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw2871step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2871step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw2871step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw2872Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2872step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw2872step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2872step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw2872step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2872step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw2872step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2872step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2872step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw2873Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2873step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw2873step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2873step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw2873step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2873step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw2873step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2873step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2873step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw2874Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2874step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw2874step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2874step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw2874step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2874step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw2874step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2874step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2874step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw2875Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2875step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw2875step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2875step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw2875step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2875step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw2875step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw2876Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2876step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw2876step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2876step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw2876step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2876step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![3, -1, -2]]
def raw2876step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2876step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-3, 2, 1]]
def raw2876step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2876step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw2876step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw2877Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2877step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw2877step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2877step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw2877step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2877step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw2877step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2877step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2877step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw2878Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2878step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw2878step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2878step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw2878step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2878step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw2878step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2878step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2878step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw2879Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2879step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw2879step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2879step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw2879step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2879step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw2879step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2879step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2879step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw2880Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2880step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw2880step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2880step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw2880step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2880step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![3, -1, -2]]
def raw2880step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2880step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 0, 1], ![-2, 1, 1]]
def raw2880step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2880step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw2880step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2881 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2881Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2881step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2881step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2881step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2881step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2881step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0]]
def raw2881step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2881step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2881step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2881step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2881step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2882 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2882Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2882step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2882step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2882step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2882step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2882step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0]]
def raw2882step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2882step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2882step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2882step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2882step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2883 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2883Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2883step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2883step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2883step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2883step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2883step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0]]
def raw2883step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2883step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2883step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2883step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2883step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2884 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -2, 2]]
def raw2884Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2884step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -2, 2]]
def raw2884step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2884step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 0, 0], ![-2, 2, 0], ![0, -2, 2]]
def raw2884step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2884step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![-2, 2, 0], ![0, -2, 2]]
def raw2884step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2884step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![0, -2, 2], ![-2, 2, 0]]
def raw2884step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2884step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -2, 0]]
def raw2884step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2885 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw2885Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2885step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw2885step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2885step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw2885step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2885step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![-1, -1, 2]]
def raw2885step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2885step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw2885step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw2885step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw2885step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2886 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2886Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2886step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2886step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2886step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2886step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2886step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2886step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2886step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2886step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2887 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2887Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2887step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2887step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2887step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2887step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2887step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2887step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2888 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2888Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2888step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2888step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2888step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2888step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2888step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2888step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2889 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -2, 2]]
def raw2889Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2889step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -2, 2]]
def raw2889step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2889step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![-2, 2, 0], ![0, -2, 2]]
def raw2889step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2889step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2889step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2889step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2889step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2890 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw2890Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2890step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw2890step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2890step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw2890step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2890step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw2890step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2890step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw2890step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2891 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2891Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2891step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2891step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2891step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2891step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2891step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2891step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2891step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2891step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2892 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2892Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2892step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2892step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2892step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2892step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2892step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2892step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2893 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2893Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2893step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2893step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2893step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2893step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2893step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2893step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2894 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -2, 2]]
def raw2894Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2894step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![-2, 2, 0], ![0, -2, 2]]
def raw2894step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2894step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![-2, 2, 0], ![0, -2, 2]]
def raw2894step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2894step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2894step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2894step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2894step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2895 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw2895Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2895step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw2895step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2895step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw2895step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2895step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw2895step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2895step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw2895step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2896 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2896Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2896step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2896step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2896step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2896step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2896step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2896step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2896step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2896step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2897 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2897Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2897step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2897step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2897step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2897step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2897step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2897step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2898 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2898Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2898step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2898step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2898step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2898step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2898step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2898step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2899 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 2, 0], ![0, -2, 2]]
def raw2899Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2899step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![-2, 2, 0], ![0, -2, 2]]
def raw2899step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2899step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![-2, 2, 0], ![0, -2, 2]]
def raw2899step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2899step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2899step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2899step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2899step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2900 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw2900Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2900step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw2900step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2900step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw2900step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2900step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw2900step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2900step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw2900step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2901 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2]]
def raw2901Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2901step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2]]
def raw2901step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2901step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2]]
def raw2901step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2901step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![0, -2, 2]]
def raw2901step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2901step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![0, 2, -2], ![0, -2, 2]]
def raw2901step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2901step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![2, -2], ![-2, 2]]
def raw2901step4Labels : Fin 2 → Fin 3 := ![1, 2]

def raw2901step5 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]
def raw2901step5Labels : Fin 2 → Fin 3 := ![1, 2]

def raw2901step6 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]
def raw2901step6Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2902 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2]]
def raw2902Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2902step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2]]
def raw2902step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2902step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2902step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2902step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![0, -2, 2]]
def raw2902step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2902step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![-2, 1, 1]]
def raw2902step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2902step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw2902step4Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2902step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw2902step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2903 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2]]
def raw2903Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2903step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2903step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2903step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2903step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2903step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![0, -2, 2]]
def raw2903step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2903step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![-2, 1, 1]]
def raw2903step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2903step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw2903step4Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2903step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw2903step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2904 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2]]
def raw2904Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2904step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2]]
def raw2904step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2904step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2]]
def raw2904step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2904step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 1, 0], ![1, -3, 2]]
def raw2904step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2904step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw2904step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2904step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw2904step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2905 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2]]
def raw2905Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2905step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2]]
def raw2905step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2905step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![-1, 1, 0], ![1, -3, 2]]
def raw2905step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2905step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2905step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2905step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2905step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2906 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2]]
def raw2906Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2906step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -3, 2]]
def raw2906step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2906step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![-1, 1, 0], ![1, -3, 2]]
def raw2906step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2906step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2906step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2906step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2906step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2907 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -3, 2]]
def raw2907Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2907step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -3, 2]]
def raw2907step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2907step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![-1, 1, 0], ![1, -3, 2]]
def raw2907step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2907step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2907step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2907step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2907step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2908 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![1, -3, 2]]
def raw2908Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2908step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![1, -3, 2]]
def raw2908step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2908step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![-2, 2, 0], ![1, -3, 2]]
def raw2908step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2908step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 2, 0], ![1, -3, 2]]
def raw2908step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2908step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw2908step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2908step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw2908step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw2909Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2909step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw2909step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2909step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0]]
def raw2909step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2909step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw2909step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2909step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]
def raw2909step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2909step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![2, -2], ![-1, 1], ![-1, 1]]
def raw2909step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2909step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def raw2909step5Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw2910Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2910step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0]]
def raw2910step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2910step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw2910step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2910step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw2910step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2910step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]
def raw2910step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2910step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![2, -2], ![-1, 1], ![-1, 1]]
def raw2910step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2910step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def raw2910step5Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2911 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0]]
def raw2911Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2911step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw2911step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2911step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw2911step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2911step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw2911step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2911step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]
def raw2911step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2911step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![2, -2], ![-1, 1], ![-1, 1]]
def raw2911step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2911step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def raw2911step5Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2912 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw2912Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2912step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw2912step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2912step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw2912step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2912step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw2912step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2912step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]
def raw2912step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2912step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![2, -2], ![-1, 1], ![-1, 1]]
def raw2912step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2912step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def raw2912step5Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2913 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0]]
def raw2913Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2913step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0]]
def raw2913step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2913step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0]]
def raw2913step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2913step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw2913step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2913step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![-1, 1, 0], ![1, -1, 0]]
def raw2913step3Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2913step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]
def raw2913step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2914 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw2914Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2914step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw2914step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2914step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0]]
def raw2914step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2914step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2914step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2914step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw2914step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2915 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw2915Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2915step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0]]
def raw2915step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2915step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw2915step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2915step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![2, -2]]
def raw2915step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2915step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw2915step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2916 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0]]
def raw2916Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2916step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw2916step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2916step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw2916step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2916step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![2, -2]]
def raw2916step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2916step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw2916step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2917 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw2917Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2917step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw2917step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2917step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw2917step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2917step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![2, -2]]
def raw2917step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2917step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw2917step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2918 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0]]
def raw2918Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2918step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0]]
def raw2918step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2918step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw2918step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2918step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2918step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2918step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def raw2918step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2919 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw2919Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2919step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0]]
def raw2919step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2919step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2919step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2919step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2919step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2919step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw2919step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2920 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw2920Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2920step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0]]
def raw2920step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2920step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2920step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2920step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw2920step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2921 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0]]
def raw2921Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2921step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw2921step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2921step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw2921step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2921step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![2, -2]]
def raw2921step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2921step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw2921step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2922 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw2922Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2922step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw2922step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2922step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw2922step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2922step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![2, -2]]
def raw2922step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2922step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw2922step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2923 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0]]
def raw2923Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2923step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw2923step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2923step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2923step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2923step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2923step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2923step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def raw2923step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2924 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0]]
def raw2924Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2924step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2924step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2924step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2924step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2924step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2924step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2924step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw2924step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2925 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0]]
def raw2925Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2925step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2925step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2925step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2925step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2925step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw2925step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2926 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0]]
def raw2926Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2926step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2926step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2926step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2926step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2926step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw2926step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2927 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw2927Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2927step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw2927step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2927step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw2927step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2927step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![2, -2]]
def raw2927step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2927step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw2927step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw2928Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2928step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2928step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2928step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2928step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2928step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2928step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2928step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def raw2928step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2929Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2929step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2929step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2929step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2929step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2929step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2929step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2929step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw2929step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2930Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2930step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2930step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2930step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2930step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2930step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw2930step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2931Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2931step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2931step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2931step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2931step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2931step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw2931step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2932Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2932step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2932step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2932step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2932step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2932step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw2932step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2933 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2933Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2933step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2933step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2933step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2933step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2933step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2933step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2933step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def raw2933step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2934 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw2934Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2934step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw2934step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2934step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw2934step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2934step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![3, -3, 0]]
def raw2934step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2934step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, 3, 0], ![3, -3, 0]]
def raw2934step3Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2934step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-3, 3], ![3, -3]]
def raw2934step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw2935Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2935step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw2935step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2935step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0]]
def raw2935step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2935step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![3, -3, 0]]
def raw2935step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2935step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![3, -3]]
def raw2935step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2935step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-2, 2]]
def raw2935step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2935step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw2935step5Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw2936Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0]]
def raw2936step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2936step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0]]
def raw2936step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2936step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![3, -3, 0]]
def raw2936step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2936step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![3, -3]]
def raw2936step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2936step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-2, 2]]
def raw2936step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2936step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw2936step5Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0]]
def raw2937Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2937step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0]]
def raw2937step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2937step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0]]
def raw2937step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2937step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![3, -3, 0]]
def raw2937step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2937step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![3, -3]]
def raw2937step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2937step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-2, 2]]
def raw2937step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2937step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw2937step5Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0]]
def raw2938Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2938step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0]]
def raw2938step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2938step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0]]
def raw2938step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2938step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![3, -3, 0]]
def raw2938step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2938step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![3, -3]]
def raw2938step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2938step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-2, 2]]
def raw2938step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2938step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw2938step5Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2939Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2939step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw2939step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2939step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2939step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2939step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2939step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2940Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2940step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2940step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2940step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw2940step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2940step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2940step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2940step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2940step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2941Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2941step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2941step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2941step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw2941step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2941step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2941step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2941step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2941step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0]]
def raw2942Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2942step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2942step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2942step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2942step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2942step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw2942step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2942step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2942step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2942step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2942step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0]]
def raw2943Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2943step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2943step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2943step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2943step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2943step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw2943step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2943step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2943step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2943step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2943step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical223
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw28551Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28551step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw28551step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28551step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw28551step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28552 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw28552Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28552step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw28552step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28553 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw28553Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28554 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw28554Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28554step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw28554step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28555 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![3, 0, -3]]
def raw28555Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28555step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw28555step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28555step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw28555step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28556 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![3, 0, -3]]
def raw28556Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28556step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw28556step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28556step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw28556step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28557 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, -2, 2], ![1, -1, 0], ![3, 0, -3]]
def raw28557Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28557step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw28557step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28557step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw28557step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28558 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![-1, -1, 2], ![1, -1, 0], ![3, 0, -3]]
def raw28558Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28558step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw28558step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28558step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw28558step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28559 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -2, 2], ![0, 0, 0], ![3, 0, -3]]
def raw28559Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28559step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -2, 2], ![3, 0, -3]]
def raw28559step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28559step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw28559step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28559step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw28559step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28560 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw28560Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28560step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw28560step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28560step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw28560step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28561 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![-2, 2], ![0, 0], ![3, -3]]
def raw28561Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28561step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![-2, 2], ![3, -3]]
def raw28561step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28561step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-2, 2], ![3, -3]]
def raw28561step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28561step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-2, 2], ![-2, 2]]
def raw28561step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28561step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw28561step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28562 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28562Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28562step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28562step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28562step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28562step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28562step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw28562step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28562step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw28562step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28563 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28563Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28563step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28563step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28563step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw28563step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28563step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw28563step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28564 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28564Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28564step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28564step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28564step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw28564step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28564step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw28564step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28565 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28565Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28565step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28565step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28565step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw28565step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28565step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def raw28565step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28566 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28566Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28566step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw28566step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28566step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28566step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28567 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28567Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28567step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28567step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28567step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw28567step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28567step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def raw28567step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28568 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28568Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28568step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw28568step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28568step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28568step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28569 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28569Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28569step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28569step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28569step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28569step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28569step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw28569step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28569step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -2, 0], ![3, -1, -2]]
def raw28569step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28570 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28570Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28570step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28570step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28570step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw28570step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28570step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28570step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28571 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28571Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28571step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28571step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28571step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw28571step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28571step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28571step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28572 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28572Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28572step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28572step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28572step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28572step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28572step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw28572step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28572step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def raw28572step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28573 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28573Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28573step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28573step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28573step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw28573step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28573step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28573step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28574 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28574Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28574step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28574step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28574step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw28574step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28574step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28574step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28575 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28575Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28575step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28575step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28575step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28575step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28575step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![-2, 2, 0], ![-2, 0, 2]]
def raw28575step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28575step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -2, 0], ![2, 0, -2]]
def raw28575step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28576 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28576Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28576step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28576step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28576step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw28576step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28576step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw28576step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28577 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28577Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28577step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28577step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28577step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw28577step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28577step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw28577step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28578 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw28578Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28578step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw28578step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28578step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw28578step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28578step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![0, 1, -1], ![-1, 0, 1], ![-2, 2, 0]]
def raw28578step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28578step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw28578step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28579 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28579Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28579step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28579step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28579step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw28579step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28580 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28580Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28580step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw28580step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28581 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw28581Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28581step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw28581step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28581step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28581step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28582 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28582Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28582step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28582step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28582step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw28582step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28583 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28583Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28583step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw28583step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28584 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw28584Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28584step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw28584step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28584step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28584step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28585 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28585Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28585step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28585step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28585step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28585step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28585step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![2, 1, -3], ![3, -3, 0]]
def raw28585step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28586 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28586Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28586step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28586step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28586step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, 1, -3], ![3, -3, 0]]
def raw28586step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28587 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28587Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28587step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28587step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28587step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, 1, -3], ![3, -3, 0]]
def raw28587step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28588 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28588Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28588step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28588step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28588step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28588step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28588step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -3, -1], ![1, 1, -2], ![-2, 0, 2], ![-3, 2, 1]]
def raw28588step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28588step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![2, 0, -2], ![3, -2, -1]]
def raw28588step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28589 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28589Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28589step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28589step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28589step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![1, 1, -2], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw28589step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28589step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28589step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28590 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28590Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28590step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28590step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28590step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![1, 1, -2], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw28590step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28590step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28590step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28591 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28591Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28591step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28591step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28591step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28591step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28591step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw28591step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28591step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw28591step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28592 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28592Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28592step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28592step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28592step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw28592step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28592step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw28592step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28593 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28593Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28593step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28593step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28593step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw28593step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28593step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw28593step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28594 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28594Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28594step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28594step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28594step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw28594step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28594step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw28594step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28595 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28595Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28595step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw28595step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28595step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw28595step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28596 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28596Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28596step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28596step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28596step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw28596step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28596step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw28596step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28597 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28597Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28597step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw28597step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28597step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw28597step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28598 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28598Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28598step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28598step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28598step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28598step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28598step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![2, 1, -3]]
def raw28598step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28598step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![2, 1, -3]]
def raw28598step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28599 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28599Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28599step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28599step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28599step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw28599step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28599step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw28599step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28600 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28600Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28600step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28600step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28600step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw28600step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28600step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw28600step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28601 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28601Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28601step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28601step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28601step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28601step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28601step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw28601step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28601step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw28601step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28602 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28602Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28602step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28602step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28602step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw28602step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28602step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw28602step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28603 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28603Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28603step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28603step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28603step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw28603step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28603step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw28603step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28604 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28604Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28604step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28604step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28604step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28604step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28604step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw28604step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28604step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw28604step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28605 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28605Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28605step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28605step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28605step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw28605step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28605step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def raw28605step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28606 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28606Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28606step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28606step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28606step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw28606step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28606step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def raw28606step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28607 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28607Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28607step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28607step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28607step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28607step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28607step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw28607step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28607step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -2, 0], ![3, -1, -2]]
def raw28607step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28608 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28608Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28608step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28608step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28608step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28608step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28608step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw28608step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28608step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def raw28608step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28609 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28609Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28609step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw28609step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28609step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28609step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28610 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw28610Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28610step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw28610step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28610step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw28610step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28611 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28611Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28611step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28611step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28611step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw28611step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28611step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw28611step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28612 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28612Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28612step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw28612step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28612step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28612step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28613 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28613Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28613step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28613step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28613step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw28613step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28613step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28613step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28614 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28614Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28614step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28614step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28614step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw28614step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28614step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28614step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28615 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28615Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28615step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28615step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28615step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 1, -2], ![3, -3, 0]]
def raw28615step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28615step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw28615step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28615step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw28615step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28615step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw28615step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28616 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28616Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28616step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28616step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28616step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw28616step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28616step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw28616step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28616step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw28616step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28617 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28617Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28617step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28617step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28617step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw28617step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28617step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw28617step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28617step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw28617step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28618 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw28618Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28618step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw28618step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28618step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![3, -3, 0]]
def raw28618step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28618step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw28618step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw28618step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw28618step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28619 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw28619Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28619step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw28619step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28619step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw28619step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28619step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw28619step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28619step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw28619step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28620 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28620Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28620step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28620step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28620step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw28620step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28620step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw28620step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28621 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28621Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28621step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28621step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28621step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -2, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw28621step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28621step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw28621step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28621step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw28621step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28622 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28622Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28622step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28622step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28622step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28622step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28622step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28622step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28623 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw28623Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28623step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw28623step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28623step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw28623step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw28623step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw28623step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28624 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28624Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28624step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28624step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28624step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw28624step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28624step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw28624step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28625 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28625Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28625step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28625step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28625step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -2, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw28625step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28625step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw28625step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28625step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw28625step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28626 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28626Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28626step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28626step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28626step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28626step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28626step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28626step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28627 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw28627Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28627step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw28627step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28627step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw28627step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw28627step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw28627step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28628 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw28628Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28628step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw28628step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28628step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, 0, -2], ![3, -3, 0]]
def raw28628step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28628step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw28628step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28628step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw28628step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28629 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw28629Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28629step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw28629step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28629step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![2, 0, -2], ![3, -3, 0]]
def raw28629step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28629step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-2, 1, 1], ![-3, 1, 2]]
def raw28629step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28629step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def raw28629step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28629step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def raw28629step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28630 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw28630Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28630step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw28630step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28630step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28630step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28630step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28630step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28630step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28630step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28631 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw28631Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28631step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw28631step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28631step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28631step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28631step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28631step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28631step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28631step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28632 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw28632Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28632step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw28632step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28632step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 1, -2], ![4, -4, 0]]
def raw28632step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28632step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 1, 0], ![-4, 1, 3]]
def raw28632step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28632step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![4, -1, -3]]
def raw28632step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28632step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![4, -1, -3]]
def raw28632step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28633 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw28633Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28633step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw28633step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28633step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 1, -2], ![4, -4, 0]]
def raw28633step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28633step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw28633step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28633step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw28633step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28633step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw28633step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28634 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw28634Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28634step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![4, -4, 0]]
def raw28634step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28634step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28634step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28634step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28634step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28634step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28634step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28635 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![4, -4, 0]]
def raw28635Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28635step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![4, -4, 0]]
def raw28635step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28635step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28635step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28635step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28635step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28635step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28635step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28636 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![4, -4, 0]]
def raw28636Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28636step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![4, -4, 0]]
def raw28636step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28636step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 2, -2], ![4, -4, 0]]
def raw28636step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28636step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw28636step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw28636step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw28636step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28637 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28637Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28637step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28637step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 1, -2], ![3, -3, 0]]
def raw28637step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28637step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw28637step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28637step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw28637step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28638 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28638Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28638step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28638step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28638step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw28638step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28638step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw28638step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28639 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28639Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28639step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28639step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28639step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw28639step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28639step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw28639step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28640 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw28640Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28640step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw28640step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28640step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![3, -3, 0]]
def raw28640step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28640step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw28640step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28640step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw28640step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28641 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw28641Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28641step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw28641step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28641step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw28641step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28641step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw28641step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28642 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28642Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28642step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28642step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28642step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw28642step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28643 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28643Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28643step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28643step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28643step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -2, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw28643step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28643step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw28643step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28644 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28644Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28644step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28644step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28644step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28644step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28645 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw28645Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28645step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw28645step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28645step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw28645step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28645step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw28645step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28646 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28646Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28646step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28646step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28646step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw28646step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28647 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28647Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28647step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28647step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28647step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -2, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw28647step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28647step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw28647step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28648 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28648Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28648step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28648step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28648step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28648step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28649 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw28649Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28649step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw28649step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28649step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw28649step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28649step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw28649step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28650 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw28650Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28650step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw28650step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28650step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, 0, -2], ![3, -3, 0]]
def raw28650step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28650step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw28650step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28651 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw28651Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28651step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw28651step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28651step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![2, 0, -2], ![3, -3, 0]]
def raw28651step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28651step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-2, 1, 1], ![-3, 1, 2]]
def raw28651step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28651step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def raw28651step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28652 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw28652Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28652step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw28652step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28652step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28652step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28652step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28652step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28653 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw28653Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28653step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw28653step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28653step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28653step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28653step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28653step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28654 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw28654Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28654step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw28654step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28654step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 1, -2], ![4, -4, 0]]
def raw28654step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28654step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 1, 0], ![-4, 1, 3]]
def raw28654step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28654step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![4, -1, -3]]
def raw28654step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28655 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw28655Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28655step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw28655step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28655step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 1, -2], ![4, -4, 0]]
def raw28655step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28655step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw28655step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28655step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw28655step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28656 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw28656Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28656step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![4, -4, 0]]
def raw28656step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28656step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28656step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28656step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28656step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28657 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![4, -4, 0]]
def raw28657Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28657step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![4, -4, 0]]
def raw28657step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28657step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28657step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28657step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28657step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28658 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![4, -4, 0]]
def raw28658Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28658step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![4, -4, 0]]
def raw28658step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28658step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 2, -2], ![4, -4, 0]]
def raw28658step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28658step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw28658step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28658step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw28658step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical224
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw28679 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw28679Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28679step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw28679step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28679step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-1, 0, 1], ![0, -3, 3]]
def raw28679step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28679step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28679step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28679step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28679step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28679step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28679step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28715 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28715Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28715step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28715step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28716 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28716Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28716step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28716step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28717 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw28717Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28717step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28717step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28718 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28718Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28718step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28718step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28719 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28719Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28719step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw28719step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28719step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28719step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28720 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![3, -1, -2]]
def raw28720Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28720step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![3, -1, -2]]
def raw28720step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28720step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw28720step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28721 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw28721Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28721step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw28721step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28721step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw28721step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28721step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw28721step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28722 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw28722Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28722step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw28722step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28722step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28722step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw28723Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28723step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw28723step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28723step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28723step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28723step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28723step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28724 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw28724Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw28724step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28724step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw28724step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28724step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw28724step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28725 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw28725Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28725step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw28725step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28725step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28725step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28726 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw28726Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28726step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw28726step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28726step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28726step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28726step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28726step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28727 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw28727Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28727step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw28727step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28727step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw28727step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28727step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28727step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28728 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28728Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28728step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28728step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28728step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw28728step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28728step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw28728step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28729 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28729Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28729step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw28729step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28729step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw28729step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28730 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28730Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28730step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28730step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28730step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw28730step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28730step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw28730step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28731 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw28731Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28731step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw28731step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28731step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw28731step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28731step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw28731step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28732 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw28732Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28732step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw28732step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28732step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw28732step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28732step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw28732step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28733 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28733Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28733step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28733step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28733step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28733step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28733step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw28733step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28733step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw28733step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28733step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw28733step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28734 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28734Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28734step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw28734step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28734step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw28734step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28735 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28735Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28735step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw28735step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28735step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw28735step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw28736Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28736step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw28736step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28736step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw28736step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28737 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw28737Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28737step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw28737step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28737step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw28737step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28737step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw28737step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28738 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28738Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28738step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28738step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28738step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw28738step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28738step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw28738step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28739 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28739Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28739step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw28739step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28739step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw28739step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28740 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![3, -1, -2]]
def raw28740Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28740step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![3, -1, -2]]
def raw28740step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28740step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw28740step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28740step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw28740step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw28741Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28741step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw28741step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28741step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw28741step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28741step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw28741step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28741step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw28741step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28742 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw28742Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28742step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw28742step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28742step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw28742step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28742step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw28742step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw28743Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28743step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw28743step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28743step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw28743step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28744 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw28744Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28744step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw28744step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28744step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw28744step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28744step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw28744step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw28745Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28745step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw28745step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28745step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw28745step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28745step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw28745step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28745step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw28745step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw28746Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28746step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw28746step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28746step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw28746step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28746step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw28746step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28747 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw28747Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28747step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw28747step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28747step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw28747step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28748 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw28748Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28748step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw28748step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28748step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw28748step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28748step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw28748step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28749 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw28749Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28749step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw28749step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28749step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw28749step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28749step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw28749step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28750 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28750Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28750step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28750step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28750step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw28750step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28750step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw28750step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28751Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28751step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28751step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28752 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28752Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28752step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28752step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28753 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw28753Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28753step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw28753step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28753step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw28753step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28753step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw28753step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28754 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw28754Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28754step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw28754step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28754step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw28754step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28754step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw28754step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28755Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28755step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw28755step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28755step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw28755step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28756Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28756step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28756step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28756step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw28756step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28756step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28756step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28757Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28757step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw28757step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28757step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28757step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28758 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw28758Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28758step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw28758step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28758step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28758step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28759 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw28759Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28759step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw28759step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28759step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28759step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28760Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28760step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28760step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28760step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw28760step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28760step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw28760step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28761Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28761step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28761step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw28762Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw28762step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28762step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28762step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28762step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28762step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw28763Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28763step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw28763step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28763step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28763step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28763step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28763step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28764 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw28764Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28764step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw28764step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28764step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw28764step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw28765Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28765step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw28765step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28765step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw28765step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28766 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw28766Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28766step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw28766step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28766step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw28766step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28767 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw28767Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28767step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw28767step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28767step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw28767step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28767step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28767step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28767step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28767step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28768 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw28768Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28768step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw28768step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28768step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28768step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28768step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28768step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28769 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw28769Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28769step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw28769step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28769step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28769step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28769step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28769step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28770 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw28770Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28770step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28770step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28770step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28770step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28771 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![3, -2, -1]]
def raw28771Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28771step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw28771step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28771step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw28771step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28771step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28771step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28771step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28771step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28772 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw28772Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28772step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw28772step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28772step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw28772step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28772step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw28772step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28773 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw28773Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28773step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw28773step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28773step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![0, -1, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw28773step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28773step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw28773step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28773step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw28773step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28774 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw28774Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28774step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28774step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28774step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28774step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28774step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28774step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28775 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![3, -2, -1]]
def raw28775Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28775step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 2, -1], ![2, -2, 0], ![3, -2, -1]]
def raw28775step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28775step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![-1, 1, 0], ![-1, -1, 2], ![-3, 1, 2]]
def raw28775step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28775step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw28775step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28775step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw28775step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28776 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![4, -3, -1]]
def raw28776Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28776step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -3, -1]]
def raw28776step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28776step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-4, 1, 3]]
def raw28776step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28776step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw28776step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28776step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw28776step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28777 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![4, -3, -1]]
def raw28777Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28777step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![4, -3, -1]]
def raw28777step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28777step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw28777step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28777step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw28777step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28777step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw28777step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -3, -1]]
def raw28778Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28778step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28778step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28778step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28778step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28778step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28778step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28779 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![4, -3, -1]]
def raw28779Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28779step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![4, -3, -1]]
def raw28779step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28779step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-3, 1, 2]]
def raw28779step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28779step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw28779step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28779step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw28779step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28780 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![4, -3, -1]]
def raw28780Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28780step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw28780step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28780step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![4, -3, -1]]
def raw28780step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28780step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw28780step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28780step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28780step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28780step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28780step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28785 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw28785Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28785step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw28785step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28785step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28785step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw28786Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28786step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw28786step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28786step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28786step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw28787Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28787step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28787step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28788 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![3, -2, -1]]
def raw28788Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28788step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw28788step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28788step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw28788step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28788step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28788step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical225
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw28815 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw28815Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28815step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw28815step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28815step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw28815step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28815step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw28815step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28815step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw28815step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28818 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28818Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28818step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28818step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28818step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw28818step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28818step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw28818step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28819 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28819Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28819step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw28819step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28819step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw28819step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28820 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28820Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28820step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28820step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28820step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw28820step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28820step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw28820step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28821 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw28821Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28821step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw28821step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28821step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw28821step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28821step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw28821step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28821step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw28821step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28822 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28822Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28822step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw28822step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28822step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw28822step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28823 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28823Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28823step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28823step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28823step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28823step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28824 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw28824Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28824step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw28824step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28824step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw28824step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28824step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28824step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28825 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28825Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28825step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28825step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28825step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw28825step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28825step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def raw28825step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28826 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28826Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28826step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw28826step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28826step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28826step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28827 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![3, 0, -3]]
def raw28827Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28827step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28827step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28827step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28827step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28827step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw28827step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28827step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28827step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28828 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28828Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28828step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28828step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28828step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw28828step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28828step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw28828step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28829 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28829Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28829step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw28829step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28829step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28829step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28830 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28830Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28830step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28830step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28830step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28830step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28830step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28830step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28831 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28831Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28831step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28831step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28831step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw28831step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28831step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw28831step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28832 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28832Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28832step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw28832step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28832step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28832step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28833 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28833Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28833step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28833step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28833step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28833step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28833step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28833step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28834 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![4, -1, -3]]
def raw28834Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28834step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw28834step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28834step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw28834step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28834step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw28834step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28834step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28834step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28835 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28835Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28835step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28835step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28835step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0], ![-2, 0, 2]]
def raw28835step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28835step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw28835step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28836 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28836Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28836step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw28836step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28836step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw28836step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28837 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28837Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28837step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28837step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28837step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw28837step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28837step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw28837step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28838 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw28838Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28838step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw28838step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28838step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw28838step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28838step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![0, 1, -1], ![-1, 0, 1], ![-2, 2, 0]]
def raw28838step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28838step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw28838step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28839 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28839Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28839step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28839step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28840 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28840Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28840step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28840step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28841 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw28841Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28841step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw28841step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28841step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28841step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28842 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28842Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28842step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28842step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28842step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw28842step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28843 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28843Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28843step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw28843step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28844 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![3, 0, -3]]
def raw28844Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28844step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28844step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28844step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28844step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28844step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -3, 0]]
def raw28844step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28845 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28845Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28845step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28845step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28845step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw28845step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28846 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28846Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28846step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw28846step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28847Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28847step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28847step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28847step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw28847step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28848Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28848step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28848step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28848step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![1, 0, -1], ![0, 1, -1], ![-2, 0, 2], ![-3, 2, 1]]
def raw28848step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28848step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw28848step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28849Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28849step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -3, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw28849step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28849step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28849step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28850Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28850step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28850step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28850step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw28850step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28850step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw28850step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![4, -1, -3]]
def raw28851Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28851step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw28851step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28851step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw28851step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28851step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -3, -1], ![0, 1, -1], ![-1, 0, 1], ![-3, 2, 1]]
def raw28851step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28851step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw28851step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28852Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28852step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28852step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28852step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw28852step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28852step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw28852step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28853Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28853step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw28853step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28853step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw28853step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28854Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28854step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28854step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28854step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw28854step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28854step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw28854step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw28855Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28855step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw28855step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28855step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw28855step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28855step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw28855step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28855step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw28855step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28856Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28856step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw28856step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28856step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw28856step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28857Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28857step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw28857step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28857step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw28857step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28858 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw28858Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28858step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw28858step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28858step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw28858step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28858step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw28858step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28859Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28859step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28859step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28859step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw28859step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28859step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw28859step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28860Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28860step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw28860step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28860step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw28860step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![3, 0, -3]]
def raw28861Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28861step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28861step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28861step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28861step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28861step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw28861step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28861step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw28861step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28862Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28862step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28862step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28862step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw28862step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28862step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw28862step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28863Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28863step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw28863step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28863step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw28863step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28864Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28864step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28864step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28864step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw28864step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28864step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw28864step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28865Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28865step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28865step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28865step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw28865step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28865step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw28865step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28866Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28866step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw28866step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28866step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw28866step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28867Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28867step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28867step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28867step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw28867step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28867step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw28867step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![4, -1, -3]]
def raw28868Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28868step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw28868step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28868step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw28868step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28868step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw28868step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28868step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw28868step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28869Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28869step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28869step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28869step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw28869step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28869step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw28869step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28870Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28870step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw28870step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28870step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw28870step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28871Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28871step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28871step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28871step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw28871step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28871step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def raw28871step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28872Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28872step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28872step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28872step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw28872step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28872step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw28872step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28873Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28873step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28873step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28873step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw28873step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28873step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw28873step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28874Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28874step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28874step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28874step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28874step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw28875Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28875step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw28875step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28875step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw28875step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28875step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28875step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw28876Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28876step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw28876step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28877Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28877step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw28877step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28877step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw28877step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28878Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28878step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28878step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28878step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw28878step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28878step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28878step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28879Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28879step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw28879step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28879step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28879step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28880Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28880step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw28880step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28880step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28880step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28881 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28881Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28881step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw28881step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28881step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28881step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28882Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28882step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28882step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28882step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw28882step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28882step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw28882step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28883Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28883step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28883step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28883step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28883step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28883step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28883step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28884Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28884step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28884step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28884step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28884step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28884step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28884step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28885 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28885Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28885step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28885step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28885step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw28885step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28885step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw28885step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28885step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw28885step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28886 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28886Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28886step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw28886step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28886step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw28886step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28886step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw28886step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28887Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28887step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28887step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28887step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw28887step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28887step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw28887step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28887step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw28887step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28888 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw28888Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28888step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw28888step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28888step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw28888step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28888step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw28888step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28888step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw28888step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28889Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28889step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw28889step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28889step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw28889step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28890 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28890Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28890step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw28890step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28890step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw28890step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28890step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw28890step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28891 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28891Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28891step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-3, 1, 2]]
def raw28891step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28891step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw28891step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28891step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw28891step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28892 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw28892Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28892step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw28892step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28892step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28892step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28892step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28892step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28893 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28893Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28893step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28893step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28893step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-3, 1, 2]]
def raw28893step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28893step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw28893step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28893step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw28893step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28894 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28894Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28894step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28894step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28894step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28894step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28894step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28894step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28895 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw28895Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28895step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw28895step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28895step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw28895step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28895step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28895step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28895step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28895step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28896 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![3, -3, 0]]
def raw28896Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28896step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -3, 0]]
def raw28896step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28896step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw28896step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28896step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw28896step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28897 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![3, -3, 0]]
def raw28897Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28897step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -3, 0]]
def raw28897step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28897step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw28897step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28897step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw28897step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28897step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw28897step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28898 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -3, 0]]
def raw28898Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28898step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28898step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28898step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28898step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28898step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28898step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28899 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 2, -1], ![2, -1, -1], ![3, -3, 0]]
def raw28899Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28899step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -3, 0]]
def raw28899step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28899step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-3, 1, 2]]
def raw28899step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28899step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw28899step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28899step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw28899step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28900 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![4, -4, 0]]
def raw28900Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28900step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -4, 0]]
def raw28900step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28900step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-4, 1, 3]]
def raw28900step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28900step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw28900step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28900step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw28900step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28901 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![4, -4, 0]]
def raw28901Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28901step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![4, -4, 0]]
def raw28901step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28901step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw28901step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28901step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw28901step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28901step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw28901step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28902 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -4, 0]]
def raw28902Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28902step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28902step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28902step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28902step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28902step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28902step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28903 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![4, -4, 0]]
def raw28903Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28903step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![4, -4, 0]]
def raw28903step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28903step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-3, 1, 2]]
def raw28903step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28903step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw28903step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28903step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw28903step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28904 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw28904Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28904step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw28904step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28904step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw28904step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28904step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28904step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28904step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28904step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28913 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28913Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28913step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28913step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28913step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-3, 1, 2]]
def raw28913step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28913step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw28913step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28914 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28914Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28914step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28914step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28914step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28914step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28915 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw28915Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28915step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw28915step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28915step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw28915step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28915step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28915step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical226
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw28965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw28965Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28965step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw28965step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28965step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw28965step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28965step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw28965step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw28966Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28966step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw28966step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![2, 0, -2]]
def raw28967Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28967step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -3, 2], ![1, 1, -2], ![2, 0, -2]]
def raw28967step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw28968Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28968step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw28968step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28968step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw28968step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28968step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw28968step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28969 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw28969Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28969step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw28969step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28969step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw28969step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![3, 0, -3]]
def raw28970Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28970step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, -1, 2], ![1, 0, -1], ![3, 0, -3]]
def raw28970step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28970step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw28970step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28970step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw28970step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![3, 0, -3]]
def raw28971Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28971step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![3, 0, -3]]
def raw28971step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28971step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw28971step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28971step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw28971step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw28972Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28972step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw28972step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28972step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw28972step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28972step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw28972step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw28976Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28976step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw28976step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![2, 1, -3]]
def raw28977Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28977step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -3, 2], ![1, 0, -1], ![2, 1, -3]]
def raw28977step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def raw28978Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28978step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def raw28978step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw28985Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28985step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw28985step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28985step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw28985step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw28986Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28986step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw28986step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28986step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw28986step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -1, -2]]
def raw28987Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28987step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw28987step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28987step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw28987step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw28988Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28988step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw28988step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28988step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw28988step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw28989Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28989step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw28989step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28989step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw28989step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw28990Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28990step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw28990step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw28991Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw28996Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28996step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw28996step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28996step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw28996step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw28997Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28997step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw28997step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw28998Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw28999Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29005 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw29005Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29005step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw29005step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29005step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-3, 1, 2]]
def raw29005step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29005step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw29005step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29006 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw29006Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29006step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw29006step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29006step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw29006step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29006step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29006step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw29007Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29007step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![3, 0, -3]]
def raw29007step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29007step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw29007step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29007step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw29007step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29008 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw29008Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29008step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw29008step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29008step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw29008step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw29009Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29009step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![3, 0, -3]]
def raw29009step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29009step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw29009step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29009step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw29009step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29010 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw29010Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29010step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw29010step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29010step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw29010step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29010step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw29010step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29011 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![0, 0], ![-1, 1], ![3, -3]]
def raw29011Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29011step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![-1, 1], ![3, -3]]
def raw29011step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29011step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw29011step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29011step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw29011step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29012 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw29012Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29012step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![3, 0, -3]]
def raw29012step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29012step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29012step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29013 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw29013Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29013step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, -2, 1], ![3, 0, -3]]
def raw29013step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29013step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -2, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw29013step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29013step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw29013step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29014 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw29014Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29014step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw29014step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29014step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw29014step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29015 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw29015Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29015step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![3, 0, -3]]
def raw29015step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29015step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw29015step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29015step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw29015step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29016 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw29016Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29016step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![2, 1, -3]]
def raw29016step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29016step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw29016step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29020 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw29020Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29020step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw29020step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29020step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw29020step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29021 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw29021Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29021step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw29021step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29021step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw29021step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29022 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw29022Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29022step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![2, -2, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw29022step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29022step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29022step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29023 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw29023Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29023step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 0, 3]]
def raw29023step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29023step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29023step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29024 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw29024Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29024step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw29024step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29024step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw29024step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29024step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw29024step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29025 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw29025Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29025step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw29025step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29025step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29025step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw29026Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29026step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw29026step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw29027Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29027step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw29027step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29027step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw29027step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29028 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw29028Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29028step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw29028step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29028step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw29028step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29029 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw29029Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29029step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw29029step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29029step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw29029step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29030 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw29030Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29030step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw29030step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29030step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw29030step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29031 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw29031Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29031step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw29031step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29032 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![-1, 1], ![1, -1], ![2, -2]]
def raw29032Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29032step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw29032step0Labels : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical227
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw29063 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29063Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29063step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29063step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29063step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw29063step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29063step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw29063step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29063step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw29063step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29064 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29064Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29064step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29064step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29064step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw29064step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29064step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw29064step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29065 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29065Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29065step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29065step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29065step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw29065step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29065step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw29065step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29066 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29066Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29066step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29066step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29066step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![3, 0, -3]]
def raw29066step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29066step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![3, 0, -3]]
def raw29066step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29066step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![3, -3]]
def raw29066step3Labels : Fin 2 → Fin 3 := ![0, 2]

def raw29066step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-2, 2]]
def raw29066step4Labels : Fin 2 → Fin 3 := ![0, 2]

def raw29066step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw29066step5Labels : Fin 2 → Fin 3 := ![0, 2]

def raw29066step6 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw29066step6Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29067 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29067Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29067step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29067step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29067step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw29067step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29067step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw29067step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29067step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw29067step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29068 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29068Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29068step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29068step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29068step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw29068step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29069 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29069Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29069step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29069step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29069step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw29069step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29069step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw29069step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29070 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29070Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29070step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29070step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29070step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw29070step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29070step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw29070step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29071 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29071Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29071step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29071step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29071step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw29071step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29071step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![3, 0, -3]]
def raw29071step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29071step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-3, 1, 2]]
def raw29071step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29071step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw29071step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29072 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29072Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29072step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29072step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29072step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw29072step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29073 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29073Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29073step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29073step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29074 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29074Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29074step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29074step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29074step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-3, 1, 2]]
def raw29074step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29074step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw29074step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29075 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29075Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29075step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw29075step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29075step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw29075step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29076 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29076Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29076step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29076step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29076step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw29076step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29076step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw29076step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29076step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw29076step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29077 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29077Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29077step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29077step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29078 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29078Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29078step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29078step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29079 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29079Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29079step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29079step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29079step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-3, 1, 2]]
def raw29079step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29079step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw29079step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29080 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29080Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29080step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw29080step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29080step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw29080step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29081 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29081Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29081step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29081step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29081step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw29081step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29081step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw29081step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29081step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw29081step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29082 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29082Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29082step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29082step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29083 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29083Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29083step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29083step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29083step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw29083step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29084 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29084Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29084step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29084step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29084step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw29084step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29084step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-2, 1, 1], ![-3, 1, 2]]
def raw29084step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29084step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def raw29084step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29085 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29085Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29085step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29085step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29085step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw29085step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29085step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw29085step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29086 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29086Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29086step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29086step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29086step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw29086step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29086step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw29086step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29087 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw29087Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29087step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw29087step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29087step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw29087step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29088 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29088Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29088step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29088step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29088step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw29088step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29088step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 0, 1], ![-4, 2, 2]]
def raw29088step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29088step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw29088step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29089 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29089Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29089step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29089step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29089step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw29089step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29089step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-2, 1, 1], ![-3, 1, 2]]
def raw29089step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29089step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw29089step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29090 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29090Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29090step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29090step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29090step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw29090step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29090step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw29090step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29091 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29091Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29091step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29091step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29091step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw29091step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29091step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw29091step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29092 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw29092Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29092step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw29092step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29092step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![4, -1, -3]]
def raw29092step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29092step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![4, -1, -3]]
def raw29092step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29092step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 0, 1], ![-3, 1, 2]]
def raw29092step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29092step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![3, -1, -2]]
def raw29092step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29093 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29093Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29093step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29093step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29093step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw29093step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29093step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw29093step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29093step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw29093step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29094 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29094Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29094step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29094step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29094step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw29094step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29094step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw29094step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29095 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29095Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29095step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29095step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29095step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw29095step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29095step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw29095step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29096 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29096Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29096step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29096step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29096step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![3, 0, -3]]
def raw29096step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29096step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![3, 0, -3]]
def raw29096step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29096step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![3, -3]]
def raw29096step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29096step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-2, 2]]
def raw29096step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29096step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw29096step5Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29097 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29097Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29097step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29097step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29097step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw29097step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29097step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw29097step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29097step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw29097step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29098 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29098Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29098step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29098step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29098step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw29098step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29098step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw29098step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29098step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw29098step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29099 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29099Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29099step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29099step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29099step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw29099step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29099step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw29099step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29100 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29100Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29100step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29100step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29100step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw29100step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29100step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw29100step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29101 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29101Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29101step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29101step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29101step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw29101step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29101step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![3, 0, -3]]
def raw29101step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29101step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![2, 1, -3]]
def raw29101step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29101step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![2, 1, -3]]
def raw29101step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29102 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29102Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29102step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29102step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29102step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw29102step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29102step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw29102step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29102step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw29102step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29103 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29103Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29103step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29103step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29103step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw29103step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29103step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw29103step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29104Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29104step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29104step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29104step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw29104step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29104step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw29104step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29105Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29105step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw29105step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29105step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw29105step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29106 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29106Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29106step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29106step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29106step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw29106step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29106step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw29106step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29106step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw29106step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29107 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29107Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29107step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29107step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29107step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw29107step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29107step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw29107step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29108Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29108step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29108step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29108step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw29108step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29108step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw29108step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29109 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29109Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29109step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29109step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29109step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw29109step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29109step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw29109step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29110 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29110Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29110step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw29110step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29110step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw29110step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29111 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29111Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29111step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29111step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29111step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw29111step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29111step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw29111step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29111step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw29111step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29112Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29112step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29112step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29112step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw29112step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29112step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw29112step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29113 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29113Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29113step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29113step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29113step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw29113step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29113step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![2, 2, -4]]
def raw29113step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29113step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![2, 2, -4]]
def raw29113step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29114Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29114step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29114step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29114step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw29114step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29114step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 1, -2], ![2, 1, -3]]
def raw29114step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29114step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 1, -2], ![2, 1, -3]]
def raw29114step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29115 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29115Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29115step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29115step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29115step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw29115step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29115step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw29115step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29116 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29116Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29116step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29116step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29116step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw29116step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29116step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw29116step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29117 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw29117Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29117step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw29117step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29117step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw29117step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29117step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw29117step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29117step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw29117step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29118 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29118Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29118step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29118step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29118step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw29118step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29118step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw29118step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29118step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw29118step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29119 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29119Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29119step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29119step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29119step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw29119step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29119step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw29119step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29119step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw29119step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29120 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29120Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29120step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29120step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29120step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw29120step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29120step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw29120step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29121 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29121Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29121step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29121step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29121step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw29121step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29121step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw29121step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29122 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw29122Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29122step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw29122step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29122step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![4, -1, -3]]
def raw29122step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29122step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![4, -1, -3]]
def raw29122step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29122step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 0, -1], ![2, 1, -3]]
def raw29122step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29122step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 0, -1], ![2, 1, -3]]
def raw29122step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29123 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw29123Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29123step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw29123step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29123step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw29123step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29123step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw29123step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29124 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw29124Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29124step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw29124step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29124step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw29124step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29124step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw29124step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29125 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw29125Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29125step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw29125step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29125step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw29125step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29126 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![3, -1, -2]]
def raw29126Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29126step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -1, -2]]
def raw29126step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29126step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw29126step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29126step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw29126step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29127 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw29127Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29127step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw29127step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29127step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw29127step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29127step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw29127step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29128 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw29128Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29128step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw29128step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29128step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw29128step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29128step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw29128step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29129 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![-1, 1], ![2, -2], ![2, -2]]
def raw29129Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29129step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![2, -2], ![2, -2]]
def raw29129step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29129step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![2, -2], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw29129step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29129step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw29129step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29137 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw29137Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29137step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw29137step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29138 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw29138Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29138step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw29138step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw29139Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29139step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw29139step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29140 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw29140Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29140step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw29140step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29146 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29146Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29146step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29146step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29146step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw29146step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29146step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw29146step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29147 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29147Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29147step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw29147step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29147step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw29147step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29148 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29148Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29148step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29148step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29148step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![3, -3]]
def raw29148step1Labels : Fin 2 → Fin 3 := ![0, 2]

def raw29148step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw29148step2Labels : Fin 2 → Fin 3 := ![0, 2]

def raw29148step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw29148step3Labels : Fin 2 → Fin 3 := ![0, 2]

def raw29148step4 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw29148step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29149 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw29149Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29149step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw29149step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29149step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw29149step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29149step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw29149step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw29150Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29150step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw29150step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29150step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw29150step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29150step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw29150step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29151 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29151Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29151step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29151step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29152 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29152Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29152step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw29152step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29152step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw29152step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29153 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29153Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29153step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29153step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29153step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw29153step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29153step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw29153step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29154 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw29154Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29154step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw29154step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29154step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29154step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29154step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29154step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29155 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw29155Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29155step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw29155step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29155step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29155step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29155step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29155step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29156 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29156Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29156step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw29156step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29157 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29157Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29157step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw29157step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29157step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw29157step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29158 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29158Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29158step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw29158step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29158step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw29158step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29159 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw29159Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29159step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw29159step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29159step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw29159step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29160 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw29160Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29160step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw29160step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29161 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29161Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29161step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29161step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29162 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29162Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29162step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29162step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29162step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -2, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw29162step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29162step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw29162step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29163 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29163Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29163step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw29163step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29163step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw29163step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29164 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![3, 0, -3]]
def raw29164Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29164step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![0, 1, -1], ![3, 0, -3]]
def raw29164step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29164step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw29164step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29164step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw29164step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29165 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw29165Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29165step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw29165step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29166 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw29166Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29166step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw29166step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29167 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw29167Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29167step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw29167step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29167step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw29167step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29167step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw29167step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29168 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw29168Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29168step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw29168step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29168step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw29168step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29169 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![3, 0, -3]]
def raw29169Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29169step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![2, -1, -1], ![3, 0, -3]]
def raw29169step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29169step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw29169step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29169step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw29169step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29170 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw29170Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29170step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw29170step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29170step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw29170step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29170step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw29170step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw29171Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29171step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw29171step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29171step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw29171step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29171step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw29171step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw29172Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29172step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw29172step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29172step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw29172step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29172step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw29172step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29173 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw29173Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29173step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw29173step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29173step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw29173step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29174 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -1, -3]]
def raw29174Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29174step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![4, -1, -3]]
def raw29174step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29174step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw29174step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29174step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw29174step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29175 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw29175Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29175step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw29175step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29175step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw29175step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29175step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw29175step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29176 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw29176Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29176step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw29176step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29176step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw29176step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29176step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw29176step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29176step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw29176step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29180 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw29180Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29180step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw29180step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw29180step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw29180step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29182 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -3, 3]]
def raw29182Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29182step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, -3, 3]]
def raw29182step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29182step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![0, -1, 1], ![0, -3, 3]]
def raw29182step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29182step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-1, 1], ![-3, 3]]
def raw29182step2Labels : Fin 2 → Fin 3 := ![1, 2]

def raw29182step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw29182step3Labels : Fin 2 → Fin 3 := ![1, 2]

def raw29182step4 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw29182step4Labels : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical228
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw29184 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -3, 3]]
def raw29184Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29184step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw29184step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29184step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw29184step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29184step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw29184step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29184step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw29184step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29186 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -3, 3]]
def raw29186Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29186step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![-1, 1, 0], ![1, -2, 1], ![0, -3, 3]]
def raw29186step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29186step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw29186step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw29186step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw29186step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29190 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -4, 3]]
def raw29190Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29190step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -4, 3]]
def raw29190step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29190step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw29190step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw29190step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw29190step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29208 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -3, 3]]
def raw29208Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29208step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 3, -1], ![0, 0, 0], ![0, -1, 1], ![0, -3, 3]]
def raw29208step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29208step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 3, -1], ![0, -1, 1], ![0, -3, 3]]
def raw29208step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29208step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 2, -3], ![3, -2, -1]]
def raw29208step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw29208step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 2, -3], ![3, -2, -1]]
def raw29208step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29209 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -3, 3]]
def raw29209Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29209step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw29209step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29209step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw29209step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29209step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw29209step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29209step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw29209step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29210 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw29210Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29210step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw29210step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29210step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![-1, 0, 1], ![0, -3, 3]]
def raw29210step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29210step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw29210step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29210step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw29210step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29210step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw29210step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29211 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw29211Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29211step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw29211step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29211step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![0, -1, 1], ![-1, -2, 3]]
def raw29211step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29211step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw29211step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29211step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw29211step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29211step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw29211step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29212 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -3, 3]]
def raw29212Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29212step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw29212step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29212step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw29212step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw29212step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw29212step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw29212step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw29212step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29213 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 3, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -3, 3]]
def raw29213Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29213step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 3, -1], ![1, -1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw29213step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29213step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw29213step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw29213step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw29213step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29214 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw29214Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29214step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw29214step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29214step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-3, 1, 2]]
def raw29214step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29214step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw29214step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29214step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw29214step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29215 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw29215Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29215step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw29215step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29215step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw29215step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29215step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw29215step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29216 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw29216Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29216step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw29216step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29216step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw29216step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw29216step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw29216step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw29216step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw29216step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29217 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw29217Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29217step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 3, -1], ![1, -1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw29217step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29217step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw29217step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw29217step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw29217step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29218 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw29218Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29218step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw29218step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw29218step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw29218step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29219 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw29219Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29219step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw29219step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29219step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-3, 1, 2]]
def raw29219step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29219step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw29219step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29219step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw29219step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29220 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw29220Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29220step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw29220step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29220step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw29220step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29220step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw29220step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29221 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, -3, 3]]
def raw29221Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29221step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![0, -3, 3]]
def raw29221step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29221step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![1, -2, 1], ![0, -3, 3]]
def raw29221step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29221step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw29221step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw29221step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw29221step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29222 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, -3, 3]]
def raw29222Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29222step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 3, -1], ![0, 0, 0], ![1, -2, 1], ![0, -3, 3]]
def raw29222step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29222step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 3, -1], ![1, -2, 1], ![0, -3, 3]]
def raw29222step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29222step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![2, 1, -3], ![3, -2, -1]]
def raw29222step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw29222step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![2, 1, -3], ![3, -2, -1]]
def raw29222step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29223 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![0, -3, 3]]
def raw29223Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29223step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![-1, 1, 0], ![1, -2, 1], ![0, -3, 3]]
def raw29223step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29223step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw29223step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw29223step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw29223step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29224 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw29224Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29224step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw29224step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29224step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![1, -2, 1], ![-1, -2, 3]]
def raw29224step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29224step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 1, -2], ![3, -1, -2]]
def raw29224step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29224step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 1, -2], ![3, -1, -2]]
def raw29224step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29225 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -4, 3]]
def raw29225Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29225step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -4, 3]]
def raw29225step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29225step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![0, -1, 1], ![1, -4, 3]]
def raw29225step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29225step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, -1, -1], ![3, 0, -3]]
def raw29225step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw29225step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, -1, -1], ![3, 0, -3]]
def raw29225step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29226 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -4, 3]]
def raw29226Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29226step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 3, -1], ![0, 0, 0], ![0, -1, 1], ![1, -4, 3]]
def raw29226step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29226step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 3, -1], ![0, -1, 1], ![1, -4, 3]]
def raw29226step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29226step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, 1, -3], ![3, -2, -1]]
def raw29226step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw29226step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, 1, -3], ![3, -2, -1]]
def raw29226step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29227 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -4, 3]]
def raw29227Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29227step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -4, 3]]
def raw29227step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29227step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw29227step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw29227step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw29227step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29228 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -4, 3]]
def raw29228Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29228step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -4, 3]]
def raw29228step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29228step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![-1, 0, 1], ![1, -4, 3]]
def raw29228step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29228step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw29228step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw29228step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw29228step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29229 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29229Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29229step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29229step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29229step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29229step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29229step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-2, 2, 0], ![-2, -1, 3]]
def raw29229step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29229step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw29229step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29230 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29230Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29230step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29230step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29230step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw29230step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29230step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29230step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29231 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29231Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29231step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29231step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29231step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw29231step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29231step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29231step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29232Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29232step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29232step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29232step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29232step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29232step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![3, 0, -3]]
def raw29232step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29232step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw29232step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29232step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw29232step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29233 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29233Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29233step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29233step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29233step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29233step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29233step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw29233step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29233step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw29233step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29234 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29234Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29234step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29234step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29235 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29235Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29235step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29235step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29236 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29236Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29236step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29236step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29236step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29236step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29237 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29237Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29237step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29237step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29238 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29238Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29238step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29238step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29239 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29239Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29240 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29240Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29240step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29240step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29240step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29240step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29241 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29241Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29241step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29241step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29241step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29241step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29242 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29242Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29242step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29242step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29242step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-3, 0, 3]]
def raw29242step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29242step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29242step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29243 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29243Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29243step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29243step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29243step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-3, 0, 3]]
def raw29243step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29243step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29243step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29244 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw29244Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29244step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw29244step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29244step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw29244step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29245 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29245Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29245step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29245step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29245step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29245step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29245step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-2, 2, 0], ![-3, 0, 3]]
def raw29245step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29245step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29245step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29246 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29246Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29246step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29246step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29246step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-3, 0, 3]]
def raw29246step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29246step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29246step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29247 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29247Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29247step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29247step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29247step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-3, 0, 3]]
def raw29247step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29247step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29247step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29248Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29248step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29248step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29248step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29248step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29248step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw29248step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29248step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw29248step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29249 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29249Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29249step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29249step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29249step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw29249step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29249step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw29249step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29250Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29250step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29250step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29250step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw29250step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29250step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw29250step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29251 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29251Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29251step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29251step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29251step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29251step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29251step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![3, 0, -3]]
def raw29251step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29251step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw29251step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29251step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw29251step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29252 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29252Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29252step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29252step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29252step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29252step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29252step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw29252step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29252step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw29252step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29253 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29253Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29253step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29253step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29253step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw29253step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29253step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw29253step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29253step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw29253step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29254 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29254Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29254step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw29254step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29254step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw29254step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29255 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29255Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29255step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29255step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29255step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29255step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29255step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw29255step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29255step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw29255step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29256 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29256Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29256step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29256step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29256step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw29256step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29256step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw29256step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29256step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw29256step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29257 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29257Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29257step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29257step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29257step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw29257step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29257step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw29257step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29257step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw29257step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29258 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29258Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29258step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw29258step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29258step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw29258step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29259 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29259Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29259step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29259step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29259step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29259step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29259step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw29259step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29259step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw29259step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29260 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29260Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29260step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29260step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29260step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29260step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29260step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![3, 0, -3]]
def raw29260step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29260step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![3, 0, -3]]
def raw29260step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29261 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29261Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29261step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29261step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29261step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw29261step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29261step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw29261step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29262 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29262Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29262step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29262step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29262step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw29262step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29262step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw29262step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29263 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw29263Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29263step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw29263step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29263step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw29263step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29263step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-3, 1, 2]]
def raw29263step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29263step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw29263step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29263step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw29263step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29264 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29264Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29264step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29264step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29264step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29264step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29264step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![3, 0, -3]]
def raw29264step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29264step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![3, 0, -3]]
def raw29264step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29265 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29265Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29265step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29265step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29265step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw29265step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29265step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw29265step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29266 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29266Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29266step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29266step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29266step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw29266step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29266step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw29266step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29267 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29267Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29267step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29267step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29267step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29267step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29267step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-2, 2, 0], ![-2, -1, 3]]
def raw29267step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29267step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw29267step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29268 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29268Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29268step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29268step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29268step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29268step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29269 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29269Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29269step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29269step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29270 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29270Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29270step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29270step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29271 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29271Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29271step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29271step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29271step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29271step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29272 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29272Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29272step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29272step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29272step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29272step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29272step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-2, 2, 0], ![-3, 0, 3]]
def raw29272step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29272step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29272step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29273 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29273Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29273step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29273step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29273step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, -1, 3]]
def raw29273step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29273step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw29273step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29274 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29274Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29274step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw29274step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29274step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw29274step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29275 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29275Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29275step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29275step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29275step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw29275step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29275step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw29275step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29276 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw29276Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29276step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw29276step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29276step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw29276step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29276step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw29276step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29277 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw29277Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29277step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw29277step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29277step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw29277step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29277step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw29277step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29278 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29278Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29278step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29278step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29278step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29278step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29279 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29279Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29279step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw29279step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29280 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29280Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29280step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw29280step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29281 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw29281Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29281step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw29281step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29282 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw29282Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29282step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw29282step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29282step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw29282step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29282step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw29282step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29283 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29283Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29283step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29283step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29284 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29284Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29284step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 0, 3]]
def raw29284step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29284step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29284step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29285 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![3, 0, -3]]
def raw29285Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29285step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![3, 0, -3]]
def raw29285step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29285step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw29285step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29286 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw29286Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29286step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw29286step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29287 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw29287Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29287step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw29287step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29287step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-3, 0, 3]]
def raw29287step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29287step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw29287step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29288 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw29288Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29288step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 0, 3]]
def raw29288step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29288step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29288step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29289 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![3, 0, -3]]
def raw29289Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29289step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 0, 1], ![2, -1, -1], ![3, 0, -3]]
def raw29289step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29289step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw29289step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29289step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw29289step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29290 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw29290Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29290step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw29290step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29290step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-3, 1, 2]]
def raw29290step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29290step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw29290step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29290step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw29290step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29291 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw29291Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29291step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw29291step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29291step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-2, 2, 0], ![-3, 0, 3]]
def raw29291step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29291step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw29291step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29292 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw29292Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29292step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 0, 3]]
def raw29292step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29292step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29292step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29293 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -1, -3]]
def raw29293Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29293step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -1, -3]]
def raw29293step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29293step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw29293step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29293step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw29293step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29294 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw29294Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29294step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw29294step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29294step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw29294step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29294step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw29294step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29295 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -3, 0]]
def raw29295Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29295step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw29295step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29295step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![3, -3]]
def raw29295step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29296 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw29296Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29296step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![-1, 1], ![1, -1], ![3, -3]]
def raw29296step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29296step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![3, -3]]
def raw29296step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29297 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw29297Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29297step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw29297step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29297step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![3, -3]]
def raw29297step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29298 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw29298Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29298step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![3, -3]]
def raw29298step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29299 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -3, 0]]
def raw29299Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29299step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![3, -3, 0]]
def raw29299step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29299step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 2, 0], ![2, -2, 0], ![3, -3, 0]]
def raw29299step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29299step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![2, -2], ![3, -3]]
def raw29299step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29300 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, -3, 0]]
def raw29300Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29300step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -3, 0]]
def raw29300step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29300step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![-1, 1], ![2, -2], ![3, -3]]
def raw29300step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29300step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![2, -2], ![-1, 1], ![-1, 1], ![-3, 3]]
def raw29300step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29300step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![3, -3]]
def raw29300step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29301 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -3, 0]]
def raw29301Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29301step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -3, 0]]
def raw29301step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29301step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![-1, 1], ![2, -2], ![3, -3]]
def raw29301step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29301step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![2, -2], ![-1, 1], ![-1, 1], ![-3, 3]]
def raw29301step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29301step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![3, -3]]
def raw29301step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29302 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -4, 0]]
def raw29302Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29302step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![4, -4, 0]]
def raw29302step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29302step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 2, 0], ![1, -1, 0], ![4, -4, 0]]
def raw29302step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29302step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![4, -4]]
def raw29302step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29302step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![4, -4], ![1, -1], ![-2, 2], ![-3, 3]]
def raw29302step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29302step4 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![2, -2], ![3, -3]]
def raw29302step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29303 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![4, -4, 0]]
def raw29303Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29303step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -4, 0]]
def raw29303step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29303step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![-1, 1], ![1, -1], ![4, -4]]
def raw29303step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29303step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![4, -4], ![1, -1], ![-1, 1], ![-1, 1], ![-3, 3]]
def raw29303step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29303step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![1, -1], ![3, -3]]
def raw29303step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29304 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -4, 0]]
def raw29304Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29304step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -4, 0]]
def raw29304step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29304step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![-1, 1], ![1, -1], ![4, -4]]
def raw29304step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29304step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![4, -4], ![1, -1], ![-1, 1], ![-1, 1], ![-3, 3]]
def raw29304step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29304step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![1, -1], ![3, -3]]
def raw29304step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29305 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29305Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29305step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29305step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29309 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw29309Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29309step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw29309step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29309step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29309step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29310 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw29310Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29310step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw29310step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29311 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, -1, 2], ![3, -1, -2], ![2, -1, -1]]
def raw29311Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29311step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, -1, 2], ![3, -1, -2], ![2, -1, -1]]
def raw29311step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29311step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw29311step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29311step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw29311step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical229
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw29312 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![3, -2, -1]]
def raw29312Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29312step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, -1, 2], ![2, 0, -2], ![3, -2, -1]]
def raw29312step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29312step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![2, 0, -2], ![-1, 0, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw29312step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29312step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw29312step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29313 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29313Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29313step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29313step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29313step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, -1, 2]]
def raw29313step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29313step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]
def raw29313step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29314 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29314Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29314step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29314step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29314step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw29314step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29314step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw29314step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29315 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29315Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29315step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw29315step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29315step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw29315step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29316 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29316Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29316step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![2, -2, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29316step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29316step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw29316step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29316step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw29316step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29317 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29317Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29317step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29317step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29317step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29317step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29317step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw29317step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29318 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29318Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29318step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29318step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29318step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw29318step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29318step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw29318step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29319 : Matrix (Fin 6) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![0, 0], ![0, 0], ![-2, 2], ![-2, 2]]
def raw29319Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29319step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![0, 0], ![-2, 2], ![-2, 2]]
def raw29319step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29319step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-2, 2], ![-2, 2]]
def raw29319step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29319step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw29319step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29320 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29320Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29320step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29320step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29321 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29321Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29322Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29322step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29322step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29323 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw29323Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29323step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw29323step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29324 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29324Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29324step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29324step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29325 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29325Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29325step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29325step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29326 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29326Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29326step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw29326step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29326step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw29326step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29327 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29327Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29327step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![2, 0, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw29327step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29327step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw29327step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29328 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29328Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29328step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw29328step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29328step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw29328step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29329 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29329Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29329step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29329step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29329step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, -1, 2]]
def raw29329step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29329step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]
def raw29329step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29330 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-3, 1, 2], ![-1, -1, 2]]
def raw29330Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29330step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw29330step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29331 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw29331Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29331step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -2, 2], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0]]
def raw29331step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29331step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw29331step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29336 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw29336Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29336step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw29336step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29337 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw29337Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29337step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw29337step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29337step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29337step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29338 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw29338Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29338step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw29338step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29338step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw29338step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29339 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2], ![2, 0, -2], ![2, 0, -2]]
def raw29339Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29339step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw29339step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29339step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw29339step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29340 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw29340Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29340step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw29340step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29340step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw29340step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29341 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2], ![1, 1, -2]]
def raw29341Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29341step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw29341step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29341step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw29341step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29342 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![-2, 2], ![2, -2], ![2, -2]]
def raw29342Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29342step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-2, 2], ![2, -2], ![2, -2]]
def raw29342step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29342step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![2, -2], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw29342step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29342step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw29342step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29343 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29343Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29343step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29343step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29344 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29344Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29344step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29344step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29345 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29345Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29345step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29345step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29346 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw29346Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29346step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw29346step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29346step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw29346step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29347 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29347Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29347step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw29347step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29348 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29348Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29348step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29348step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29348step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29348step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29349 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29349Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29349step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29349step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29349step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 0, 2], ![-3, 3, 0]]
def raw29349step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29349step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw29349step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29350 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29350Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29350step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29350step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29350step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![2, 0, -2], ![0, -1, 1], ![-2, 0, 2], ![-3, 3, 0]]
def raw29350step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29350step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw29350step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29351 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29351Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29351step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw29351step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29351step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw29351step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29352 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29352Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29352step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29352step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29352step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-2, 0, 2], ![-1, -1, 2]]
def raw29352step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29352step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, -1, 2]]
def raw29352step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29352step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]
def raw29352step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29353 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-3, 1, 2], ![-1, -1, 2]]
def raw29353Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29353step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![1, -1, 0], ![-3, 1, 2], ![-1, -1, 2]]
def raw29353step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29353step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw29353step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29354 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw29354Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29354step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![1, -1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw29354step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29354step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -2, 2], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0]]
def raw29354step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29354step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0]]
def raw29354step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29355 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29355Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29355step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29355step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29355step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![-2, 0, 2], ![-1, -1, 2]]
def raw29355step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29355step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, -1, 2], ![-2, 3, -1]]
def raw29355step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29355step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]
def raw29355step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29356 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29356Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29356step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29356step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29356step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw29356step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29356step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw29356step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29357 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29357Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29357step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29357step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29357step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw29357step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29357step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw29357step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29357step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw29357step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29358 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29358Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29358step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29358step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29358step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-2, 0, 2], ![0, -2, 2]]
def raw29358step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29358step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw29358step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29358step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw29358step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29359 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw29359Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29359step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw29359step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29360 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw29360Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29360step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw29360step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29360step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw29360step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29360step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw29360step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29361 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw29361Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29361step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw29361step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29361step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw29361step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29362 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![2, 0, -2]]
def raw29362Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29362step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, -1, 2], ![2, 0, -2], ![2, 0, -2]]
def raw29362step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29362step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![-1, -1, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw29362step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29362step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw29362step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29363 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw29363Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29363step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw29363step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29363step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw29363step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29363step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw29363step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29364 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![1, 1, -2]]
def raw29364Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29364step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -2, 2], ![2, 0, -2], ![1, 1, -2]]
def raw29364step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29364step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw29364step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29364step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw29364step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29365 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![0, 0], ![-2, 2], ![2, -2], ![2, -2]]
def raw29365Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29365step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![-2, 2], ![2, -2], ![2, -2]]
def raw29365step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29365step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![2, -2]]
def raw29365step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29366 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw29366Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29366step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw29366step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29366step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![2, 0, -2], ![2, -1, -1]]
def raw29366step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29366step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![2, -1, -1], ![2, 0, -2]]
def raw29366step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29367 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw29367Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29367step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw29367step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29367step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![2, 0, -2], ![2, -1, -1]]
def raw29367step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29367step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![2, -1, -1], ![2, 0, -2]]
def raw29367step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29368 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw29368Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29368step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw29368step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29368step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw29368step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29369 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw29369Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29369step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw29369step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29369step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw29369step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29370 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw29370Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29370step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw29370step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29370step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![3, -1, -2], ![2, -1, -1]]
def raw29370step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29370step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-2, -1, 3], ![-3, 3, 0]]
def raw29370step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29370step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 1, -3], ![3, -3, 0]]
def raw29370step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29371 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw29371Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29371step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw29371step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29371step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![2, 0, -2], ![3, -2, -1]]
def raw29371step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29371step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![2, 0, -2], ![-2, -1, 3], ![-3, 3, 0]]
def raw29371step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29371step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![2, 1, -3], ![3, -3, 0]]
def raw29371step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29372 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-3, 3], ![0, 0], ![0, 0], ![2, -2], ![1, -1]]
def raw29372Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29372step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-3, 3], ![0, 0], ![2, -2], ![1, -1]]
def raw29372step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29372step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-3, 3], ![2, -2], ![1, -1]]
def raw29372step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29372step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![1, -1]]
def raw29372step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29372step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw29372step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29373 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw29373Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29373step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw29373step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29374 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw29374Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29374step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw29374step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29374step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw29374step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29375 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw29375Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29375step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw29375step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29376 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw29376Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29376step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw29376step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29376step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![0, 2, -2], ![2, -2, 0]]
def raw29376step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29377 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw29377Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29377step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw29377step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29377step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw29377step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29378 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw29378Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29378step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw29378step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29378step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw29378step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29379 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-3, 3], ![0, 0], ![-1, 1], ![2, -2], ![2, -2]]
def raw29379Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29379step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw29379step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29379step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw29379step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29380 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29380Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29380step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29380step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29381 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29381Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29381step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29381step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29382Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![1, 0, -1]]
def raw29383Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29383step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![1, 0, -1]]
def raw29383step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29383step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw29383step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw29384Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29384step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw29384step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29384step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw29384step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29384step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw29384step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29385 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw29385Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29385step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw29385step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29386 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![3, -1, -2], ![2, -1, -1]]
def raw29386Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29386step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, -1, 2], ![3, -1, -2], ![2, -1, -1]]
def raw29386step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29386step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw29386step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29386step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw29386step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29387 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![3, -2, -1]]
def raw29387Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29387step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, -1, 2], ![2, 0, -2], ![3, -2, -1]]
def raw29387step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29387step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![2, 0, -2], ![-1, 1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw29387step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29387step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw29387step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29388 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29388Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29388step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![2, -2, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29388step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29388step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw29388step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29388step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw29388step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29391 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29391Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29391step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29391step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29391step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw29391step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29391step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw29391step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29394 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29394Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29394step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29394step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29394step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29394step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29394step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw29394step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29395 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29395Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29395step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29395step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29395step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw29395step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29395step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw29395step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29400 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29400Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29400step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![2, -2, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29400step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29400step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw29400step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29400step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw29400step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29401 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29401Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29401step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![2, -2, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29401step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29401step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw29401step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29401step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw29401step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29402 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29402Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29402step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw29402step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29402step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw29402step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29403 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw29403Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29403step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![2, -2, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw29403step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29403step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw29403step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29404 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29404Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29404step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29404step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29405 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29405Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29405step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29405step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29406 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29406Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29406step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29406step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29407 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw29407Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29407step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw29407step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29408 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29408Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29408step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw29408step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29408step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw29408step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29409 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29409Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29409step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29409step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29410 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29410Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29410step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw29410step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29410step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw29410step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29411 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29411Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29411step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![2, 0, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw29411step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29411step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw29411step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29416 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29416Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29416step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29416step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29416step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw29416step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29417 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29417Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29417step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29417step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29417step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw29417step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29418 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29418Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29418step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29418step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29418step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29418step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29418step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw29418step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29419 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw29419Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29419step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw29419step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29419step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw29419step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29420 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29420Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29420step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw29420step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29420step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw29420step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29421 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29421Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29421step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw29421step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29421step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw29421step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29422 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29422Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29422step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29422step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29422step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw29422step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29422step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw29422step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29423 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw29423Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29423step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw29423step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29431 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw29431Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29431step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw29431step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29431step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw29431step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29431step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw29431step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29432 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw29432Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29432step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw29432step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29432step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw29432step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29433 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw29433Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29433step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw29433step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29434 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw29434Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29434step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw29434step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29435 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![3, -3, 0], ![2, 1, -3]]
def raw29435Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29435step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![3, -3, 0], ![2, 1, -3]]
def raw29435step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29435step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw29435step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29436 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29436Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29436step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw29436step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29436step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw29436step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29436step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw29436step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29437 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![0, 0], ![0, 0], ![3, -3]]
def raw29437Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29437step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![0, 0], ![3, -3]]
def raw29437step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29437step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![3, -3]]
def raw29437step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29437step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![3, -3]]
def raw29437step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29437step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-2, 2]]
def raw29437step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29437step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw29437step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29438 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![2, -3, 1]]
def raw29438Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29438step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2], ![2, -3, 1]]
def raw29438step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29438step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw29438step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29439 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![2, -3, 1]]
def raw29439Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29439step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 0, -1], ![2, 0, -2], ![2, -3, 1]]
def raw29439step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29439step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw29439step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw2944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2944Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2944step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2944step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2945Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2945step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2945step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2946Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2946step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2946step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0]]
def raw2947Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2947step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2947step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2947step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2947step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0]]
def raw2948Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2948step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2948step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2948step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2948step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2949Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2949step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2949step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2949step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2949step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2950Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2950step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2950step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2951 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2951Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2951step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 0, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2951step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2951step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2951step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0]]
def raw2952Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2952step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2952step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2952step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2952step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2952step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2952step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0]]
def raw2953Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2953step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2953step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2953step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2953step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2953step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2953step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2954Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2954step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2954step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2954step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2954step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2955Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2955step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2955step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2956Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2956step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2956step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2956step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2956step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw2957Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2957step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw2957step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2957step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw2957step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2957step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2957step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw2958Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2958step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw2958step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2958step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw2958step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2958step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2958step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw2959Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2959step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw2959step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2959step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw2959step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw2960Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2960step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw2960step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2960step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2960step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2960step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2960step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw2961Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2961step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw2961step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2961step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw2961step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2961step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2961step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2961step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2961step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0]]
def raw2962Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2962step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0]]
def raw2962step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2962step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw2962step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2962step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2962step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2962step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2962step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0]]
def raw2963Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2963step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2963step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2963step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2963step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw2964Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2964step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw2964step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw2965Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2965step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw2965step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2965step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2965step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2965step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2965step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw2966Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2966step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw2966step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2966step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw2966step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2966step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2966step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2966step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2966step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw2967Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2967step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw2967step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2967step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw2967step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2967step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2967step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2967step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2967step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical230
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw29440 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -3, 1]]
def raw29440Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29440step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![2, -3, 1]]
def raw29440step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29440step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw29440step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29441 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -3, 1]]
def raw29441Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29441step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw29441step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29442 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw29442Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29442step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw29442step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29443 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![1, -2, 1]]
def raw29443Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29443step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2], ![1, -2, 1]]
def raw29443step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29443step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw29443step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29444 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![0, 0], ![2, -2], ![-1, 1]]
def raw29444Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29444step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![2, -2], ![-1, 1]]
def raw29444step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29444step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw29444step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29444step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw29444step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29445 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw29445Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29445step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw29445step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29445step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw29445step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29446 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw29446Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29446step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw29446step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29446step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw29446step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29447 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-2, 2, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw29447Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29447step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-2, 2, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw29447step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29447step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw29447step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29448 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw29448Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29448step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw29448step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29449 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![-3, 1, 2], ![1, -3, 2]]
def raw29449Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29449step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-3, 1, 2], ![1, -3, 2]]
def raw29449step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29449step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -3, 2], ![1, 0, -1], ![2, 1, -3]]
def raw29449step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29450 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29450Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29450step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29450step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29450step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw29450step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29450step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw29450step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29451 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29451Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29451step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29451step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29451step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw29451step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29451step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw29451step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29452 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29452Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29452step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29452step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29452step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-2, 0, 2], ![0, -2, 2]]
def raw29452step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29452step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -2, 2], ![-2, 0, 2]]
def raw29452step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29452step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]
def raw29452step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29453 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29453Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29453step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw29453step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29453step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw29453step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29454 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29454Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29454step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29454step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29454step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw29454step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29454step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw29454step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29455 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29455Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29455step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw29455step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29455step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw29455step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29456 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29456Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29456step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29456step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29457 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29457Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29458Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29458step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29458step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![3, -3, 0], ![2, 0, -2]]
def raw29459Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29459step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw29459step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29460Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29461 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw29461Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29461step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw29461step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2], ![2, -2, 0]]
def raw29462Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29462step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29462step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2], ![2, -2, 0]]
def raw29463Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29463step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29463step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2], ![2, -2, 0]]
def raw29464Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29464step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29464step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29465 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![-1, 0, 1], ![2, 0, -2], ![2, -2, 0]]
def raw29465Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29465step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29465step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29466 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw29466Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29466step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw29466step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2], ![1, -1, 0]]
def raw29467Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29467step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw29467step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29468 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![-1, 1], ![2, -2], ![0, 0]]
def raw29468Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29468step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![-1, 1], ![2, -2]]
def raw29468step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29468step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw29468step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29468step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw29468step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29469 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 0, 1], ![2, 0, -2], ![2, -2, 0]]
def raw29469Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29469step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw29469step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29469step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw29469step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29470 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![-1, 0, 1], ![2, 0, -2], ![2, -2, 0]]
def raw29470Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29470step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29470step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29471 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 0, 1], ![3, -1, -2], ![2, -2, 0]]
def raw29471Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29471step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw29471step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29471step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw29471step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29472 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 0, 1], ![2, 0, -2], ![3, -3, 0]]
def raw29472Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29472step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw29472step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29473 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29473Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29473step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw29473step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29473step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw29473step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29474 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-2, 2, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29474Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29474step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw29474step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29474step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw29474step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29475 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw29475Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29475step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw29475step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29476 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29476Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29476step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw29476step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29476step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw29476step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29477 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29477Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29477step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw29477step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29477step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw29477step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29480 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29480Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29480step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29480step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29480step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw29480step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29482 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29482Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29482step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29482step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29483 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29483Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29483step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29483step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29484 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29484Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29485 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29485Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29485step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29485step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29486 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![3, -2, -1], ![2, -1, -1]]
def raw29486Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29486step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw29486step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29487 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29487Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29488 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw29488Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29488step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw29488step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29491 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29491Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29491step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29491step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29491step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw29491step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29493 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29493Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29493step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29493step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29493step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw29493step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29494 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, 1, 0], ![2, -2, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29494Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29494step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw29494step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29494step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw29494step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29495 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw29495Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29495step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw29495step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29495step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw29495step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29496 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29496Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29496step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29496step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29496step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw29496step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29496step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw29496step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29497 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29497Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29497step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29497step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29497step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw29497step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29497step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw29497step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29497step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]
def raw29497step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29498 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw29498Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29498step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw29498step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29498step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw29498step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29498step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw29498step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29499 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw29499Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29499step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw29499step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29500 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw29500Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29500step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, 1, -1], ![0, -2, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw29500step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29500step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw29500step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw29501Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29501step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw29501step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29501step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw29501step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw29502Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29502step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw29502step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29502step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw29502step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29503 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw29503Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29503step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw29503step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29504 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1]]
def raw29504Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29504step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw29504step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29504step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw29504step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29505 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![-2, 2], ![2, -2], ![1, -1]]
def raw29505Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29505step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw29505step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29506 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29506Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29506step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29506step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29507 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29507Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29507step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29507step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29508 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw29508Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29508step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw29508step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29508step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw29508step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29509 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29509Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29509step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29509step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29510 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29510Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29511 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw29511Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29511step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw29511step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29511step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![3, -3, 0], ![2, 0, -2]]
def raw29511step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29511step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-2, 0, 2], ![-3, 2, 1]]
def raw29511step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29511step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![3, -2, -1]]
def raw29511step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29511step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![3, -2, -1]]
def raw29511step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29512 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw29512Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29512step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw29512step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29512step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw29512step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29512step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw29512step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29512step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw29512step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29513 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw29513Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29513step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw29513step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29513step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw29513step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29513step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw29513step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29513step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw29513step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29514 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![1, 1, -2]]
def raw29514Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29514step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![1, 1, -2]]
def raw29514step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29514step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![3, -3, 0], ![1, 1, -2]]
def raw29514step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29514step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw29514step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29514step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw29514step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29514step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw29514step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29515 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29515Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29515step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29515step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29515step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29515step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29515step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29515step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29516 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29516Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29516step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29516step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29516step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw29516step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29516step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw29516step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29517 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29517Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29517step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29517step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29517step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw29517step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29517step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw29517step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29518 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw29518Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29518step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw29518step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29518step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw29518step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29518step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw29518step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29518step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw29518step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29519 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29519Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29519step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29519step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29519step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29519step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29520 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29520Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29520step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29520step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29521 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw29521Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29521step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw29521step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29521step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw29521step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29522 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29522Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29522step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29522step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29522step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29522step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29523 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29523Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29523step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29523step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29524 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw29524Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29524step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw29524step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29524step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![3, -3, 0], ![2, 0, -2]]
def raw29524step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29524step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-2, 0, 2], ![-3, 2, 1]]
def raw29524step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29524step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![3, -2, -1]]
def raw29524step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw29525Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29525step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw29525step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29525step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw29525step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29525step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw29525step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw29526Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29526step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw29526step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29526step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw29526step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29526step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw29526step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29527 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![1, 1, -2]]
def raw29527Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29527step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![1, 1, -2]]
def raw29527step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29527step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![3, -3, 0], ![1, 1, -2]]
def raw29527step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29527step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw29527step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29527step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw29527step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29528 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29528Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29528step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29528step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29528step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, 0, -2], ![2, -2, 0]]
def raw29528step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29528step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw29528step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29528step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29528step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29529 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29529Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29529step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29529step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29529step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw29529step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29529step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw29529step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29530Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29530step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29530step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29530step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw29530step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29530step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw29530step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29531 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw29531Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29531step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw29531step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29531step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![2, 0, -2], ![1, -1, 0]]
def raw29531step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29531step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw29531step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29531step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw29531step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29532 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29532Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29532step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29532step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29532step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29532step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29532step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29532step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29533 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29533Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29533step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29533step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29533step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29533step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29533step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29533step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29534 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29534Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29534step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29534step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29534step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29534step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29535 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw29535Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29535step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw29535step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29535step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw29535step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29535step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw29535step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29536 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29536Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29536step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29536step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29536step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29536step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29536step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29536step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29537 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29537Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29537step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29537step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29537step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29537step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29537step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29537step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29538 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29538Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29538step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29538step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29538step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29538step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29539 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw29539Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29539step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw29539step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29539step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw29539step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29539step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw29539step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw29540Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29540step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw29540step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29540step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![3, -1, -2], ![2, -2, 0]]
def raw29540step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29540step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw29540step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29540step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw29540step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29541 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw29541Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29541step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw29541step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29541step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![3, -1, -2], ![2, -2, 0]]
def raw29541step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29541step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29541step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29541step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29541step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw29542Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29542step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw29542step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29542step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw29542step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29542step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw29542step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29543 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw29543Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29543step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw29543step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29543step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw29543step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29543step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw29543step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29544 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![1, -1, 0]]
def raw29544Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29544step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![3, -1, -2], ![1, -1, 0]]
def raw29544step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29544step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![3, -1, -2], ![1, -1, 0]]
def raw29544step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29544step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw29544step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29544step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw29544step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29545 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29545Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29545step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29545step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29545step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, 0, -2], ![2, -2, 0]]
def raw29545step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29545step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw29545step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29545step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29545step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29546 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29546Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29546step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29546step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29546step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw29546step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29546step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw29546step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29547 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29547Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29547step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29547step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29547step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw29547step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29547step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw29547step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29548 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw29548Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29548step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw29548step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29548step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![2, 0, -2], ![1, -1, 0]]
def raw29548step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29548step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw29548step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29549 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29549Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29549step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29549step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29549step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29549step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29550 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29550Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29550step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29550step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29550step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29550step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29551 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29551Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29551step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29551step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29552 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw29552Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29552step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw29552step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29552step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw29552step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29553 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29553Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29553step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29553step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29553step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29553step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29554 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29554Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29554step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29554step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29554step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29554step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29555 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29555Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29555step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29555step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29556 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw29556Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29556step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw29556step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29556step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw29556step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29557 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw29557Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29557step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw29557step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29557step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![3, -1, -2], ![2, -2, 0]]
def raw29557step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29557step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw29557step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29558 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw29558Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29558step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw29558step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29558step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![3, -1, -2], ![2, -2, 0]]
def raw29558step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29558step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29558step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29559 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw29559Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29559step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw29559step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29559step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw29559step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29560 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw29560Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29560step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw29560step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29560step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw29560step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29561 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![1, -1, 0]]
def raw29561Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29561step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![3, -1, -2], ![1, -1, 0]]
def raw29561step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29561step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![3, -1, -2], ![1, -1, 0]]
def raw29561step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29561step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw29561step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29562 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29562Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29562step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29562step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29562step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![-2, 0, 2], ![0, -2, 2]]
def raw29562step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29562step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29562step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29562step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29562step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29563 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29563Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29563step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29563step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29563step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29563step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29563step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29563step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29564 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29564Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29564step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29564step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29564step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29564step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29564step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29564step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29565 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw29565Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29565step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw29565step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29565step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-3, 1, 2], ![0, -2, 2]]
def raw29565step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29565step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw29565step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29565step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw29565step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29566 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29566Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29566step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29566step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29566step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-2, 0, 2], ![-1, -1, 2]]
def raw29566step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29566step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29566step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29566step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29566step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29567 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29567Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29567step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29567step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29567step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-2, 0, 2], ![0, -2, 2]]
def raw29567step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29567step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29567step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29567step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29567step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical231
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw29568 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29568Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29568step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29568step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29568step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw29568step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29568step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw29568step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29569 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29569Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29569step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29569step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29569step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw29569step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29569step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw29569step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29570 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw29570Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29570step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw29570step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29570step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-3, 1, 2], ![0, -2, 2]]
def raw29570step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29570step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw29570step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29570step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw29570step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29571 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29571Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29571step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29571step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29571step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-2, 0, 2], ![-1, -1, 2]]
def raw29571step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29571step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29571step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29571step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29571step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29572 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29572Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29572step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29572step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29572step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29572step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29572step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29572step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29573 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29573Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29573step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29573step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29573step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29573step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29573step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29573step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29574 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29574Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29574step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29574step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29574step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29574step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29575 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw29575Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29575step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw29575step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29575step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw29575step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29575step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw29575step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29576 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29576Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29576step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29576step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29576step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29576step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29576step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29576step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29577 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29577Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29577step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29577step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29577step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29577step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29577step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29577step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29578 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29578Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29578step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29578step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29578step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29578step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29578step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29578step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29579 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29579Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29579step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29579step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29579step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29579step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29580 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw29580Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29580step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw29580step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29580step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw29580step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29580step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw29580step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29581 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29581Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29581step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29581step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29581step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29581step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29581step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29581step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29582 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29582Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29582step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29582step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29582step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, -1, 2], ![0, -2, 2]]
def raw29582step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29582step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw29582step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29582step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw29582step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29583 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29583Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29583step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29583step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29583step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-1, -1, 2], ![0, -2, 2]]
def raw29583step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29583step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29583step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29583step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29583step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29584 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29584Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29584step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29584step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29584step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29584step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29584step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29584step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29585 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29585Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29585step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29585step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29585step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29585step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29585step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29585step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29586 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29586Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29586step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29586step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29586step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw29586step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29586step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29586step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29586step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29586step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29587 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw29587Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29587step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw29587step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29587step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-2, 0, 2], ![1, -3, 2]]
def raw29587step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29587step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw29587step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29587step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw29587step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29588 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw29588Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29588step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw29588step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29588step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-2, 0, 2], ![1, -3, 2]]
def raw29588step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29588step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw29588step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29588step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw29588step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29589 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw29589Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29589step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw29589step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29589step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw29589step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29589step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw29589step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29590 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw29590Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29590step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw29590step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29590step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw29590step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29590step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw29590step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29591 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-3, 1, 2], ![1, -3, 2]]
def raw29591Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29591step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-3, 1, 2], ![1, -3, 2]]
def raw29591step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29591step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-3, 1, 2], ![1, -3, 2]]
def raw29591step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29591step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw29591step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29591step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw29591step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29592 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29592Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29592step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29592step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29592step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![-2, 0, 2], ![0, -2, 2]]
def raw29592step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29592step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29592step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29592step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29592step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29593 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29593Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29593step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29593step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29593step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29593step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29593step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29593step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29594 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29594Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29594step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29594step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29594step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29594step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29594step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29594step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29595 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw29595Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29595step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw29595step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29595step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-3, 1, 2], ![0, -2, 2]]
def raw29595step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29595step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw29595step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29595step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw29595step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29596 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29596Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29596step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29596step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29596step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-2, 0, 2], ![-1, -1, 2]]
def raw29596step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29596step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29596step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29596step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29596step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29597 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29597Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29597step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29597step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29597step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-2, 0, 2], ![0, -2, 2]]
def raw29597step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29597step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -2, 0], ![2, 0, -2]]
def raw29597step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29597step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -2, 0], ![2, 0, -2]]
def raw29597step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29598 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29598Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29598step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29598step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29598step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29598step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29598step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29598step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29599 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29599Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29599step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29599step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29599step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29599step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29599step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29599step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29600 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw29600Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29600step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw29600step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29600step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-3, 1, 2], ![0, -2, 2]]
def raw29600step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29600step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -2, 0], ![2, 1, -3]]
def raw29600step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29600step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -2, 0], ![2, 1, -3]]
def raw29600step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29601 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29601Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29601step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29601step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29601step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-2, 0, 2], ![-1, -1, 2]]
def raw29601step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29601step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw29601step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29601step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw29601step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29602 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29602Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29602step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29602step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29602step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw29602step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29602step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw29602step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29603 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29603Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29603step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29603step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29603step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw29603step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29603step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw29603step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29604 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29604Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29604step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29604step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29604step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29604step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29605 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw29605Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29605step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw29605step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29605step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw29605step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29605step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw29605step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29606 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29606Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29606step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29606step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29606step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29606step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29606step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29606step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29607 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29607Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29607step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29607step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29607step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw29607step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29607step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw29607step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29608 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29608Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29608step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29608step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29608step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw29608step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29608step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw29608step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29609 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29609Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29609step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29609step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29609step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29609step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29610 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw29610Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29610step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw29610step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29610step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw29610step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29610step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw29610step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29611 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29611Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29611step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29611step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29611step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29611step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29611step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29611step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29612 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29612Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29612step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29612step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29612step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, -1, 2], ![0, -2, 2]]
def raw29612step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29612step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![2, -2, 0], ![2, -1, -1]]
def raw29612step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29612step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![2, -2, 0], ![2, -1, -1]]
def raw29612step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29613 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29613Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29613step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29613step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29613step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-1, -1, 2], ![0, -2, 2]]
def raw29613step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29613step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw29613step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29613step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw29613step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29614 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29614Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29614step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29614step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29614step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29614step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29614step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29614step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29615 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29615Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29615step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29615step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29615step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29615step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29615step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29615step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29616 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29616Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29616step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29616step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29616step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw29616step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29616step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw29616step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29616step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw29616step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29617 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw29617Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29617step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw29617step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29617step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-2, 0, 2], ![1, -3, 2]]
def raw29617step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29617step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![3, -3, 0]]
def raw29617step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29617step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![3, -3, 0]]
def raw29617step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29618 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw29618Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29618step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw29618step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29618step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-2, 0, 2], ![1, -3, 2]]
def raw29618step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29618step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw29618step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29618step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw29618step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29619 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw29619Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29619step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw29619step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29619step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw29619step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29619step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw29619step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29620 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw29620Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29620step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw29620step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29620step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw29620step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29620step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw29620step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29621 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-3, 1, 2], ![1, -3, 2]]
def raw29621Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29621step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-3, 1, 2], ![1, -3, 2]]
def raw29621step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29621step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-3, 1, 2], ![1, -3, 2]]
def raw29621step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29621step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -3, 1], ![2, 1, -3]]
def raw29621step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29621step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -3, 1], ![2, 1, -3]]
def raw29621step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29622 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29622Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29622step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29622step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29622step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29622step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29623 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29623Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29623step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29623step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29624 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29624Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29624step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29624step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29625 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29625Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29625step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29625step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29625step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29625step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29625step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw29625step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29626 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29626Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29626step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29626step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29627 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29627Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29627step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29627step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29628 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29628Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29628step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29628step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29628step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw29628step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29629 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29629Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29629step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29629step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29630 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29630Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29631 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29631Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29631step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29631step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29631step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw29631step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29632 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29632Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29632step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29632step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29632step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29632step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29632step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-2, 0, 2], ![-3, 2, 1]]
def raw29632step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29632step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29632step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29632step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29632step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29633 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29633Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29633step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29633step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29633step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw29633step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29633step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw29633step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29633step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw29633step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29634 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29634Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29634step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29634step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29634step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw29634step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29634step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw29634step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29634step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw29634step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29635 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw29635Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29635step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw29635step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29635step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![3, -2, -1], ![1, 0, -1]]
def raw29635step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29635step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw29635step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29636 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29636Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29636step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29636step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29636step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29636step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29636step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29636step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29637 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29637Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29637step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29637step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw29637step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29637step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw29637step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29638 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29638Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29638step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29638step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29638step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw29638step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29638step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw29638step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29639 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29639Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29639step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29639step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29639step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29639step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29639step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw29639step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29639step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw29639step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29640 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29640Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29640step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29640step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29640step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29640step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29641 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29641Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29641step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29641step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29642 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29642Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29642step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29642step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29642step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw29642step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29643 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29643Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29643step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29643step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29643step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29643step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29644 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29644Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29644step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29644step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29645 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29645Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29645step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29645step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29645step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw29645step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29646 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29646Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29646step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29646step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29646step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29646step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29646step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-2, 0, 2], ![-3, 2, 1]]
def raw29646step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29646step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29646step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29647 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29647Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29647step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29647step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29647step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw29647step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29647step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw29647step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29648 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29648Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29648step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29648step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29648step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw29648step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29648step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw29648step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29649 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw29649Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29649step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw29649step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29649step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![3, -2, -1], ![1, 0, -1]]
def raw29649step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29649step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw29649step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29649step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw29649step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29650 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29650Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29650step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29650step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29650step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29650step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29650step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29650step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29651 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29651Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29651step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29651step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29651step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29651step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29652 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29652Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29652step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29652step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29652step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw29652step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29652step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw29652step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29653 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29653Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29653step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29653step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29653step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29653step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29653step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29653step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29654 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29654Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29654step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29654step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29654step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29654step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29655 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29655Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29655step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29655step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29655step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw29655step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29655step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw29655step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29656 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29656Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29656step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29656step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29656step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![3, -2, -1], ![2, -1, -1]]
def raw29656step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29656step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw29656step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29656step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw29656step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29657 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29657Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29657step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29657step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29657step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw29657step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29657step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw29657step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29657step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw29657step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29658 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29658Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29658step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29658step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29658step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw29658step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29658step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw29658step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29658step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw29658step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29659 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw29659Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29659step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw29659step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29659step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![3, -2, -1], ![1, 0, -1]]
def raw29659step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29659step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw29659step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29659step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw29659step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29660 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29660Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29660step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29660step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29660step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw29660step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29660step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw29660step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29661 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29661Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29661step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29661step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29661step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw29661step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29661step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw29661step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29662 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29662Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29662step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29662step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29662step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw29662step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29662step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw29662step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29663 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29663Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29663step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29663step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29663step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1]]
def raw29663step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29663step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw29663step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29664 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29664Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29664step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29664step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29664step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29665 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29665Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29665step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29665step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29666 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29666Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29666step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29666step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29666step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw29666step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29667 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29667Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29667step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29667step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29667step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29667step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29668 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29668Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29668step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29668step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29669 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29669Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29669step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29669step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29669step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw29669step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29670 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29670Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29670step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29670step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29670step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![3, -2, -1], ![2, -1, -1]]
def raw29670step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29670step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw29670step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29671 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29671Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29671step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29671step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29671step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw29671step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29671step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw29671step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29672 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29672Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29672step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29672step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29672step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw29672step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29672step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw29672step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29673 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw29673Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29673step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw29673step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29673step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![3, -2, -1], ![1, 0, -1]]
def raw29673step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29673step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw29673step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29674 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29674Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29674step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29674step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29674step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw29674step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29674step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29674step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29674step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29674step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29675 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29675Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29675step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29675step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29675step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29675step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29675step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29675step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29676 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29676Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29676step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29676step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29676step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29676step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29676step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29676step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29677 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw29677Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw29677step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29677step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw29677step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29677step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29677step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29677step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29677step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29678 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29678Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29678step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29678step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29678step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw29678step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29678step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29678step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29678step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29678step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29679 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29679Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29679step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29679step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29679step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw29679step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29679step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw29679step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29680 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29680Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29680step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29680step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29680step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw29680step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29680step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw29680step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29681 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw29681Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29681step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw29681step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29681step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw29681step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29681step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29681step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29681step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29681step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29682 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29682Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29682step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29682step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29682step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29682step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29682step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29682step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29683 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29683Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29683step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29683step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29683step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29683step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29683step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29683step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29684 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29684Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29684step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29684step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29684step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29684step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29685 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw29685Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29685step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw29685step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29685step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29685step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29685step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29685step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29686 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29686Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29686step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29686step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29686step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]

end MUB6.Certificate.MixedSemantics

end OAI
end


