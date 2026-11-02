-- Prove2me | Definitions.Def_OAIQ106D013
-- name    : OAIQ106D013
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T12:02:00.407291+00:00
-- url     : https://prove2.me/theorems/ab118e13-9cfb-4799-9714-e0faafdecd89
-- title:
--   Definitions bundle OAIQ106D013 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1260 declarations of OpenAI's Lean: 1260 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSemantics.raw18220`, `OAI.MUB6.Certificate.MixedSemantics.raw18220Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18220step0`, `OAI.MUB6.Certificate.MixedSemantics.raw18220step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18221`, `OAI.MUB6.Certificate.MixedSemantics.raw18221Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18221step0`, `OAI.MUB6.Certificate.MixedSemantics.raw18221step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18222`, `OAI.MUB6.Certificate.MixedSemantics.raw18222Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18222step0`, `OAI.MUB6.Certificate.MixedSemantics.raw18222step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18223`, `OAI.MUB6.Certificate.MixedSemantics.raw18223Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18223step0`, `OAI.MUB6.Certificate.MixedSemantics.raw18223step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18223step1`, `OAI.MUB6.Certificate.MixedSemantics.raw18223step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18223step2`, `OAI.MUB6.Certificate.MixedSemantics.raw18223step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18224`, `OAI.MUB6.Certificate.MixedSemantics.raw18224Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18224step0`, `OAI.MUB6.Certificate.MixedSemantics.raw18224step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18224step1`, `OAI.MUB6.Certificate.MixedSemantics.raw18224step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18224step2`, `OAI.MUB6.Certificate.MixedSemantics.raw18224step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18225`, `OAI.MUB6.Certificate.MixedSemantics.raw18225Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18225step0`, `OAI.MUB6.Certificate.MixedSemantics.raw18225step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18225step1`, `OAI.MUB6.Certificate.MixedSemantics.raw18225step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18226`, `OAI.MUB6.Certificate.MixedSemantics.raw18226Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18227`, `OAI.MUB6.Certificate.MixedSemantics.raw18227Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18227step0`, `OAI.MUB6.Certificate.MixedSemantics.raw18227step0Labels` and 1220 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_MixedSemantics_Canonical1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical1.lean), [`MutuallyUnbiased_MixedSemantics_Canonical14`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical14.lean), [`MutuallyUnbiased_MixedSemantics_Canonical142`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical142.lean), [`MutuallyUnbiased_MixedSemantics_Canonical143`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical143.lean), [`MutuallyUnbiased_MixedSemantics_Singletons45`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Singletons45.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound1475`, `OAI.MUB6.Certificate.MixedSemantics.sound2904`, `OAI.MUB6.Certificate.MixedSemantics.sourceEq1094`, `OAI.MUB6.Certificate.MixedSemantics.sourceEq1095`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound125`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound128`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound131`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound21`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound28`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound35`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound49`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound6`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound7`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1780`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound0`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound109`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1108`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1114`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound113`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1130`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1158`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1191`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1293`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1317`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1433`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1505`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1508`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound151`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1516`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1648`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1655`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1657`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1672`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1673`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1686`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1687`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1708`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1710`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1715`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1744`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1822`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1835`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1839`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1844`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1853`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1858`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1873`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1882`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1904`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1963`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1968`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1993`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1995`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1999`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2006`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2033`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2059`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2066`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2099`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2107`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2108`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound267`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound339`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound357`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound365`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound369`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound417`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound444`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound542`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound545`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound546`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound551`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound553`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound564`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound566`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound580`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound584`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound587`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound588`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound589`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound632`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound787`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound813`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound865`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound93`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound944`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound945`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound946`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound949`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound950`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound951`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound952`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound97`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound991`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound992`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound993` and `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1914`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw182Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw182step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw182step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw182step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw182step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw183 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]

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

def raw1823 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![-2, 3, -1]]

def raw1823step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw1823step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1823step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw1823step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1823step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw1823step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1824 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![1, 0, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw1824Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1824step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw1824step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1824step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw1824step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1825 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![1, 0, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw1825Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1825step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw1825step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1826 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![1, 0, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw1826Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1826step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw1826step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1826step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw1826step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1826step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw1826step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1827 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, 0, -2], ![0, 1, -1], ![-2, 2, 0]]
def raw1827Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1827step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw1827step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1827step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw1827step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1828 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, 0, -2], ![0, 1, -1], ![-2, 2, 0]]
def raw1828Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1828step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw1828step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1829 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, 0, -2], ![0, 1, -1], ![-2, 2, 0]]
def raw1829Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1829step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw1829step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1829step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw1829step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1829step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw1829step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1830 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -3, 3], ![2, 0, -2], ![-2, 3, -1]]
def raw1830Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1830step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw1830step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1830step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw1830step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1831 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -3, 3], ![2, 0, -2], ![-2, 3, -1]]
def raw1831Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1831step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw1831step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1832 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -3, 3], ![2, 0, -2], ![-2, 3, -1]]
def raw1832Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1832step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![-1, -2, 3], ![-2, 2, 0]]
def raw1832step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1832step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![2, -2, 0]]
def raw1832step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1832step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![2, -2, 0]]
def raw1832step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1833 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -2, 2], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw1833Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1833step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw1833step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1833step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw1833step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1834 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -2, 2], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw1834Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1834step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw1834step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1835 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -2, 2], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw1835Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1835step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw1835step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1835step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw1835step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1835step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw1835step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

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

def raw18220 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18220Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18220step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw18220step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18221Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18221step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw18221step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18222 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18222Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18222step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw18222step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw18223Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18223step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw18223step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18223step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw18223step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18223step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18223step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18224 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18224Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18224step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18224step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18224step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18224step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18224step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18224step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18225 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18225Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18225step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18225step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18225step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18225step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18226 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18226Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18227 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![2, 0, -2]]
def raw18227Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18227step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18227step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18228 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw18228Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18228step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw18228step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18229 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw18229Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18229step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw18229step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18230 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw18230Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18230step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18230step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18230step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18230step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18230step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18230step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18231 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw18231Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18231step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw18231step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18231step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw18231step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw18232Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18232step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18232step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18233 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw18233Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18233step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw18233step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18234 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw18234Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18234step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw18234step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18234step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw18234step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18235 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw18235Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18235step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw18235step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18235step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18235step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18236 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw18236Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18236step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw18236step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18236step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw18236step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18237 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![0, 0, 0], ![3, -1, -2]]
def raw18237Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18237step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![3, -1, -2]]
def raw18237step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18237step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw18237step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18237step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18237step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18238 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18238Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18238step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw18238step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18238step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw18238step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18239 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18239Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18239step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18239step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18239step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18239step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18240 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18240Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18240step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18240step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18240step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18240step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18241 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw18241Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18241step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw18241step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18241step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18241step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18241step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18241step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18242 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18242Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18242step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18242step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18242step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18242step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18243 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18243Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18243step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18243step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18243step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw18243step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18243step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18243step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18243step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18243step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18244 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18244Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18244step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18244step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18244step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw18244step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18244step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18244step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18244step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18244step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18245 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw18245Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18245step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw18245step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18245step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw18245step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18245step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18245step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18245step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18245step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18246 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18246Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18246step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw18246step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18246step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw18246step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18246step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw18246step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18247 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18247Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18247step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw18247step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18247step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw18247step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18248Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18248step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw18248step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18248step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw18248step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18249 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw18249Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18249step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw18249step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18249step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18249step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18249step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18249step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18250Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18250step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18250step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18250step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18250step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18250step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18250step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18251 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18251Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18251step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw18251step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18251step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18251step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18251step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18251step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18252 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18252Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18252step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18252step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18252step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18252step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18253 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![2, 0, -2]]
def raw18253Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18253step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18253step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18253step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18253step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18253step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18253step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18254 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw18254Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18254step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw18254step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18254step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw18254step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18254step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw18254step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18255 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw18255Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18255step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw18255step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18255step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw18255step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18256 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw18256Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18256step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18256step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18256step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18256step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18257 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw18257Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18257step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw18257step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18257step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw18257step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18257step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw18257step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18258 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw18258Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18258step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw18258step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18258step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw18258step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18258step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw18258step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18259 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw18259Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18259step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw18259step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18259step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw18259step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18260 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw18260Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18260step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw18260step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18260step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw18260step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18261 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw18261Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18261step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18261step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18261step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18261step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18262 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw18262Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18262step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw18262step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18262step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw18262step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18263 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![0, 0, 0], ![3, -1, -2]]
def raw18263Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18263step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![3, -1, -2]]
def raw18263step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18263step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18263step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18263step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18263step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18264 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18264Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18264step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18264step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18264step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18264step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18264step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18264step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18265 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18265Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18265step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw18265step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18265step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18265step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18265step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18265step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18266 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18266Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18266step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18266step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18266step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18266step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18267 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw18267Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18267step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18267step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18267step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18267step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18268 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18268Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18268step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18268step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18269 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18269Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18269step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw18269step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18269step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18269step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18269step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18269step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18270 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18270Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18270step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18270step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18270step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18270step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18271 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18271Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18271step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw18271step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18271step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18271step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18271step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18271step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18272 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw18272Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18272step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18272step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18272step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18272step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18273 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18273Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18273step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw18273step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18273step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18273step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18273step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18273step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18274 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18274Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18274step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw18274step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18274step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw18274step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18274step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw18274step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18275 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18275Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18275step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw18275step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18275step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw18275step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18276 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18276Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18276step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw18276step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18276step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw18276step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18277 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw18277Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18277step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18277step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18277step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18277step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18278 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18278Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18278step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18278step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18278step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18278step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18278step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18278step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18279 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18279Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18279step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18279step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18279step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18279step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18280 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18280Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18280step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18280step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18280step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18280step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18281 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18281Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18281step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18281step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18281step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18281step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18282 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw18282Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18282step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18282step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18282step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18282step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18283 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18283Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18283step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18283step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18283step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18283step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18284 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw18284Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18284step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw18284step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18284step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw18284step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18285 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw18285Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18285step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw18285step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18285step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw18285step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18286 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw18286Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18286step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw18286step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18286step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18286step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18286step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18286step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18287 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -2, 0]]
def raw18287Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18287step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw18287step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18287step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw18287step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18287step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw18287step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18288 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw18288Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18288step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18288step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18288step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18288step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18289 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw18289Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18289step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw18289step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18289step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw18289step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18290 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw18290Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18290step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw18290step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18290step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw18290step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18290step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw18290step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18291 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw18291Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18291step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw18291step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18291step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18291step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18291step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18291step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18292 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw18292Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18292step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw18292step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18292step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw18292step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18293 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw18293Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18293step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18293step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18293step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18293step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18294 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18294Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18294step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18294step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18294step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18294step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18294step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw18294step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18294step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18294step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18295 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18295Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18295step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18295step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18295step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw18295step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18295step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18295step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18296 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18296Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18296step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18296step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18296step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw18296step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18296step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18296step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18297 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw18297Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18297step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw18297step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18297step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw18297step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18297step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![2, 0, -2]]
def raw18297step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18297step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw18297step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18297step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw18297step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18298 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18298Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18298step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18298step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18298step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18298step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18298step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw18298step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18298step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw18298step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18299 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18299Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18299step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18299step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18300 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18300Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18300step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18300step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18301 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw18301Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18301step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw18301step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18301step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18301step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18302 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18302Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18302step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18302step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18303 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18303Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18303step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18303step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical143
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw18304 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18304Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18305 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw18305Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18305step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18305step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18305step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18305step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18306 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw18306Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18306step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw18306step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18306step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![2, 0, -2]]
def raw18306step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18307 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw18307Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18307step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw18307step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18307step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw18307step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18307step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18307step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18308 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw18308Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18308step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw18308step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18308step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw18308step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18308step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18308step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18309 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw18309Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18309step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw18309step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18309step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw18309step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18309step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18309step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18310 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw18310Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18310step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw18310step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18310step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![3, -1, -2]]
def raw18310step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18310step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw18310step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18310step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw18310step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18311 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw18311Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18311step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw18311step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18311step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw18311step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18311step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18311step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18312 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw18312Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18312step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw18312step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18312step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw18312step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18312step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18312step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18313 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18313Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18313step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18313step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18313step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18313step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18313step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18313step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18314 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18314Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18314step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18314step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18314step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18314step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18315 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18315Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18315step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18315step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18315step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18315step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18315step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18315step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18316 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw18316Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18316step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw18316step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18316step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18316step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18316step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18316step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18317 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18317Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18317step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18317step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18317step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw18317step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18317step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18317step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18317step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18317step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18318 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18318Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18318step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18318step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18318step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18318step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18319 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18319Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18319step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw18319step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18320 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18320Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18320step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw18320step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18321 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw18321Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18321step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18321step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18322Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18322step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18322step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18322step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18322step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18322step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18322step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18323 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18323Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18323step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18323step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18324 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18324Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18324step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw18324step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18324step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18324step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18325 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![2, 0, -2]]
def raw18325Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18325step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![2, 0, -2]]
def raw18325step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18325step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18325step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18326 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18326Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18326step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18326step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18327 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw18327Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18327step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw18327step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18327step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw18327step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18327step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw18327step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18328 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw18328Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18328step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw18328step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18328step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18328step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18329 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw18329Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18329step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw18329step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18329step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw18329step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18329step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw18329step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18330 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 1, -2]]
def raw18330Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18330step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![1, 1, -2]]
def raw18330step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18330step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18330step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18331 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw18331Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18331step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw18331step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18331step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw18331step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18331step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw18331step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18332 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw18332Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18332step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw18332step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18332step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18332step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18333 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw18333Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18333step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw18333step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18333step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw18333step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18333step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw18333step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18334 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw18334Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18334step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw18334step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18334step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw18334step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18334step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18334step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18335 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw18335Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18335step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw18335step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18335step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw18335step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw18336 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw18336Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18336step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![-1, 1], ![1, -1], ![2, -2]]
def raw18336step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw18336step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw18336step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw18337 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw18337Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18337step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw18337step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18337step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw18337step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw18338 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw18338Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18338step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw18338step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw18339 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0]]
def raw18339Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18339step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0]]
def raw18339step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18339step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![2, -2, 0], ![2, -2, 0]]
def raw18339step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18339step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![2, -2]]
def raw18339step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw18340 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0]]
def raw18340Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18340step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw18340step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18340step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![2, -2], ![2, -2]]
def raw18340step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw18340step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![2, -2], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw18340step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw18340step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw18340step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw18341 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw18341Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18341step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw18341step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18341step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![2, -2], ![2, -2]]
def raw18341step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw18341step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![2, -2], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw18341step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw18341step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw18341step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw18342 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -3, 0]]
def raw18342Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18342step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![3, -3, 0]]
def raw18342step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18342step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![1, -1, 0], ![3, -3, 0]]
def raw18342step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18342step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![3, -3]]
def raw18342step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw18342step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-2, 2], ![-2, 2]]
def raw18342step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw18342step4 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw18342step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw18343 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -3, 0]]
def raw18343Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18343step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw18343step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18343step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![3, -3]]
def raw18343step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw18343step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw18343step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw18343step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw18343step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw18344 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw18344Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18344step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw18344step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18344step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![3, -3]]
def raw18344step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw18344step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw18344step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw18344step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw18344step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw18345 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18345Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18345step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18345step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18345step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18345step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18345step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18345step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18346 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18346Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18346step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw18346step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18346step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw18346step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18347 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw18347Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18347step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18347step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18347step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18347step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18347step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw18347step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18347step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw18347step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18348 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw18348Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18348step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw18348step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18348step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw18348step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18348step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18348step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18348step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18348step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18349 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18349Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18349step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18349step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18349step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18349step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18350 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw18350Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18350step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18350step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18351 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw18351Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18351step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18351step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18352 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18352Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18352step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18352step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18352step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18352step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18352step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18352step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18353 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18353Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18353step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw18353step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18353step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18353step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18353step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18353step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18354 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![1, 1, -2]]
def raw18354Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18354step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw18354step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18354step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw18354step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18354step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18354step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18355 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![0, 2, -2]]
def raw18355Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18355step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![0, 2, -2]]
def raw18355step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18355step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw18355step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18355step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw18355step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18355step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw18355step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18356 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw18356Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18356step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw18356step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18356step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18356step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18356step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18356step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18357 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw18357Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18357step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw18357step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18357step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18357step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18357step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18357step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18358 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![0, 2, -2]]
def raw18358Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18358step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![0, 2, -2]]
def raw18358step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18358step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw18358step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18358step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw18358step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18358step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw18358step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18359 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18359Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18359step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18359step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18359step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18359step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18359step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18359step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18360 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18360Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18360step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18360step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18360step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18360step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18360step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18360step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18361 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18361Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18361step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18361step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18361step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw18361step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18361step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18361step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18361step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18361step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18362 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw18362Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18362step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18362step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18362step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw18362step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18362step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18362step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18362step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18362step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18363 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw18363Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18363step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18363step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18363step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18363step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18363step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18363step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18364 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18364Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18364step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18364step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18365 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18365Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18365step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18365step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18366 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18366Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18366step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18366step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18366step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18366step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18367 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw18367Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18367step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18367step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18367step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18367step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18368 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw18368Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18368step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18368step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18369 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18369Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18369step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw18369step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18369step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw18369step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18370 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18370Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18370step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18370step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18370step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18370step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18370step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18370step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18371 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![1, 0, -1]]
def raw18371Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18371step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw18371step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18371step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18371step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18372 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![0, 1, -1]]
def raw18372Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18372step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw18372step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18372step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18372step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18372step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18372step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18373 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw18373Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18373step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw18373step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18373step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw18373step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18374 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw18374Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18374step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18374step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18374step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18374step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18374step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18374step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18375 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1]]
def raw18375Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18375step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw18375step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18375step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18375step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18376 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![0, 1, -1]]
def raw18376Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18376step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw18376step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18376step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18376step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18376step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18376step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18377 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18377Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18377step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18377step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18377step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18377step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18378 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18378Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18379 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18379Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18379step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18379step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18380 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw18380Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18380step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18380step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18381 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18381Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18381step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18381step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18381step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18381step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18382Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18382step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18382step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw18383Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18383step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18383step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw18384Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18384step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18384step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18384step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw18384step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18384step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18384step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18385 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18385Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18385step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18385step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18385step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18385step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18386 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18386Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18386step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18386step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18386step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18386step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18387 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw18387Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18387step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw18387step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18387step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18387step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18387step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18387step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18388 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw18388Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18388step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18388step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18388step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw18388step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18388step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw18388step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18389 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18389Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18389step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18389step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18389step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18389step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18390 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18390Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18390step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18390step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18390step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18390step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18391 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw18391Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18391step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18391step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18391step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18391step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18391step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18391step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18392 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw18392Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18392step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18392step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18392step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18392step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18392step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18392step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18393 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18393Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18393step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18394Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall2904 : Fin 2 → Fin 1 := ![0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end


