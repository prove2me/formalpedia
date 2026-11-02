-- Prove2me | Definitions.Def_OAIQ106D065
-- name    : OAIQ106D065
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T12:29:27.196753+00:00
-- url     : https://prove2.me/theorems/a87b26c8-b6ad-475d-8dd5-33c9357a7200
-- title:
--   Definitions bundle OAIQ106D065 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1779 declarations of OpenAI's Lean: 1779 definitions. The definitions and types are `OAI.MUB6.Certificate.PairSemantics.raw8289`, `OAI.MUB6.Certificate.PairSemantics.raw8289step0`, `OAI.MUB6.Certificate.PairSemantics.raw8289step1`, `OAI.MUB6.Certificate.PairSemantics.raw828step0`, `OAI.MUB6.Certificate.PairSemantics.raw829`, `OAI.MUB6.Certificate.PairSemantics.raw8290`, `OAI.MUB6.Certificate.PairSemantics.raw8290step0`, `OAI.MUB6.Certificate.PairSemantics.raw8290step1`, `OAI.MUB6.Certificate.PairSemantics.raw8291`, `OAI.MUB6.Certificate.PairSemantics.raw8291step0`, `OAI.MUB6.Certificate.PairSemantics.raw8291step1`, `OAI.MUB6.Certificate.PairSemantics.raw8292`, `OAI.MUB6.Certificate.PairSemantics.raw8292step0`, `OAI.MUB6.Certificate.PairSemantics.raw8292step1`, `OAI.MUB6.Certificate.PairSemantics.raw8293`, `OAI.MUB6.Certificate.PairSemantics.raw8293step0`, `OAI.MUB6.Certificate.PairSemantics.raw8293step1`, `OAI.MUB6.Certificate.PairSemantics.raw8294`, `OAI.MUB6.Certificate.PairSemantics.raw8294step0`, `OAI.MUB6.Certificate.PairSemantics.raw8294step1`, `OAI.MUB6.Certificate.PairSemantics.raw8294step2`, `OAI.MUB6.Certificate.PairSemantics.raw8295`, `OAI.MUB6.Certificate.PairSemantics.raw8295step0`, `OAI.MUB6.Certificate.PairSemantics.raw8295step1`, `OAI.MUB6.Certificate.PairSemantics.raw8296`, `OAI.MUB6.Certificate.PairSemantics.raw8296step0`, `OAI.MUB6.Certificate.PairSemantics.raw8296step1`, `OAI.MUB6.Certificate.PairSemantics.raw8296step2`, `OAI.MUB6.Certificate.PairSemantics.raw8297`, `OAI.MUB6.Certificate.PairSemantics.raw8297step0`, `OAI.MUB6.Certificate.PairSemantics.raw8297step1`, `OAI.MUB6.Certificate.PairSemantics.raw8298`, `OAI.MUB6.Certificate.PairSemantics.raw8298step0`, `OAI.MUB6.Certificate.PairSemantics.raw8298step1`, `OAI.MUB6.Certificate.PairSemantics.raw8299`, `OAI.MUB6.Certificate.PairSemantics.raw8299step0`, `OAI.MUB6.Certificate.PairSemantics.raw8299step1`, `OAI.MUB6.Certificate.PairSemantics.raw829step0`, `OAI.MUB6.Certificate.PairSemantics.raw82step0`, `OAI.MUB6.Certificate.PairSemantics.raw82step1` and 1739 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_Cubic_CubicPattern`, `MutuallyUnbiased_PairSemantics_Canonical2`, `MutuallyUnbiased_PairSemantics_Canonical25`, `MutuallyUnbiased_PairSemantics_Canonical259`, `MutuallyUnbiased_PairSemantics_Canonical26`, `MutuallyUnbiased_PairSemantics_Canonical260`, `MutuallyUnbiased_PairSemantics_Canonical261`, `MutuallyUnbiased_PairSemantics_Canonical262`, `MutuallyUnbiased_PairSemantics_Canonical263`, `MutuallyUnbiased_PairSemantics_Canonical264`, `MutuallyUnbiased_PairSemantics_Canonical265`, `MutuallyUnbiased_PairSemantics_Canonical266`, `MutuallyUnbiased_PairSemantics_Canonical267`, `MutuallyUnbiased_PairSemantics_Canonical268`, `MutuallyUnbiased_PairSemantics_Canonical269`, `MutuallyUnbiased_PairSemantics_Canonical27`, `MutuallyUnbiased_PairSemantics_Canonical270`, `MutuallyUnbiased_PairSemantics_Canonical271`, `MutuallyUnbiased_PairSemantics_Canonical272`, `MutuallyUnbiased_PairSemantics_Canonical273`, `MutuallyUnbiased_PairSemantics_Canonical274`, `MutuallyUnbiased_PairSemantics_Canonical275`, `MutuallyUnbiased_PairSemantics_Canonical276`, `MutuallyUnbiased_PairSemantics_Canonical277`, `MutuallyUnbiased_PairSemantics_Canonical278`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ106D140`; the statement `OAI.MUB6.Certificate.PairSemantics.canonical845`; the proof of `OAI.MUB6.Certificate.PairSemantics.canonical845`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Cubic_CubicPattern
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! From cubed row-ratio patterns to the single three-by-three exceptional block. -/

noncomputable section

namespace MUB6

def nonOneSupport (f : Fin 6 → ℂ) : Finset (Fin 6) := by
  classical
  exact Finset.univ.filter (fun i => f i ≠ 1)

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw82step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]

def raw82step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 2, -3]]

def raw83 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]

def raw83step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 3, -4]]

def raw84 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]

def raw84step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 3, -4]]

def raw85 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]

def raw85step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-3, 3, 0]]

def raw85step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]

def raw86 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]

def raw86step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 3, -4]]

def raw87 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]

def raw87step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]

def raw87step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

def raw88 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw828step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]

def raw829 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

def raw829step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]

def raw830 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]

def raw830step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]

def raw831 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]

def raw831step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, 0, 1], ![-2, 0, 2]]

def raw831step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical259
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8289 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -3, 4], ![0, 1, 1, -2], ![0, 1, 1, -2], ![0, -1, 1, 0]]

def raw8289step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![1, 1, -2], ![1, 1, -2], ![-1, 1, 0]]

def raw8289step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2]]

def raw8290 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, -2, 3], ![-1, 0, 2, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0]]

def raw8290step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 2, -3], ![1, 0, -2, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 1, 0, 0]]

def raw8290step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -2, 0, 1]]

def raw8291 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -2, 3], ![-1, 0, 2, -1], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def raw8291step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 2, -3], ![1, 0, -2, 1], ![0, -2, 0, 2], ![-1, 1, 0, 0]]

def raw8291step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -2, 0, 1]]

def raw8292 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -2, 3], ![-1, 1, -1, 1], ![0, 1, 1, -2], ![1, -1, 2, -2]]

def raw8292step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 2, -3], ![1, -1, 1, -1], ![0, -1, -1, 2], ![-1, 1, -2, 2]]

def raw8292step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, -1, -1, 2], ![0, 1, 2, -3], ![1, -1, 1, -1]]

def raw8293 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -2, 3], ![-1, 1, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw8293step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 2, -3], ![1, -1, -1, 1], ![0, -1, -1, 2], ![-1, 1, 0, 0]]

def raw8293step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -1, 2], ![0, 2, 1, -3], ![1, -1, -1, 1]]

def raw8294 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, -2, 3], ![-1, 2, 3, -4], ![1, -1, -1, 1]]

def raw8294step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 2, -1], ![-2, 3, -1], ![3, -4, 1]]

def raw8294step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![1, -2, 1], ![2, -3, 1], ![-3, 4, -1]]

def raw8294step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 0, 1], ![1, 1, -2], ![1, 2, -3]]

def raw8295 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, -2, 3], ![0, -1, 2, -1], ![0, 2, 0, -2]]

def raw8295step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![2, 0, -2]]

def raw8295step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]

def raw8296 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, -2, 3], ![0, -1, 3, -2], ![0, 2, -1, -1]]

def raw8296step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, 2, -3], ![0, 1, -3, 2], ![0, -2, 1, 1]]

def raw8296step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![1, -3, 2], ![-2, 1, 1]]

def raw8296step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -3, 2], ![1, 2, -3]]

def raw8297 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, -2, 3], ![0, 0, 1, -1], ![-1, 1, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0]]

def raw8297step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 2, -3], ![0, 0, -1, 1], ![1, -1, -1, 1], ![0, -1, 0, 1], ![-1, 1, 0, 0]]

def raw8297step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, -1, 1]]

def raw8298 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -2, 3], ![0, 0, 1, -1], ![-1, 2, 1, -2], ![1, -1, 0, 0]]

def raw8298step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 2, -1], ![-2, 1, 1, 0], ![3, -1, -2, 0]]

def raw8298step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw8299 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, -2, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-1, 1, 1, -1], ![1, -1, 0, 0]]

def raw8299step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 2, -3], ![0, 0, -1, 1], ![0, -1, 0, 1], ![1, -1, -1, 1], ![-1, 1, 0, 0]]

def raw8299step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, -1, 1]]

def raw8300 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, -2, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![0, -1, 1, 0]]

def raw8300step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0]]

def raw8300step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw8301 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -2, 3], ![0, 0, 1, -1], ![0, 2, 0, -2], ![0, -1, 1, 0]]

def raw8301step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![2, 0, -2], ![-1, 1, 0]]

def raw8301step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw8302 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, -2, 3], ![0, 0, 4, -4], ![0, 1, -2, 1]]

def raw8302step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 4, -4], ![1, -2, 1]]

def raw8303 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -2, 3], ![0, 1, 0, -1], ![-1, 1, 2, -2], ![1, -1, 0, 0]]

def raw8303step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, 1, -1], ![-2, 0, 2, 0], ![3, -1, -2, 0]]

def raw8303step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, 1, -1]]

def raw8304 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -2, 3], ![0, 1, 0, -1], ![0, 1, 1, -2], ![0, -1, 1, 0]]

def raw8304step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![1, 0, -1], ![1, 1, -2], ![-1, 1, 0]]

def raw8304step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw8305 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, -2, 3], ![0, 1, 3, -4], ![0, 0, -1, 1]]

def raw8305step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, 2, -3], ![0, -1, -3, 4], ![0, 0, 1, -1]]

def raw8305step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![-1, -3, 4], ![0, 1, -1]]

def raw8305step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![1, 2, -3]]

def raw8306 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, -2, 3], ![0, 2, 2, -4], ![0, -1, 0, 1]]

def raw8306step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 0, 0], ![-1, 2, -1], ![-2, 2, 0], ![3, -4, 1]]

def raw8306step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 0, 0], ![1, -2, 1], ![2, -2, 0], ![-3, 4, -1]]

def raw8306step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -2, 1], ![2, -2, 0], ![-3, 4, -1]]

def raw8306step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![1, 1, -2]]

def raw8307 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -1, 2], ![-1, -1, 0, 2], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw8307step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw8308 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -1, 2], ![-1, -1, 1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw8308step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw8309 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -1, 2], ![-1, 1, 3, -3], ![0, 1, -2, 1], ![1, -1, 0, 0]]

def raw8309step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 1, 1, -1], ![-1, 3, -2, 0], ![2, -3, 1, 0]]

def raw8309step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -2, 3], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def raw8310 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, -1, 2], ![-1, 2, 2, -3], ![1, -1, -1, 1]]

def raw8310step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 2, -1], ![-1, 2, -1], ![2, -3, 1]]

def raw8310step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![-2, 3, -1]]

def raw8310step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]

def raw8311 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, -1, -1, 2], ![0, 2, 2, -4]]

def raw8311step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, 1, -2], ![0, 1, 1, -2], ![0, -2, -2, 4]]

def raw8311step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-2, -2, 4]]

def raw8311step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![1, 1, -2], ![1, 1, -2]]

def raw8312 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, -1, 0, 1], ![-1, 2, 2, -3], ![1, 0, -1, 0]]

def raw8312step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 2, 0], ![-1, 0, 2, -1], ![2, 1, -3, 0]]

def raw8312step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, 1, -2, 0], ![1, 0, -2, 1], ![-2, -1, 3, 0]]

def raw8312step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 0, 1], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw8313 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, -1, 0, 1], ![0, 2, 2, -4], ![0, 0, -1, 1]]

def raw8313step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 1, -2], ![0, 1, 0, -1], ![0, -2, -2, 4], ![0, 0, 1, -1]]

def raw8313step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-2, -2, 4], ![0, 1, -1]]

def raw8313step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw8314 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, -1, 1, 0], ![-1, 2, 1, -2], ![1, 0, -1, 0]]

def raw8314step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 2, 0], ![-1, 1, 1, -1], ![2, 0, -2, 0]]

def raw8314step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, -1, 1]]

def raw8315 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, -1, 1, 0], ![0, 2, 1, -3], ![0, 0, -1, 1]]

def raw8315step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 1, -2], ![0, 1, -1, 0], ![0, -2, -1, 3], ![0, 0, 1, -1]]

def raw8315step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![-2, -1, 3], ![0, 1, -1]]

def raw8315step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw8316 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, -1, 2, -1], ![0, 2, -1, -1]]

def raw8316step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, 1, -2], ![0, 1, -2, 1], ![0, -2, 1, 1]]

def raw8316step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 1, -2], ![1, -2, 1], ![-2, 1, 1]]

def raw8316step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 1, -2]]

def raw8317 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, -1, 3, -2], ![0, 2, -2, 0]]

def raw8317step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 3, -2], ![2, -2, 0]]

def raw8317step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]

def raw8318 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![-2, 0, 2, 0], ![1, 2, 1, -4]]

def raw8318step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 1, -2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![2, 0, -2, 0], ![-1, -2, -1, 4]]

def raw8318step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw8319 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![-2, 1, 1, 0], ![1, 1, 2, -4]]

def raw8319step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 1, 2, -4]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw832 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]

def raw832step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

def raw833 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]

def raw833step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]

def raw834 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]

def raw834step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]

def raw835 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]

def raw835step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]

def raw835step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw836 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]

def raw836step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]

def raw836step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2]]

def raw837 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]

def raw837step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]

def raw838 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![2, 1, -3]]

def raw838step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![2, -3, 1]]

def raw839 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]

def raw839step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]

def raw840 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 1, -2], ![2, -3, 1]]

def raw840step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -3, 2], ![1, 2, -3]]

def raw841 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, 2, 1], ![3, -2, -1]]

def raw841step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![1, -1]]

def raw841step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw842 : Matrix (Fin 2) (Fin 4) ℤ := ![![-3, 2, 2, -1], ![3, -2, -2, 1]]

def raw842step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![2, -2], ![-1, 1]]

def raw842step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]

def raw843 : Matrix (Fin 2) (Fin 4) ℤ := ![![-3, 2, 3, -2], ![3, -2, -3, 2]]

def raw843step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![3, -3], ![-2, 2]]

def raw843step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![2, -2], ![3, -3]]

def raw844 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![0, 0], ![1, -1], ![1, -1], ![3, -3]]

def raw844step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![3, -3]]

def raw845 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![0, 0], ![1, -1], ![2, -2], ![2, -2]]

def raw845step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![2, -2], ![2, -2]]

def raw846 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![0, 0], ![2, -2], ![3, -3]]

def raw846step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![2, -2], ![3, -3]]

def raw847 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]

def raw848 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![3, -3]]

def raw849 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![2, -2], ![2, -2]]

def raw850 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![4, -4]]

def raw850step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![2, -2], ![3, -3]]

def raw851 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![2, -2], ![1, -1], ![2, -2]]

def raw851step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![2, -2], ![2, -2]]

def raw852 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![2, -2], ![3, -3]]

def raw853 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![3, -3], ![2, -2]]

def raw853step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![2, -2], ![3, -3]]

def raw854 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![3, -3]]

def raw855 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2], ![2, -2]]

def raw856 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![-1, 1], ![2, -2], ![3, -3]]

def raw856step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![3, -3]]

def raw857 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![0, 0], ![0, 0], ![1, -1], ![3, -3]]

def raw857step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![0, 0], ![1, -1], ![3, -3]]

def raw857step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]

def raw858 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![0, 0], ![0, 0], ![2, -2], ![2, -2]]

def raw858step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![0, 0], ![2, -2], ![2, -2]]

def raw858step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]

def raw859 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![0, 0], ![1, -1], ![1, -1], ![2, -2]]

def raw859step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]

def raw860 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![0, 0], ![1, -1], ![3, -3]]

def raw860step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]

def raw861 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![0, 0], ![2, -2], ![2, -2]]

def raw861step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]

def raw863 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![0, 0], ![1, -1], ![2, -2]]

def raw863step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical260
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8320 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![-2, 2, 0, 0], ![1, 0, 3, -4]]

def raw8320step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 1, -2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![2, -2, 0, 0], ![-1, 0, -3, 4]]

def raw8320step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -3, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw8321 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, -1, 1, 2], ![2, 1, 0, -3]]

def raw8321step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 1, -2], ![0, 0, 1, -1], ![0, 0, -1, 1], ![0, -1, 0, 1], ![2, 1, -1, -2], ![-2, -1, 0, 3]]

def raw8321step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, 1, -1, -2]]

def raw8322 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, 1, 0, 1], ![2, -1, 1, -2]]

def raw8322step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 1, -2], ![0, 0, 1, -1], ![0, 0, -1, 1], ![0, -1, 0, 1], ![2, -1, 0, -1], ![-2, 1, -1, 2]]

def raw8322step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def raw8323 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 2, 1, -1]]

def raw8323step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 1, -2], ![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![2, -2, -1, 1]]

def raw8323step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw8324 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, 0, 1, 1], ![1, 1, 2, -4]]

def raw8324step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw8325 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, 1, 0, 1], ![1, 0, 3, -4]]

def raw8325step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw8326 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 1, 3, -2]]

def raw8326step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw8327 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 1, 2, -1]]

def raw8327step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 1, -2], ![0, 0, 1, -1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![2, -1, -2, 1]]

def raw8327step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw8328 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, 1, 0, 1], ![1, -1, 2, -2]]

def raw8328step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 1, -2], ![0, 0, 1, -1], ![0, -1, 0, 1], ![-1, 0, 0, 1], ![2, -1, 0, -1], ![-1, 1, -2, 2]]

def raw8328step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw8329 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 0, 1, 1], ![0, 2, 2, -4]]

def raw8329step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 1, -2], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![2, 0, -1, -1], ![0, -2, -2, 4]]

def raw8329step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw8330 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![0, 1, 3, -4]]

def raw8330step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw8331 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![-2, -1, 0, 3], ![2, 1, 0, -3]]

def raw8331step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, -1, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, 0, -3]]

def raw8332 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 2, 0, 0]]

def raw8332step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 1, -2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![2, -2, 0, 0]]

def raw8332step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def raw8333 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 1, 1, 0]]

def raw8333step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw8334 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 1, 1, 0]]

def raw8334step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw8335 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![0, 2, 1, -3]]

def raw8335step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 1, -2], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![2, 0, 0, -2], ![0, -2, -1, 3]]

def raw8335step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw8336 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 0, 0, -1], ![0, -1, 2, -1], ![-2, 2, -2, 2]]

def raw8336step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, -1, 2], ![0, -1, 2, -1], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw8337 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 0, 3, -3], ![0, 1, -2, 1]]

def raw8337step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 3, -3], ![1, -2, 1]]

def raw8338 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 0, 4, -4], ![0, 1, -3, 2]]

def raw8338step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, 1, -2], ![0, 0, -4, 4], ![0, -1, 3, -2]]

def raw8338step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 1, -2], ![0, -4, 4], ![-1, 3, -2]]

def raw8338step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 4, -4], ![1, -2, 1]]

def raw8339 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, 0, 0, 2], ![1, 0, 3, -4]]

def raw8339step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw8340 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 0, 2, 0]]

def raw8340step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 1, -2], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![2, 0, -2, 0]]

def raw8340step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw8341 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![0, 1, 3, -4]]

def raw8341step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw8342 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 2, 1, -3], ![0, -1, 0, 1]]

def raw8342step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, 1, -2], ![0, -2, -1, 3], ![0, 1, 0, -1]]

def raw8342step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 1, -2], ![-2, -1, 3], ![1, 0, -1]]

def raw8342step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![1, 1, -2]]

def raw8343 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw8343step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw8344 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, 0, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw8344step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw8345 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, 0, 2], ![0, 2, 2, -4], ![1, 0, -2, 1]]

def raw8345step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, 2, 0], ![0, 0, 2, -2], ![1, 2, -4, 1]]

def raw8345step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![1, 1, -2, 0], ![0, 0, -2, 2], ![-1, -2, 4, -1]]

def raw8345step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 1, 0, -2]]

def raw8346 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw8346step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw8347 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, 1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw8347step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw8348 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, 1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-1, 0, -1, 2], ![1, 1, 2, -4]]

def raw8348step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![1, 1, -1, -1], ![0, -1, 1, 0], ![-1, 0, 1, 0], ![1, 0, 1, -2], ![-1, -1, -2, 4]]

def raw8348step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 0, 1, 0], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def raw8349 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, 1, 1], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def raw8349step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, 2, 0], ![0, 1, 1, -2], ![1, 1, -3, 1]]

def raw8349step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![1, 1, -2, 0], ![0, -1, -1, 2], ![-1, -1, 3, -1]]

def raw8349step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw8350 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, 1, 1], ![0, 2, 2, -4], ![1, 0, -3, 2]]

def raw8350step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, 2, 0], ![0, 1, 2, -3], ![1, 1, -4, 2]]

def raw8350step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![1, 1, -2, 0], ![0, -1, -2, 3], ![-1, -1, 4, -2]]

def raw8350step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 3, -2], ![0, 1, -1, 0], ![1, 1, 0, -2]]

def raw8351 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, 2, 0], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw8351step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 2, -2, 0], ![1, 0, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical261
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8352 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, 2, 0], ![0, 2, 1, -3], ![1, 0, -3, 2]]

def raw8352step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 2, -3, 1], ![1, 0, 2, -3]]

def raw8353 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-1, -1, 2, 0], ![2, 1, 1, -4]]

def raw8353step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![1, 0, 1, -2], ![0, 0, 1, -1], ![0, -1, 1, 0], ![1, 1, -2, 0], ![-2, -1, -1, 4]]

def raw8353step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -2, 0]]

def raw8354 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, -1, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![-1, 2, -1, 0], ![1, 0, 3, -4]]

def raw8354step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![1, 0, 1, -2], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![1, -2, 1, 0], ![-1, 0, -3, 4]]

def raw8354step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -3, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw8355 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, -1, 2], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def raw8355step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 0, 1], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def raw8356 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, -1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![-1, -1, 1, 1], ![2, 0, 2, -4]]

def raw8356step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![1, 0, 1, -2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![1, 1, -1, -1], ![-2, 0, -2, 4]]

def raw8356step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def raw8357 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, -1, 2], ![0, 2, -2, 0], ![1, -1, 3, -3]]

def raw8357step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 2, -1], ![0, -1, -2, 3], ![1, 2, 0, -3]]

def raw8357step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![1, 0, -2, 1], ![0, 1, 2, -3], ![-1, -2, 0, 3]]

def raw8357step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, 0, -2, 1]]

def raw8358 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, -1, 2], ![0, 2, 2, -4], ![1, -1, -1, 1]]

def raw8358step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 2, -1], ![0, -1, 2, -1], ![1, 2, -4, 1]]

def raw8358step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![1, 0, -2, 1], ![0, 1, -2, 1], ![-1, -2, 4, -1]]

def raw8358step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw8359 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 0, 1], ![0, 2, 1, -3], ![1, -1, -1, 1]]

def raw8359step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 2, -1], ![0, 0, 1, -1], ![1, 1, -3, 1]]

def raw8359step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![1, 0, -2, 1], ![0, 0, -1, 1], ![-1, -1, 3, -1]]

def raw8359step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw8360 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw8360step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw8361 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw8361step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw8362 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 1, 0], ![0, 2, -3, 1], ![1, -1, 2, -2]]

def raw8362step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 2, -1], ![0, 1, -3, 2], ![1, 0, 1, -2]]

def raw8362step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![1, 0, -2, 1], ![0, -1, 3, -2], ![-1, 0, -1, 2]]

def raw8362step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw8363 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 2, -1], ![0, 1, -2, 1], ![1, 0, 0, -1]]

def raw8363step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw8364 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 2, -1], ![0, 1, -1, 0], ![1, 0, -1, 0]]

def raw8364step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw8365 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 2, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def raw8365step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, 0, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def raw8366 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 2, -1], ![0, 2, -3, 1], ![1, -1, 1, -1]]

def raw8366step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, -1, 1]]

def raw8367 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 2, -1], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def raw8367step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 1, -1, -1]]

def raw8368 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 2, -1], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw8368step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, 0, 1], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw8369 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 2, -1], ![0, 2, 1, -3], ![1, -1, -3, 3]]

def raw8369step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, 0, 1], ![0, 2, 1, -3], ![1, -1, -3, 3]]

def raw8370 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 3, -2], ![0, 2, -3, 1], ![1, -1, 0, 0]]

def raw8370step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 2, -1], ![0, 3, -3, 0], ![1, -2, 1, 0]]

def raw8370step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, 0, -1, 0]]

def raw8371 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 3, -2], ![0, 2, -2, 0], ![1, -1, -1, 1]]

def raw8371step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 1, -1, -1]]

def raw8372 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 3, -2], ![0, 2, 0, -2], ![1, -1, -3, 3]]

def raw8372step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 3, -2], ![0, -1, 0, 1], ![0, 2, 0, -2], ![1, -1, -3, 3]]

def raw8373 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 1, -3, 3], ![0, 1, 2, -3], ![1, -1, 1, -1]]

def raw8373step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 1, 1, -1], ![0, -3, 2, 1], ![1, 3, -3, -1]]

def raw8373step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, -1, -3, 3]]

def raw8374 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 1, -3, 3], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def raw8374step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 1, 1, -1], ![0, -3, 3, 0], ![1, 3, -4, 0]]

def raw8374step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -3, 3], ![0, 1, -1, 0], ![1, 0, 3, -4]]

def raw8375 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 1, -1, 1], ![0, 1, -2, 1], ![1, -1, 3, -3]]

def raw8375step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 1, 1, -1], ![0, -1, -2, 3], ![1, 1, 1, -3]]

def raw8375step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![1, -1, -1, 1], ![0, 1, 2, -3], ![-1, -1, -1, 3]]

def raw8375step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, -1, 1]]

def raw8376 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 1, -1, 1], ![0, 1, 2, -3], ![1, -1, -1, 1]]

def raw8376step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 1, 1, -1], ![0, -1, 2, -1], ![1, 1, -3, 1]]

def raw8376step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![1, -1, -1, 1], ![0, 1, -2, 1], ![-1, -1, 3, -1]]

def raw8376step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def raw8377 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 1, 1, -1], ![0, 1, 1, -2], ![1, -1, -2, 2]]

def raw8377step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, 0, 1], ![0, 1, 1, -2], ![1, -1, -2, 2]]

def raw8378 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, -2, 3], ![0, 2, 2, -4]]

def raw8378step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 0, 0], ![-1, -1, 2], ![0, -2, 2], ![1, 3, -4]]

def raw8378step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 0, 0], ![1, 1, -2], ![0, 2, -2], ![-1, -3, 4]]

def raw8378step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![-1, -3, 4]]

def raw8378step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![1, 1, -2]]

def raw8379 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-2, 0, 2, 0], ![2, 1, 1, -4]]

def raw8379step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 1, -2], ![0, 0, 1, -1], ![0, -1, 1, 0], ![2, 0, -2, 0], ![-2, -1, -1, 4]]

def raw8379step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -2, 0]]

def raw8380 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 0, 2, 0], ![1, 2, 1, -4]]

def raw8380step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 1, -2], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![2, 0, -2, 0], ![-1, -2, -1, 4]]

def raw8380step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw8381 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 1, 1, 0], ![1, 1, 2, -4]]

def raw8381step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw8382 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 2, 0, 0], ![1, 0, 3, -4]]

def raw8382step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 1, -2], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![2, -2, 0, 0], ![-1, 0, -3, 4]]

def raw8382step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -3, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw8383 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![-2, 0, 1, 1], ![2, 0, 2, -4]]

def raw8383step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 1, -2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![2, 0, -1, -1], ![-2, 0, -2, 4]]

def raw8383step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical262
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8384 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-2, 0, 1, 1], ![1, 1, 2, -4]]

def raw8384step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw8385 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![1, 0, 3, -4]]

def raw8385step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 3, -4]]

def raw8386 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, -1, 2], ![0, 2, 1, -3]]

def raw8386step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 1, -2], ![0, -2, -1, 3]]

def raw8386step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 0, -1], ![1, 1, -2], ![-2, -1, 3]]

def raw8386step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![1, 1, -2]]

def raw8387 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, -1, 2], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-2, 0, 1, 1], ![0, 2, 2, -4]]

def raw8387step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 1, -2], ![-1, 0, 1, 0], ![-1, 0, 1, 0], ![2, 0, -1, -1], ![0, -2, -2, 4]]

def raw8387step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw8388 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, -1, 2], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![0, 1, 3, -4]]

def raw8388step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, -1, 0, 1], ![0, 1, 3, -4], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw8389 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 0, -1, 2], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw8389step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -1, 0, 0]]

def raw8390 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 1, -1, 1], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw8390step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, 0, 0]]

def raw8391 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 2, 2, -3], ![1, 0, -2, 1]]

def raw8391step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 2, 0], ![0, 0, 2, -2], ![1, 1, -3, 1]]

def raw8391step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, 1, -2, 0], ![0, 0, -2, 2], ![-1, -1, 3, -1]]

def raw8391step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, 0, -2]]

def raw8392 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![-1, 2, 2, -3], ![1, 0, -1, 0]]

def raw8392step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 0, -1], ![0, 0, 1, -1], ![1, -2, -2, 3], ![-1, 0, 1, 0]]

def raw8392step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -2, 3]]

def raw8393 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![0, 0, -1, 1]]

def raw8393step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 0, -1], ![0, 0, 1, -1], ![0, -2, -2, 4], ![0, 0, 1, -1]]

def raw8393step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![-2, -2, 4], ![0, 1, -1]]

def raw8393step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw8394 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![-1, 1, 2, -2], ![1, 0, -1, 0]]

def raw8394step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw8395 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![0, 0, -1, 1]]

def raw8395step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 0, -1], ![0, -1, 1, 0], ![0, -1, -2, 3], ![0, 0, 1, -1]]

def raw8395step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, -2, 3], ![0, 1, -1]]

def raw8395step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw8396 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 2, 1, -3], ![0, 0, -1, 1]]

def raw8396step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 0, -1], ![0, -2, -1, 3], ![0, 0, 1, -1]]

def raw8396step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![-2, -1, 3], ![0, 1, -1]]

def raw8396step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw8397 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 2, 2, -4], ![0, 0, -2, 2]]

def raw8397step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 0, -1], ![0, -2, -2, 4], ![0, 0, 2, -2]]

def raw8397step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![-2, -2, 4], ![0, 2, -2]]

def raw8397step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

def raw8398 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![-1, 0, -1, 2], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw8398step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def raw8399 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![-1, 1, -1, 1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw8399step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw8400 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![-1, 1, -1, 1], ![1, 0, -1, 0], ![-1, 0, -1, 2], ![1, 1, 2, -4]]

def raw8400step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![-1, 0, 1, 0], ![1, 0, 1, -2], ![-1, -1, -2, 4]]

def raw8400step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 0, 1, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def raw8401 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![-1, 2, 1, -2], ![1, 0, -2, 1]]

def raw8401step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 2, 0], ![0, 1, 1, -2], ![1, 0, -2, 1]]

def raw8401step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 0, 1, -2]]

def raw8402 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![-1, 2, 2, -3], ![1, 0, -3, 2]]

def raw8402step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 2, 0], ![0, 1, 2, -3], ![1, 0, -3, 2]]

def raw8402step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -3, 2], ![1, 0, 2, -3]]

def raw8403 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![-1, 2, 1, -2], ![1, 0, -1, 0]]

def raw8403step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw8404 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 2, 1, -3], ![0, 0, -1, 1]]

def raw8404step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, -1, 0], ![0, 0, 1, -1], ![0, -2, -1, 3], ![0, 0, 1, -1]]

def raw8404step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![1, -1, 0], ![0, 1, -1], ![-2, -1, 3], ![0, 1, -1]]

def raw8404step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw8405 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![-1, 1, 1, -1], ![1, 0, -1, 0]]

def raw8405step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw8406 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 0, -1, 1], ![-1, 0, -1, 2], ![1, 1, 2, -4]]

def raw8406step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, -1, 0], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 0, 1, -2], ![-1, -1, -2, 4]]

def raw8406step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw8407 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 1, -2], ![0, 0, -1, 1]]

def raw8407step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![0, -1, 1]]

def raw8407step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw8408 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-2, 0, -1, 3], ![1, 1, 2, -4]]

def raw8408step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw8409 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-1, 0, -1, 2], ![0, 1, 2, -3]]

def raw8409step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw8410 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 2, 1, -3], ![0, 0, -2, 2]]

def raw8410step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, -1, 0], ![0, -2, -1, 3], ![0, 0, 2, -2]]

def raw8410step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, -1, 0], ![-2, -1, 3], ![0, 2, -2]]

def raw8410step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw8411 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 2, 2, -4], ![0, 0, -3, 3]]

def raw8411step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, -1, 0], ![0, -2, -2, 4], ![0, 0, 3, -3]]

def raw8411step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, -1, 0], ![-2, -2, 4], ![0, 3, -3]]

def raw8411step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw8412 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 2, -1], ![-1, 2, 0, -1], ![1, 0, -2, 1]]

def raw8412step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, -2, 1], ![1, -2, 0, 1], ![-1, 0, 2, -1]]

def raw8412step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw8413 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 2, -1], ![-1, 2, 1, -2], ![1, 0, -3, 2]]

def raw8413step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 2, 0], ![0, 2, 1, -3], ![1, -1, -2, 2]]

def raw8413step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 2, -3, 1], ![1, -1, 2, -2]]

def raw8414 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 2, -1], ![0, 2, -2, 0]]

def raw8414step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![2, -2, 0]]

def raw8414step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![1, -1, 0]]

def raw8415 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 2, -1], ![0, 2, 0, -2], ![0, 0, -2, 2]]

def raw8415step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![0, -2, 2]]

def raw8415step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical263
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8416 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 2, -1], ![0, 2, 1, -3], ![0, 0, -3, 3]]

def raw8416step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, -2, 1], ![0, -2, -1, 3], ![0, 0, 3, -3]]

def raw8416step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, -2, 1], ![-2, -1, 3], ![0, 3, -3]]

def raw8416step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

def raw8417 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 3, -2], ![0, 2, -3, 1]]

def raw8417step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 0, 0], ![-1, -1, 2], ![0, 3, -3], ![1, -2, 1]]

def raw8417step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 3, -3], ![1, -2, 1]]

def raw8418 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![-1, 0, -1, 2], ![0, 1, -1, 0], ![-1, -1, 2, 0], ![2, 1, 1, -4]]

def raw8418step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![1, 0, 1, -2], ![0, -1, 1, 0], ![1, 1, -2, 0], ![-2, -1, -1, 4]]

def raw8418step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -2, 0]]

def raw8419 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![-1, 0, -1, 2], ![1, -1, 0, 0], ![-1, 2, -1, 0], ![1, 0, 3, -4]]

def raw8419step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![1, 0, 1, -2], ![-1, 1, 0, 0], ![1, -2, 1, 0], ![-1, 0, -3, 4]]

def raw8419step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -3, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw8420 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![-1, 0, 3, -2], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def raw8420step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw8421 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![-1, 1, -1, 1], ![0, 1, -1, 0], ![-1, -1, 1, 1], ![2, 0, 2, -4]]

def raw8421step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![0, -1, 1, 0], ![1, 1, -1, -1], ![-2, 0, -2, 4]]

def raw8421step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw8422 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![-1, 2, -2, 1], ![1, -1, 3, -3]]

def raw8422step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 2, -1], ![0, -1, -2, 3], ![1, 1, 1, -3]]

def raw8422step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, 0, -2, 1], ![0, 1, 2, -3], ![-1, -1, -1, 3]]

def raw8422step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 0, 2, -3]]

def raw8423 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![-1, 2, 2, -3], ![1, -1, -1, 1]]

def raw8423step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 2, -1], ![0, -1, 2, -1], ![1, 1, -3, 1]]

def raw8423step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, 0, -2, 1], ![0, 1, -2, 1], ![-1, -1, 3, -1]]

def raw8423step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw8424 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![-2, 0, 2, 0], ![2, 1, 1, -4]]

def raw8424step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![0, -1, 1, 0], ![2, 0, -2, 0], ![-2, -1, -1, 4]]

def raw8424step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -2, 0]]

def raw8425 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, -1, -1, 2], ![1, 0, -1, 0], ![-2, 0, 2, 0], ![1, 2, 1, -4]]

def raw8425step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![-1, 0, 1, 0], ![2, 0, -2, 0], ![-1, -2, -1, 4]]

def raw8425step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw8426 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, -1, -1, 2], ![1, 0, -1, 0], ![-2, 1, 1, 0], ![1, 1, 2, -4]]

def raw8426step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw8427 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, -1, -1, 2], ![1, 0, -1, 0], ![-2, 2, 0, 0], ![1, 0, 3, -4]]

def raw8427step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![-1, 0, 1, 0], ![2, -2, 0, 0], ![-1, 0, -3, 4]]

def raw8427step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -3, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw8428 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 1, -1, 1], ![-1, -1, 2, 0], ![2, 1, 1, -4]]

def raw8428step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 1, -2, 0], ![-2, -1, -1, 4]]

def raw8428step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def raw8429 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, -1, 0, 1], ![-1, 2, -1, 0], ![1, 0, 3, -4]]

def raw8429step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 1, 0], ![-1, 0, -3, 4]]

def raw8429step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, 1, 0]]

def raw8430 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![-2, 0, 2, 0], ![2, 1, 1, -4]]

def raw8430step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![2, 0, -2, 0], ![-2, -1, -1, 4]]

def raw8430step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw8431 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-2, -1, 2, 1], ![2, 1, 1, -4]]

def raw8431step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -1, 1, 0], ![2, 1, -2, -1], ![-2, -1, -1, 4]]

def raw8431step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -2, -1]]

def raw8432 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-2, 0, 1, 1], ![2, 0, 2, -4]]

def raw8432step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw8433 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-2, 0, 2, 0], ![2, 0, 1, -3]]

def raw8433step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw8434 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-1, -1, 2, 0], ![1, 1, 1, -3]]

def raw8434step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -1, 1, 0], ![1, 1, -2, 0], ![-1, -1, -1, 3]]

def raw8434step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -2, 0]]

def raw8435 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![-2, 0, 2, 0], ![1, 2, 1, -4]]

def raw8435step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 1, -1], ![2, 0, -2, 0], ![-1, -2, -1, 4]]

def raw8435step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw8436 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![-2, 1, 1, 0], ![1, 1, 2, -4]]

def raw8436step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, 1, 2, -4]]

def raw8437 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![-2, 2, 0, 0], ![1, 0, 3, -4]]

def raw8437step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 1, -1], ![2, -2, 0, 0], ![-1, 0, -3, 4]]

def raw8437step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -3, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw8438 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![-2, 2, -1, 1], ![1, 0, 3, -4]]

def raw8438step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw8439 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![-1, 2, -1, 0], ![0, 0, 3, -3]]

def raw8439step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![1, -2, 1, 0], ![0, 0, -3, 3]]

def raw8439step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -3, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 1, 0]]

def raw8440 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, -1, 2, 1], ![1, 2, 1, -4]]

def raw8440step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![2, 1, -2, -1], ![-1, -2, -1, 4]]

def raw8440step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 2, -2, -1]]

def raw8441 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 0, 1, 1], ![1, 1, 2, -4]]

def raw8441step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![2, 0, -1, -1], ![-1, -1, -2, 4]]

def raw8441step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw8442 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 0, 2, 0], ![1, 1, 1, -3]]

def raw8442step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![2, 0, -2, 0], ![-1, -1, -1, 3]]

def raw8442step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw8443 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![1, 0, 3, -4]]

def raw8443step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def raw8444 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 1, 1, 0], ![1, 0, 2, -3]]

def raw8444step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def raw8445 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 2, 0, 0], ![1, -1, 3, -3]]

def raw8445step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw8446 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, 3, -3], ![-1, 2, -2, 1], ![1, -1, 0, 0]]

def raw8446step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![0, 0, -3, 3], ![1, -2, 2, -1], ![-1, 1, 0, 0]]

def raw8446step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -3, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 2, -1]]

def raw8447 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, 3, -3], ![0, 2, -2, 0], ![0, -1, 0, 1]]

def raw8447step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![0, 0, -3, 3], ![0, -2, 2, 0], ![0, 1, 0, -1]]

def raw8447step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![0, 1, -1], ![0, -3, 3], ![-2, 2, 0], ![1, 0, -1]]

def raw8447step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical264
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8448 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-1, 1, -1, 1], ![-1, -1, 1, 1], ![2, 0, 2, -4]]

def raw8448step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![0, -1, 1, 0], ![1, -1, 1, -1], ![1, 1, -1, -1], ![-2, 0, -2, 4]]

def raw8448step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw8449 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 0, -1, 1], ![-2, 0, 1, 1], ![2, 0, 2, -4]]

def raw8449step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw8450 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![-2, -1, 1, 2], ![2, 0, 2, -4]]

def raw8450step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 2, -4]]

def raw8451 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![-2, 0, 1, 1], ![2, -1, 2, -3]]

def raw8451step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 2, -3]]

def raw8452 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![-1, -1, 1, 1], ![1, 0, 2, -3]]

def raw8452step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 2, -3]]

def raw8453 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![-2, 0, 1, 1], ![1, 1, 2, -4]]

def raw8453step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 2, -4]]

def raw8454 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![-2, 1, 0, 1], ![1, 0, 3, -4]]

def raw8454step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 3, -4]]

def raw8455 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-2, -1, 1, 2], ![1, 1, 2, -4]]

def raw8455step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw8456 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![1, 0, 3, -4]]

def raw8456step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, 0, -1, 0]]

def raw8457 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-2, 0, 1, 1], ![1, 0, 2, -3]]

def raw8457step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw8458 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![1, -1, 3, -3]]

def raw8458step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw8459 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, -2, 0], ![0, -1, 3, -2]]

def raw8459step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![-1, 3, -2]]

def raw8459step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw8460 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![0, -1, 0, 1]]

def raw8460step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![0, -2, -1, 3], ![0, 1, 0, -1]]

def raw8460step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, 1, -1], ![-2, -1, 3], ![1, 0, -1]]

def raw8460step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw8461 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![0, -1, -1, 2]]

def raw8461step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![0, -2, -2, 4], ![0, 1, 1, -2]]

def raw8461step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, 1, -1], ![-2, -2, 4], ![1, 1, -2]]

def raw8461step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw8462 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, 0, -1, 0], ![-2, 0, 1, 1], ![0, 2, 2, -4]]

def raw8462step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![-1, 1, 1, -1], ![-1, 0, 1, 0], ![2, 0, -1, -1], ![0, -2, -2, 4]]

def raw8462step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw8463 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![0, 1, 3, -4]]

def raw8463step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw8464 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, -1, -1, 1], ![-2, 0, 1, 1], ![0, 2, 2, -4]]

def raw8464step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![-1, 1, 1, -1], ![2, 0, -1, -1], ![0, -2, -2, 4]]

def raw8464step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw8465 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, -1, -1, 1], ![-2, 1, 0, 1], ![0, 1, 3, -4]]

def raw8465step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw8466 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-2, -1, 1, 2], ![0, 2, 2, -4]]

def raw8466step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw8467 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![0, 1, 3, -4]]

def raw8467step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![-1, 0, 1, 0], ![2, 0, 0, -2], ![0, -1, -3, 4]]

def raw8467step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw8468 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-2, 0, 1, 1], ![0, 1, 2, -3]]

def raw8468step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![-1, 0, 1, 0], ![2, 0, -1, -1], ![0, -1, -2, 3]]

def raw8468step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw8469 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![0, 0, 3, -3]]

def raw8469step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, 3, -3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 0, 1]]

def raw8470 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw8470step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw8471 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 1, -1], ![-1, 1, -1, 1], ![1, 0, 0, -1]]

def raw8471step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw8472 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 1, -1], ![-1, 1, 1, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def raw8472step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def raw8473 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 1, -1], ![-1, 2, -3, 2], ![1, -1, 2, -2]]

def raw8473step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 2, -1], ![0, 1, -3, 2], ![1, -1, 2, -2]]

def raw8473step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, 0, -2, 1], ![0, -1, 3, -2], ![-1, 1, -2, 2]]

def raw8473step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, -1, 2, -2]]

def raw8474 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 1, -1], ![-1, 2, 1, -2], ![1, -1, -2, 2]]

def raw8474step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 2, -1], ![0, 1, 1, -2], ![1, -1, -2, 2]]

def raw8474step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 2, -2]]

def raw8475 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 1, -1], ![-1, 2, 2, -3], ![1, -1, -3, 3]]

def raw8475step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 2, -1], ![0, 1, 2, -3], ![1, -1, -3, 3]]

def raw8475step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, 0, -2, 1], ![0, -1, -2, 3], ![-1, 1, 3, -3]]

def raw8475step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 3, -3]]

def raw8476 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 2, 0, -1], ![1, -1, -2, 2]]

def raw8476step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -1, 2]]

def raw8477 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![0, -1, -2, 3]]

def raw8477step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2], ![-1, -2, 3]]

def raw8477step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def raw8478 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 0, 0, 0]]

def raw8478step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, -1, 0]]

def raw8478step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![1, -1, 0]]

def raw8479 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-1, 1, 1, -1], ![1, -1, -2, 2]]

def raw8479step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical265
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8480 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![0, -1, -1, 2]]

def raw8480step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-1, -1, 2]]

def raw8480step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw8481 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, -3, 1], ![0, -1, 2, -1]]

def raw8481step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, -1, 1], ![0, -2, 3, -1], ![0, 1, -2, 1]]

def raw8481step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -1, 1], ![-2, 3, -1], ![1, -2, 1]]

def raw8481step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw8482 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![0, -1, -1, 2]]

def raw8482step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![-1, -1, 2]]

def raw8482step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

def raw8483 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, 1, -3], ![0, -1, -2, 3]]

def raw8483step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![2, 1, -3], ![-1, -2, 3]]

def raw8483step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3]]

def raw8484 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 2, -2], ![-1, 1, -2, 2], ![1, 0, 0, -1]]

def raw8484step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, -2, 2], ![1, -1, 2, -2], ![-1, 0, 0, 1]]

def raw8484step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 2, -2]]

def raw8485 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 2, -2], ![-1, 1, -1, 1], ![1, 0, -1, 0]]

def raw8485step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 1, 0], ![0, 2, -1, -1], ![1, -2, 1, 0]]

def raw8485step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw8486 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 2, -2], ![-1, 1, 0, 0], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def raw8486step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -2, -1, 2]]

def raw8487 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 2, -2], ![-1, 2, -3, 2], ![1, -1, 1, -1]]

def raw8487step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 2, -1], ![0, 2, -3, 1], ![1, -2, 2, -1]]

def raw8487step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, -1, -2, 2]]

def raw8488 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 2, -2], ![-1, 2, -1, 0], ![1, -1, -1, 1]]

def raw8488step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 2, -1], ![0, 2, -1, -1], ![1, -2, 0, 1]]

def raw8488step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, 0, -2, 1], ![0, -2, 1, 1], ![-1, 2, 0, -1]]

def raw8488step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw8489 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 2, -2], ![-1, 2, 0, -1], ![1, -1, -2, 2]]

def raw8489step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, -2, -1, 2]]

def raw8490 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 2, -2], ![-1, 2, 1, -2], ![1, -1, -3, 3]]

def raw8490step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 2, -1], ![0, 2, 1, -3], ![1, -2, -2, 3]]

def raw8490step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -2, -2, 3]]

def raw8491 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, -2, 1]]

def raw8491step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, -2, 2], ![0, -1, 2, -1]]

def raw8491step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 0, -1], ![0, -2, 2], ![-1, 2, -1]]

def raw8491step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![1, -1, 0]]

def raw8492 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, -2, 1], ![0, 0, 0, 0]]

def raw8492step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, -2, 2], ![0, -1, 2, -1], ![0, 0, 0, 0]]

def raw8492step1 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, -2, 2], ![0, -1, 2, -1]]

def raw8492step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 0, -1], ![0, -2, 2], ![-1, 2, -1]]

def raw8492step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![1, -1, 0]]

def raw8493 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 0, -1, 1]]

def raw8493step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![0, -1, 1]]

def raw8493step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0]]

def raw8494 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![-1, 1, 0, 0], ![1, -1, -2, 2]]

def raw8494step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -2, -1, 2]]

def raw8495 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![0, -1, -2, 3]]

def raw8495step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![-1, -2, 3]]

def raw8495step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

def raw8496 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 2, -3, 1], ![0, -1, 1, 0]]

def raw8496step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, -2, 2], ![0, -2, 3, -1], ![0, 1, -1, 0]]

def raw8496step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -2, 2], ![-2, 3, -1], ![1, -1, 0]]

def raw8496step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw8497 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 2, -1, -1], ![0, -1, -1, 2]]

def raw8497step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, -2, 2], ![0, -2, 1, 1], ![0, 1, 1, -2]]

def raw8497step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -2, 2], ![-2, 1, 1], ![1, 1, -2]]

def raw8497step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw8498 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 2, 0, -2], ![0, -1, -2, 3]]

def raw8498step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 2, -2], ![2, 0, -2], ![-1, -2, 3]]

def raw8498step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]

def raw8499 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 3, -3], ![-1, 2, -3, 2], ![1, -1, 0, 0]]

def raw8499step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 2, -1], ![0, 3, -3, 0], ![1, -3, 2, 0]]

def raw8499step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 1, -3, 2], ![1, 0, 0, -1]]

def raw8500 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 3, -3], ![-1, 2, -2, 1], ![1, -1, -1, 1]]

def raw8500step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 2, -1], ![0, 3, -2, -1], ![1, -3, 1, 1]]

def raw8500step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, 0, -2, 1], ![0, -3, 2, 1], ![-1, 3, -1, -1]]

def raw8500step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 1, 2, -3], ![1, 1, -2, 0]]

def raw8501 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 3, -3], ![0, 1, -3, 2]]

def raw8501step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, -3, 3], ![0, -1, 3, -2]]

def raw8501step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 0, -1], ![0, -3, 3], ![-1, 3, -2]]

def raw8501step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 3, -3], ![1, -1, 0]]

def raw8502 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 3, -3], ![0, 2, -3, 1], ![0, -1, 0, 1]]

def raw8502step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, -3, 3], ![0, -2, 3, -1], ![0, 1, 0, -1]]

def raw8502step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -3, 3], ![-2, 3, -1], ![1, 0, -1]]

def raw8502step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def raw8503 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 3, -3], ![0, 2, -2, 0], ![0, -1, -1, 2]]

def raw8503step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, -3, 3], ![0, -2, 2, 0], ![0, 1, 1, -2]]

def raw8503step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -3, 3], ![-2, 2, 0], ![1, 1, -2]]

def raw8503step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -2, 1], ![1, -1, 0]]

def raw8504 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 1, -3, 2], ![-1, 1, 2, -2], ![1, -1, 1, -1]]

def raw8504step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, 1, -1], ![0, -3, 2, 1], ![1, 2, -2, -1]]

def raw8504step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -3, 2], ![0, 1, 0, -1], ![1, -1, 2, -2]]

def raw8505 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 1, -3, 2], ![-1, 1, 3, -3], ![1, -1, 0, 0]]

def raw8505step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, 1, -1], ![0, -3, 3, 0], ![1, 2, -3, 0]]

def raw8505step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -3, 3], ![0, 1, 0, -1], ![1, 0, 2, -3]]

def raw8506 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 1, -3, 2], ![0, 1, 2, -3], ![0, -1, 1, 0]]

def raw8506step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, -1, 3, -2], ![0, -1, -2, 3], ![0, 1, -1, 0]]

def raw8506step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-1, 3, -2], ![-1, -2, 3], ![1, -1, 0]]

def raw8506step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1]]

def raw8507 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 1, -3, 2], ![0, 1, 3, -4], ![0, -1, 0, 1]]

def raw8507step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, -1, 3, -2], ![0, -1, -3, 4], ![0, 1, 0, -1]]

def raw8507step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-1, 3, -2], ![-1, -3, 4], ![1, 0, -1]]

def raw8507step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 3, -2], ![1, 0, -1], ![1, 0, -1]]

def raw8508 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 1, -1, 0], ![-1, 1, 2, -2], ![1, -1, -1, 1]]

def raw8508step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, 1, -1], ![0, -1, 2, -1], ![1, 0, -2, 1]]

def raw8508step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, -1, -1, 1], ![0, 1, -2, 1], ![-1, 0, 2, -1]]

def raw8508step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw8509 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![1, 0, 3, -4]]

def raw8509step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, 0, -1, 0]]

def raw8510 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, -1, 1], ![-2, 0, 0, 2], ![1, 0, 3, -4]]

def raw8510step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 3, -4]]

def raw8511 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-2, -1, 0, 3], ![1, 0, 3, -4]]

def raw8511step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 3, -4]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical266
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8512 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![1, -1, 3, -3]]

def raw8512step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw8513 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![0, -1, -1, 2]]

def raw8513step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, -1, 1, 0], ![0, -1, -2, 3], ![0, 1, 1, -2]]

def raw8513step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-1, 1, 0], ![-1, -2, 3], ![1, 1, -2]]

def raw8513step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw8514 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![0, 1, 3, -4]]

def raw8514step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw8515 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, -1, -1, 1], ![-2, 0, 0, 2], ![0, 1, 3, -4]]

def raw8515step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw8516 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-2, -1, 0, 3], ![0, 1, 3, -4]]

def raw8516step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw8517 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![0, 0, 3, -3]]

def raw8517step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 0, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0]]

def raw8518 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 1, 0, -1], ![-1, 1, 2, -2], ![1, -1, -2, 2]]

def raw8518step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, 1, -1], ![0, 0, 2, -2], ![1, -1, -2, 2]]

def raw8518step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, -1, 1, -1]]

def raw8519 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![0, -1, -1, 2]]

def raw8519step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![-1, -1, 2]]

def raw8519step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2]]

def raw8520 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![-1, 3, -2], ![2, 1, -3]]

def raw8520step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![1, 1, -2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![-2, -1, 3]]

def raw8520step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 1, -2]]

def raw8521 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0]]

def raw8521step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0]]

def raw8522 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![-2, 3, -1], ![2, 1, -3]]

def raw8522step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![2, -3, 1], ![-2, -1, 3]]

def raw8522step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]

def raw8523 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![-1, 4, -3]]

def raw8523step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw8524 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-1, 3, -2]]

def raw8524step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 3, -2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]

def raw8525 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![-2, 4, -2]]

def raw8525step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]

def raw8526 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw8526step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw8527 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

def raw8527step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

def raw8528 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![-2, 0, 2], ![2, 2, -4]]

def raw8528step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![2, 0, -2], ![-2, -2, 4]]

def raw8528step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

def raw8529 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-1, 2, -1]]

def raw8529step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw8530 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![-1, -1, 2], ![1, 2, -3]]

def raw8530step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![-1, -2, 3]]

def raw8530step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

def raw8531 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![0, 3, -3], ![1, -1, 0]]

def raw8531step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0]]

def raw8532 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![0, 4, -4], ![1, -2, 1]]

def raw8532step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 4, -4], ![1, -2, 1]]

def raw8533 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![1, 3, -4]]

def raw8533step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]

def raw8534 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![-1, -1, 2], ![0, 4, -4]]

def raw8534step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0], ![1, 0, -1]]

def raw8536 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![-1, -1, 2], ![0, 3, -3]]

def raw8536step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

def raw8537 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0]]

def raw8537step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]

def raw8538 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![-2, -1, 3], ![2, 1, -3]]

def raw8538step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]

def raw8539 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![-1, -2, 3], ![1, 2, -3]]

def raw8539step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def raw8540 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-1, -1, 2]]

def raw8540step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw8541 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![-1, -2, 3], ![0, 3, -3]]

def raw8541step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw8542 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 1, 0], ![1, 0, -1]]

def raw8542step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![1, -1, 0]]

def raw8543 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![-2, 3, -1], ![1, -3, 2]]

def raw8543step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical267
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8544 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![-1, 3, -2], ![0, -3, 3]]

def raw8544step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def raw8545 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 2, -1], ![1, -1, 0]]

def raw8545step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![1, 0, -1]]

def raw8546 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 3, -2], ![0, -2, 2], ![1, 0, -1]]

def raw8546step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

def raw8547 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 4, -3], ![0, -3, 3], ![1, 0, -1]]

def raw8547step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0]]

def raw8548 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -1, 1], ![0, -3, 3], ![0, 4, -4]]

def raw8548step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-3, 3], ![4, -4]]

def raw8548step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![3, -3]]

def raw8549 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![-2, 2, 0], ![2, 1, -3]]

def raw8549step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![-2, -1, 3]]

def raw8549step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

def raw8550 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-2, 4, -2]]

def raw8550step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]

def raw8551 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![-3, 1, 2], ![3, 0, -3]]

def raw8551step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![3, -1, -2], ![-3, 0, 3]]

def raw8551step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]

def raw8552 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![-2, 0, 2], ![2, 1, -3]]

def raw8552step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![-2, -1, 3]]

def raw8552step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

def raw8553 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1], ![2, 0, -2]]

def raw8553step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![-2, 0, 2]]

def raw8553step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

def raw8555 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![-2, 0, 2], ![1, 3, -4]]

def raw8555step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 3, -4]]

def raw8556 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![-3, 1, 2], ![2, 1, -3]]

def raw8556step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]

def raw8557 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![-2, 0, 2], ![1, 2, -3]]

def raw8557step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 2, -3]]

def raw8558 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-2, 2, 0]]

def raw8558step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]

def raw8559 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2], ![-3, 2, 1]]

def raw8559step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]

def raw8560 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![0, 3, -3]]

def raw8560step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![3, -3]]

def raw8560step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw8561 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![-2, 0, 2], ![0, 4, -4]]

def raw8561step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0], ![1, 0, -1]]

def raw8562 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![-2, 1, 1], ![0, 3, -3]]

def raw8562step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw8563 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![-3, 1, 2], ![1, 2, -3]]

def raw8563step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]

def raw8564 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![-2, 0, 2], ![0, 3, -3]]

def raw8564step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

def raw8565 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![-1, -1, 2], ![-1, 4, -3]]

def raw8565step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 4, -3], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]

def raw8566 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![-3, 3, 0]]

def raw8566step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![3, -3, 0]]

def raw8566step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]

def raw8567 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![0, -1, 1], ![-1, 3, -2], ![2, 1, -3]]

def raw8567step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![0, 1, -1], ![1, -3, 2], ![-2, -1, 3]]

def raw8567step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 1, -2]]

def raw8568 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![0, 4, -4], ![1, -1, 0]]

def raw8568step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0]]

def raw8569 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![1, -1, 0], ![-2, 3, -1], ![2, 1, -3]]

def raw8569step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![-1, 1, 0], ![2, -3, 1], ![-2, -1, 3]]

def raw8569step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]

def raw8570 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![-1, 4, -3]]

def raw8570step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw8571 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![-1, 3, -2]]

def raw8571step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 3, -2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]

def raw8572 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![-2, 4, -2]]

def raw8572step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]

def raw8573 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1]]

def raw8573step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def raw8574 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0]]

def raw8574step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw8575 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![-2, 0, 2], ![2, 2, -4]]

def raw8575step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![-2, -2, 4]]

def raw8575step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical268
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8576 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![-1, 2, -1]]

def raw8576step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw8577 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![-1, -1, 2], ![1, 2, -3]]

def raw8577step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![-1, -2, 3]]

def raw8577step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw8578 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![-1, 3, -2], ![1, -1, 0]]

def raw8578step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw8579 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -2, 2], ![0, 1, -1], ![-2, 2, 0], ![2, 1, -3]]

def raw8579step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![0, -1, 1], ![2, -2, 0], ![-2, -1, 3]]

def raw8579step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

def raw8580 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![-2, 4, -2]]

def raw8580step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]

def raw8581 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-1, 3, -2], ![2, 1, -3]]

def raw8581step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![1, -3, 2], ![-2, -1, 3]]

def raw8581step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 1, -2]]

def raw8582 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 4, -3], ![1, -1, 0]]

def raw8582step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw8583 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 3, -1], ![2, 1, -3]]

def raw8583step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1]]

def raw8584 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 3, -2], ![1, 1, -2]]

def raw8584step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1]]

def raw8585 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![-1, 4, -3]]

def raw8585step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def raw8586 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![-2, 2, 0], ![2, 1, -3]]

def raw8586step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]

def raw8586step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![-2, -1, 3]]

def raw8586step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]

def raw8587 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![-1, 3, -2]]

def raw8587step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![-1, 3, -2]]

def raw8587step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def raw8588 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![-2, 4, -2]]

def raw8588step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![-2, 4, -2]]

def raw8588step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def raw8589 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![-2, 1, 1], ![2, 1, -3]]

def raw8589step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![-2, -1, 3]]

def raw8589step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def raw8590 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![-2, 2, 0], ![2, 0, -2]]

def raw8590step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]

def raw8592 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 4, -4], ![0, -1, 1]]

def raw8592step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![4, -4], ![-1, 1]]

def raw8592step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]

def raw8593 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![-3, 3, 0], ![2, 1, -3]]

def raw8593step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]

def raw8594 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![-2, 1, 1], ![1, 3, -4]]

def raw8594step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

def raw8595 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![-2, 3, -1], ![1, 1, -2]]

def raw8595step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]

def raw8596 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 4, -3]]

def raw8596step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 4, -3]]

def raw8596step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw8597 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![-2, 4, -2]]

def raw8597step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw8598 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![-1, -1, 2], ![0, 4, -4]]

def raw8598step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 4, -4], ![1, 0, -1]]

def raw8599 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![-1, 3, -2]]

def raw8599step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![-1, 3, -2]]

def raw8599step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def raw8600 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![-2, 4, -2]]

def raw8600step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw8601 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-2, 3, -1]]

def raw8601step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]

def raw8602 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![-3, 4, -1]]

def raw8602step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]

def raw8603 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![-3, 1, 2], ![3, 0, -3]]

def raw8603step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![-3, 1, 2], ![3, 0, -3]]

def raw8603step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![1, -3, 2], ![1, 0, -1]]

def raw8604 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![-2, 0, 2], ![2, 1, -3]]

def raw8604step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![-2, -1, 3]]

def raw8604step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2], ![-2, -1, 3]]

def raw8604step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

def raw8605 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![-2, 1, 1], ![2, 0, -2]]

def raw8605step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![-2, 0, 2]]

def raw8605step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![-2, 0, 2]]

def raw8605step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def raw8607 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![1, 3, -4]]

def raw8607step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![-2, 0, 2], ![1, 3, -4]]

def raw8607step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical269
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8608 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![-3, 1, 2], ![2, 1, -3]]

def raw8608step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2], ![-2, -1, 3]]

def raw8608step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![3, -1, -2], ![-2, -1, 3]]

def raw8608step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]

def raw8609 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![-2, 0, 2], ![1, 2, -3]]

def raw8609step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![-1, -2, 3]]

def raw8609step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![2, 0, -2], ![-1, -2, 3]]

def raw8609step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def raw8610 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![-1, -1, 2], ![0, 3, -3]]

def raw8610step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![-1, -1, 2], ![0, 3, -3]]

def raw8610step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1]]

def raw8611 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![-2, 2, 0]]

def raw8611step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-2, 2, 0]]

def raw8611step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]

def raw8612 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2], ![-3, 2, 1]]

def raw8612step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2], ![3, -2, -1]]

def raw8612step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2], ![3, -2, -1]]

def raw8612step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]

def raw8613 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1]]

def raw8613step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def raw8614 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0]]

def raw8614step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw8615 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, -1, 1], ![-2, 0, 2], ![2, 2, -4]]

def raw8615step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![-2, -2, 4]]

def raw8615step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

def raw8616 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![-1, 2, -1]]

def raw8616step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def raw8617 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![-3, 1, 2], ![3, 0, -3]]

def raw8617step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![-3, 1, 2], ![3, 0, -3]]

def raw8617step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![1, -3, 2], ![1, 0, -1]]

def raw8618 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![-2, 0, 2], ![2, 1, -3]]

def raw8618step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2], ![-2, -1, 3]]

def raw8618step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2], ![-2, -1, 3]]

def raw8618step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

def raw8619 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![-2, 1, 1], ![2, 0, -2]]

def raw8619step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![-2, 0, 2]]

def raw8619step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![-2, 0, 2]]

def raw8619step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def raw8620 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![1, 2, -3]]

def raw8620step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![-1, -2, 3]]

def raw8620step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![-1, -2, 3]]

def raw8620step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]

def raw8621 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-3, 0, 3], ![3, 0, -3]]

def raw8621step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -3, 3], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

def raw8622 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-3, 1, 2], ![3, -1, -2]]

def raw8622step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]

def raw8623 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-2, -1, 3], ![2, 1, -3]]

def raw8623step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, 1, -3]]

def raw8624 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 0, 2], ![2, 0, -2]]

def raw8624step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

def raw8625 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1], ![2, -1, -1]]

def raw8625step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def raw8626 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0]]

def raw8626step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1]]

def raw8626step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def raw8628 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![0, -1, 1]]

def raw8628step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![2, -2], ![-1, 1]]

def raw8628step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw8629 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![-2, 0, 2], ![1, 3, -4]]

def raw8629step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 3, -4]]

def raw8630 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![-3, 0, 3], ![2, 2, -4]]

def raw8630step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]

def raw8631 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![-3, 1, 2], ![2, 1, -3]]

def raw8631step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]

def raw8632 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![-2, -1, 3], ![1, 3, -4]]

def raw8632step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 3, -4]]

def raw8633 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![-2, 0, 2], ![1, 2, -3]]

def raw8633step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def raw8634 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1]]

def raw8634step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![-1, 2, -1]]

def raw8634step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw8635 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-2, 2, 0]]

def raw8635step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw8636 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![-3, 2, 1]]

def raw8636step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]

def raw8637 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-3, 0, 3], ![2, 1, -3]]

def raw8637step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![3, 0, -3], ![-2, -1, 3]]

def raw8637step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

def raw8638 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-3, 1, 2], ![2, 0, -2]]

def raw8638step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1]]

def raw8639 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-2, -1, 3], ![1, 2, -3]]

def raw8639step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 2, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw864 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![0, 0], ![3, -3]]

def raw864step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]

def raw866 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]

def raw867 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]

def raw868 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![2, -2], ![1, -1]]

def raw868step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]

def raw869 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]

def raw872 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]

def raw873 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![4, -4]]

def raw873step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![3, -3]]

def raw877 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![-1, 1], ![2, -2], ![2, -2]]

def raw877step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]

def raw879 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![0, 0], ![1, -1], ![2, -2]]

def raw879step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![1, -1], ![2, -2]]

def raw879step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![2, -2]]

def raw879step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw880 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![0, 0], ![2, -2], ![1, -1]]

def raw880step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![2, -2], ![1, -1]]

def raw880step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![2, -2], ![1, -1]]

def raw880step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![1, -1]]

def raw880step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw881 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![0, 0], ![3, -3]]

def raw881step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![3, -3]]

def raw881step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![3, -3]]

def raw881step2 : Matrix (Fin 2) (Fin 2) ℤ := ![![-3, 3], ![3, -3]]

def raw882 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![1, -1], ![0, 0], ![2, -2]]

def raw882step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![1, -1], ![2, -2]]

def raw882step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![2, -2]]

def raw882step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw883 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![1, -1], ![1, -1], ![1, -1]]

def raw883step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![1, -1], ![1, -1]]

def raw883step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

def raw884 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![1, -1], ![2, -2]]

def raw884step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![2, -2]]

def raw884step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw885 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![1, -1], ![2, -2], ![0, 0]]

def raw885step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![1, -1], ![2, -2]]

def raw885step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![2, -2]]

def raw885step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw886 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![2, -2], ![1, -1]]

def raw886step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![2, -2], ![1, -1]]

def raw886step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![1, -1]]

def raw886step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw887 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![3, -3]]

def raw887step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![3, -3]]

def raw887step1 : Matrix (Fin 2) (Fin 2) ℤ := ![![-3, 3], ![3, -3]]

def raw889 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![0, 0], ![0, 0], ![2, -2]]

def raw889step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![0, 0], ![2, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical270
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8640 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-2, 0, 2], ![1, 1, -2]]

def raw8640step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw8641 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-1, -1, 2], ![0, 2, -2]]

def raw8641step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

def raw8642 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![-2, 2, 0]]

def raw8642step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw8643 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-2, 1, 1]]

def raw8643step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw8644 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![-3, 2, 1]]

def raw8644step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]

def raw8645 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2], ![-3, 1, 2]]

def raw8645step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1]]

def raw8646 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![0, -1, 1]]

def raw8646step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![3, -3], ![-1, 1]]

def raw8646step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

def raw8647 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![-2, 0, 2], ![0, 4, -4]]

def raw8647step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 4, -4], ![1, -2, 1], ![1, 0, -1]]

def raw8648 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![-2, 1, 1], ![0, 3, -3]]

def raw8648step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw8649 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![1, 3, -4]]

def raw8649step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

def raw8650 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![0, 4, -4]]

def raw8650step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![-1, -1, 2], ![0, 4, -4]]

def raw8650step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0]]

def raw8651 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![-3, 1, 2], ![1, 3, -4]]

def raw8651step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]

def raw8652 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, 4, -4]]

def raw8652step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0], ![1, -1, 0]]

def raw8653 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, 3, -3]]

def raw8653step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw8654 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![-3, 1, 2], ![1, 2, -3]]

def raw8654step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]

def raw8655 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![-2, -1, 3], ![0, 4, -4]]

def raw8655step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0], ![1, 0, -1]]

def raw8656 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![-2, 0, 2], ![0, 3, -3]]

def raw8656step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw8657 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![-2, 1, 1], ![0, 2, -2]]

def raw8657step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw8658 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![-1, -1, 2], ![-1, 4, -3]]

def raw8658step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw8659 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![-3, 3, 0]]

def raw8659step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def raw8660 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![-1, -1, 2], ![0, 3, -3]]

def raw8660step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![-1, -1, 2], ![0, 3, -3]]

def raw8660step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1]]

def raw8662 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![-3, 1, 2], ![1, 2, -3]]

def raw8662step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]

def raw8663 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![0, 3, -3]]

def raw8663step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw8664 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![-1, -1, 2], ![-1, 4, -3]]

def raw8664step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw8665 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1], ![-3, 3, 0]]

def raw8665step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def raw8666 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-3, 0, 3], ![1, 2, -3]]

def raw8666step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![3, 0, -3], ![-1, -2, 3]]

def raw8666step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

def raw8667 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-3, 1, 2], ![1, 1, -2]]

def raw8667step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![3, -1, -2], ![-1, -1, 2]]

def raw8667step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 3, -2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]

def raw8668 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-2, -1, 3], ![0, 3, -3]]

def raw8668step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

def raw8669 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-2, 0, 2], ![0, 2, -2]]

def raw8669step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def raw8670 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-1, -2, 3], ![-1, 4, -3]]

def raw8670step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 4, -3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]

def raw8671 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-1, -1, 2], ![-1, 3, -2]]

def raw8671step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 3, -2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical271
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8672 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![-3, 3, 0]]

def raw8672step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def raw8673 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![-3, 2, 1]]

def raw8673step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![3, -2, -1]]

def raw8673step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]

def raw8674 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![-2, 1, 1], ![-1, -1, 2], ![3, 0, -3]]

def raw8674step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![-2, 1, 1], ![-1, -1, 2], ![3, 0, -3]]

def raw8674step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

def raw8675 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![-3, 0, 3], ![2, 1, -3]]

def raw8675step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![-1, 1, 0], ![3, 0, -3], ![-2, -1, 3]]

def raw8675step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![3, 0, -3], ![-2, -1, 3]]

def raw8675step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw8676 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![-2, -1, 3], ![1, 2, -3]]

def raw8676step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![-2, -1, 3], ![1, 2, -3]]

def raw8676step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def raw8677 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-2, 1, 1]]

def raw8677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-2, 1, 1]]

def raw8677step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw8678 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![-3, 1, 2]]

def raw8678step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2], ![3, -1, -2]]

def raw8678step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2], ![3, -1, -2]]

def raw8678step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw8679 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-2, 0, 2]]

def raw8679step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-2, 0, 2]]

def raw8679step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw8680 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![-2, -1, 3]]

def raw8680step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![-2, -1, 3]]

def raw8680step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw8681 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![-3, 1, 2]]

def raw8681step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1], ![3, -1, -2]]

def raw8681step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1], ![3, -1, -2]]

def raw8681step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw8682 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, 3, -3]]

def raw8682step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, 3, -3]]

def raw8682step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def raw8683 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![-3, 0, 3], ![1, 2, -3]]

def raw8683step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![3, 0, -3], ![-1, -2, 3]]

def raw8683step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![3, 0, -3], ![-1, -2, 3]]

def raw8683step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw8684 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![-2, -1, 3], ![0, 3, -3]]

def raw8684step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![-2, -1, 3], ![0, 3, -3]]

def raw8684step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw8685 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![-1, -1, 2], ![-1, 3, -2]]

def raw8685step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![-1, -1, 2], ![-1, 3, -2]]

def raw8685step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw8686 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![-3, 2, 1]]

def raw8686step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![3, -2, -1]]

def raw8686step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![3, -2, -1]]

def raw8686step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw8687 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![-3, 1, 2]]

def raw8687step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![3, -1, -2]]

def raw8687step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![3, -1, -2]]

def raw8687step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw8688 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![-2, 0, 2], ![-1, 2, -1], ![2, -1, -1]]

def raw8688step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![1, -2, 1], ![-2, 1, 1]]

def raw8688step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-1, 0, 1], ![2, 0, -2], ![1, -2, 1], ![-2, 1, 1]]

def raw8688step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw8689 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![-2, 2, 0], ![-1, -1, 2], ![2, 0, -2]]

def raw8689step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![1, 1, -2], ![-2, 0, 2]]

def raw8689step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-1, 0, 1], ![2, -2, 0], ![1, 1, -2], ![-2, 0, 2]]

def raw8689step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0]]

def raw8690 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![-1, 2, -1], ![2, 0, -2], ![-2, -1, 3]]

def raw8690step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2], ![2, 1, -3]]

def raw8690step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2], ![2, 1, -3]]

def raw8690step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3]]

def raw8691 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![-1, -2, 3], ![-1, 3, -2]]

def raw8691step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-1, -2, 3], ![-1, 3, -2]]

def raw8691step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]

def raw8692 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0]]

def raw8692step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]

def raw8693 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![-2, -1, 3], ![2, 1, -3]]

def raw8693step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]

def raw8694 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, -2, 3], ![1, 2, -3]]

def raw8694step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def raw8695 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![-1, -1, 2]]

def raw8695step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw8696 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![-1, -2, 3], ![0, 3, -3]]

def raw8696step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 3, -3], ![1, 0, -1]]

def raw8697 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 0, 0]]

def raw8697step0 : Matrix (Fin 2) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1]]

def raw8697step1 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

def raw8698 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2], ![3, 0, -3]]

def raw8698step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![-2, 1, 1], ![-1, -1, 2], ![3, 0, -3]]

def raw8698step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

def raw8699 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3], ![2, 1, -3]]

def raw8699step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![3, 0, -3], ![-2, -1, 3]]

def raw8699step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![3, 0, -3], ![-2, -1, 3]]

def raw8699step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw8700 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3], ![1, 2, -3]]

def raw8700step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![-2, -1, 3], ![1, 2, -3]]

def raw8700step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def raw8701 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![-2, 1, 1]]

def raw8701step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-2, 1, 1]]

def raw8701step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw8702 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![-3, 1, 2]]

def raw8702step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![3, -1, -2]]

def raw8702step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2], ![3, -1, -2]]

def raw8702step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw8703 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![-2, 3, -1], ![1, -3, 2]]

def raw8703step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-2, 3, -1], ![1, -3, 2]]

def raw8703step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical272
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8704 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![-1, 3, -2], ![0, -3, 3]]

def raw8704step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-1, 3, -2], ![0, -3, 3]]

def raw8704step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0]]

def raw8705 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![-2, 0, 2]]

def raw8705step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-2, 0, 2]]

def raw8705step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw8706 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![-2, -1, 3]]

def raw8706step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![-2, -1, 3]]

def raw8706step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw8707 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![-3, 1, 2]]

def raw8707step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, -1, 1], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![3, -1, -2]]

def raw8707step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1], ![3, -1, -2]]

def raw8707step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw8708 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 0, 2], ![-1, -1, 2], ![3, 0, -3]]

def raw8708step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

def raw8709 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1], ![-1, -2, 3], ![3, 0, -3]]

def raw8709step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![1, 2, -3], ![-3, 0, 3]]

def raw8709step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]

def raw8710 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1], ![-1, -1, 2], ![3, -1, -2]]

def raw8710step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![1, 1, -2], ![-3, 1, 2]]

def raw8710step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]

def raw8711 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1]]

def raw8711step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![1, -1], ![-1, 1]]

def raw8711step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def raw8712 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-2, -1, 3], ![2, 1, -3]]

def raw8712step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, 1, -3]]

def raw8713 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -2, 3], ![1, 2, -3]]

def raw8713step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 2, -3]]

def raw8714 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![-1, -1, 2]]

def raw8714step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![-1, -1, 2]]

def raw8714step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw8715 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![-3, 0, 3], ![2, 1, -3]]

def raw8715step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]

def raw8716 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![-2, -1, 3], ![1, 2, -3]]

def raw8716step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 2, -3]]

def raw8717 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![-2, 1, 1]]

def raw8717step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw8718 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2], ![-3, 1, 2]]

def raw8718step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]

def raw8719 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![-3, -1, 4], ![2, 1, -3]]

def raw8719step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]

def raw8720 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![-3, 0, 3], ![2, 0, -2]]

def raw8720step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![3, 0, -3], ![-2, 0, 2]]

def raw8720step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw8721 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![-2, -2, 4], ![1, 2, -3]]

def raw8721step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def raw8722 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![-2, -1, 3], ![1, 1, -2]]

def raw8722step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw8723 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![-1, -2, 3], ![0, 2, -2]]

def raw8723step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

def raw8724 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1]]

def raw8724step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw8725 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-2, 0, 2]]

def raw8725step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw8726 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![-2, -1, 3]]

def raw8726step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw8727 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![-3, 1, 2]]

def raw8727step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]

def raw8728 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![-3, 0, 3]]

def raw8728step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2], ![3, 0, -3]]

def raw8728step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw8729 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![-1, -1, 2]]

def raw8729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![-1, -1, 2]]

def raw8729step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw8730 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2]]

def raw8730step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw8731 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-2, -1, 3]]

def raw8731step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw8732 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![-2, -2, 4]]

def raw8732step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw8733 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![-3, 1, 2]]

def raw8733step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]

def raw8734 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![-3, 0, 3]]

def raw8734step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1], ![3, 0, -3]]

def raw8734step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

def raw8735 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![-2, 0, 2], ![0, 3, -3]]

def raw8735step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 3, -3], ![1, -2, 1], ![1, -1, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical273
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8736 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![-3, 0, 3], ![1, 2, -3]]

def raw8736step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]

def raw8737 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![-2, -1, 3], ![0, 3, -3]]

def raw8737step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

def raw8738 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![-1, -1, 2], ![-1, 3, -2]]

def raw8738step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw8739 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![-3, 2, 1]]

def raw8739step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]

def raw8740 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2], ![-3, 1, 2]]

def raw8740step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]

def raw8741 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![-2, 0, 2], ![-1, 2, -1], ![2, -1, -1]]

def raw8741step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![2, 0, -2], ![1, -2, 1], ![-2, 1, 1]]

def raw8741step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]

def raw8742 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![-2, 2, 0], ![-1, -1, 2], ![2, 0, -2]]

def raw8742step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![2, -2, 0], ![1, 1, -2], ![-2, 0, 2]]

def raw8742step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]

def raw8743 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![-1, 2, -1], ![2, 0, -2], ![-2, -1, 3]]

def raw8743step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]

def raw8744 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, -2, 3], ![0, 3, -3]]

def raw8744step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![-1, -2, 3], ![0, 3, -3]]

def raw8744step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0]]

def raw8745 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2], ![0, 3, -3]]

def raw8745step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 3, -3], ![1, -2, 1], ![1, -1, 0]]

def raw8746 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3], ![1, 2, -3]]

def raw8746step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]

def raw8747 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3], ![0, 3, -3]]

def raw8747step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def raw8748 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, 2, -2]]

def raw8748step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]

def raw8749 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, 3, -2]]

def raw8749step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw8750 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![-3, 2, 1]]

def raw8750step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![3, -2, -1]]

def raw8750step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw8751 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![-3, 1, 2]]

def raw8751step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]

def raw8752 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-3, -1, 4], ![1, 2, -3]]

def raw8752step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]

def raw8753 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-3, 0, 3], ![1, 1, -2]]

def raw8753step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![3, 0, -3], ![-1, -1, 2]]

def raw8753step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw8754 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-2, -2, 4], ![0, 3, -3]]

def raw8754step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw8755 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-2, -1, 3], ![0, 2, -2]]

def raw8755step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw8756 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-1, -2, 3], ![-1, 3, -2]]

def raw8756step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw8757 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-1, -1, 2], ![-1, 2, -1]]

def raw8757step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw8758 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![-3, 2, 1]]

def raw8758step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 1, 0], ![3, -2, -1]]

def raw8758step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw8759 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![-3, 1, 2]]

def raw8759step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![3, -1, -2]]

def raw8759step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw8760 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![-3, 0, 3]]

def raw8760step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![3, 0, -3]]

def raw8760step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw8761 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-2, -1, 3], ![-1, 2, -1], ![2, -1, -1]]

def raw8761step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

def raw8762 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-2, 0, 2], ![-1, 1, 0], ![2, -1, -1]]

def raw8762step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw8763 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-2, 0, 2], ![-1, 2, -1], ![2, -2, 0]]

def raw8763step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![2, 0, -2], ![1, -2, 1], ![-2, 2, 0]]

def raw8763step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]

def raw8764 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-2, 1, 1], ![-1, -1, 2], ![2, 0, -2]]

def raw8764step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]

def raw8765 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-2, 2, 0], ![-1, -2, 3], ![2, 0, -2]]

def raw8765step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]

def raw8766 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-2, 2, 0], ![-1, -1, 2], ![2, -1, -1]]

def raw8766step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![2, -2, 0], ![1, 1, -2], ![-2, 1, 1]]

def raw8766step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]

def raw8767 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-1, 1, 0], ![2, 0, -2], ![-2, -1, 3]]

def raw8767step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical274
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8768 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-1, 2, -1], ![2, -1, -1], ![-2, -1, 3]]

def raw8768step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

def raw8769 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-1, 2, -1], ![2, 0, -2], ![-2, -2, 4]]

def raw8769step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]

def raw8770 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![-2, 3, -1], ![1, -3, 2]]

def raw8770step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-2, 3, -1], ![1, -3, 2]]

def raw8770step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def raw8771 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![-1, 3, -2], ![0, -3, 3]]

def raw8771step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-1, 3, -2], ![0, -3, 3]]

def raw8771step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0]]

def raw8772 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![-1, -2, 3], ![-1, 3, -2]]

def raw8772step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw8773 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-3, 3, 0], ![1, -3, 2]]

def raw8773step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]

def raw8774 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-2, 3, -1], ![0, -3, 3]]

def raw8774step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def raw8775 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-1, -3, 4], ![-1, 3, -2]]

def raw8775step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 3, -2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw8776 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-1, -2, 3], ![-1, 2, -1]]

def raw8776step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw8777 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-1, 3, -2], ![-1, -3, 4]]

def raw8777step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 3, -2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw8778 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -1, 1], ![0, 2, -2], ![0, -1, 1]]

def raw8778step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1]]

def raw8778step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw8781 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![-2, 0, 2], ![-1, 4, -3]]

def raw8781step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 4, -3], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]

def raw8782 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![-2, 1, 1], ![-1, 2, -1]]

def raw8782step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![2, -1, -1], ![1, -2, 1]]

def raw8782step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]

def raw8783 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![-1, -1, 2], ![-2, 4, -2]]

def raw8783step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]

def raw8784 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![1, -1, 0], ![1, -2, 1], ![1, 0, -1], ![-2, 0, 2], ![-1, 4, -3]]

def raw8784step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 4, -3], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]

def raw8785 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, 4, -3]]

def raw8785step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]

def raw8786 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![-2, -1, 3], ![-1, 4, -3]]

def raw8786step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 4, -3], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

def raw8787 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![-2, 0, 2], ![-1, 3, -2]]

def raw8787step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![2, 0, -2], ![1, -3, 2]]

def raw8787step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

def raw8788 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![-2, 1, 1], ![-1, 2, -1]]

def raw8788step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]

def raw8789 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![-1, -1, 2], ![-2, 4, -2]]

def raw8789step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

def raw8790 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, 2, -1]]

def raw8790step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]

def raw8791 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![-1, -1, 2], ![-2, 4, -2]]

def raw8791step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

def raw8792 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![-2, 0, 2], ![-1, 2, -1]]

def raw8792step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, 0, -2], ![1, -2, 1]]

def raw8792step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw8793 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![-2, 1, 1], ![-1, 1, 0]]

def raw8793step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -1, -1], ![1, -1, 0]]

def raw8793step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw8794 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![-1, -2, 3], ![-2, 4, -2]]

def raw8794step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

def raw8795 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![-1, -1, 2], ![-2, 3, -1]]

def raw8795step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -3, 1]]

def raw8795step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]

def raw8796 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-5, 2, 1, 2], ![5, -1, -2, -2]]

def raw8796step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -5, 5], ![-1, 2, -1], ![1, 1, -2], ![0, 2, -2]]

def raw8796step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 5, -5], ![1, -2, 1]]

def raw8797 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-4, 2, 1, 1], ![4, -1, -2, -1]]

def raw8797step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![-1, 2, -1], ![1, 1, -2], ![0, 1, -1]]

def raw8797step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 4, -4], ![1, -2, 1]]

def raw8798 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-3, -1, 1, 3], ![3, 2, -2, -3]]

def raw8798step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![-1, -1, 2], ![1, 1, -2], ![0, 3, -3]]

def raw8798step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -3, 3], ![0, 3, -3], ![1, 1, -2]]

def raw8799 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-3, 2, -2, 3], ![3, -1, 1, -3]]

def raw8799step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![-1, 2, -1], ![1, -2, 1], ![0, 3, -3]]

def raw8799step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -3, 3], ![0, 3, -3], ![1, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical275
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8800 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-3, 3, -2, 2], ![3, -2, 1, -2]]

def raw8800step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![-1, 3, -2], ![1, -2, 1], ![0, 2, -2]]

def raw8800step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -2, 2], ![0, 3, -3], ![1, 1, -2]]

def raw8801 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-3, 3, 1, -1], ![3, -2, -2, 1]]

def raw8801step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![-1, 3, -2], ![1, 1, -2], ![0, -1, 1]]

def raw8801step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 3, -3], ![1, -2, 1]]

def raw8802 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 1, 2], ![2, 2, -2, -2]]

def raw8802step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-1, -1, 2], ![1, 1, -2], ![0, 2, -2]]

def raw8802step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2]]

def raw8803 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 2, 1], ![2, 2, -3, -1]]

def raw8803step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-1, -1, 2], ![1, 2, -3], ![0, 1, -1]]

def raw8803step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![-1, -2, 3], ![0, -1, 1]]

def raw8803step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2]]

def raw8804 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 2, -2, 2], ![2, -1, 1, -2]]

def raw8804step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-1, 2, -1], ![1, -2, 1], ![0, 2, -2]]

def raw8804step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2]]

def raw8805 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 2, 1, -1], ![2, -1, -2, 1]]

def raw8805step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-1, 2, -1], ![1, 1, -2], ![0, -1, 1]]

def raw8805step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1]]

def raw8806 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 3, -2, 1], ![2, -2, 1, -1]]

def raw8806step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-1, 3, -2], ![1, -2, 1], ![0, 1, -1]]

def raw8806step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2]]

def raw8807 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 3, 1, -2], ![2, -2, -2, 2]]

def raw8807step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-1, 3, -2], ![1, 1, -2], ![0, -2, 2]]

def raw8807step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![0, 2, -2], ![1, -2, 1]]

def raw8808 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -2, 2, 1], ![1, 3, -3, -1]]

def raw8808step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -2, 3], ![1, 2, -3], ![0, 1, -1]]

def raw8808step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3]]

def raw8809 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, 1, 1], ![1, 2, -2, -1]]

def raw8809step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![1, 1, -2], ![0, 1, -1]]

def raw8809step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2]]

def raw8810 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, 3, -1], ![1, 2, -4, 1]]

def raw8810step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![1, 3, -4], ![0, -1, 1]]

def raw8810step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![1, 1, -2], ![-1, -3, 4], ![0, 1, -1]]

def raw8810step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]

def raw8811 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, -1, 2], ![0, 2, 2, -4], ![1, -1, -2, 2]]

def raw8811step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 2, 2, -4], ![1, -1, -2, 2]]

def raw8812 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, 1, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def raw8812step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![1, 0, -1, 0], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 1, 2, -2]]

def raw8812step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw8813 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, 1, 0], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw8813step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 2, -1], ![1, 1, 0, -2], ![0, 0, -2, 2]]

def raw8813step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![1, 0, -2, 1], ![-1, -1, 0, 2], ![0, 0, 2, -2]]

def raw8813step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 0, -1]]

def raw8814 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, 1, 0], ![0, 2, 1, -3], ![1, -1, -3, 3]]

def raw8814step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 2, -1], ![1, 1, 1, -3], ![0, 0, -3, 3]]

def raw8814step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![1, 0, -2, 1], ![-1, -1, -1, 3], ![0, 0, 3, -3]]

def raw8814step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, 0, 0, -1]]

def raw8815 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, 2, -1], ![0, 2, 0, -2], ![1, -1, -3, 3]]

def raw8815step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 2, -1], ![1, 2, 0, -3], ![0, -1, -2, 3]]

def raw8815step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![1, 0, -2, 1], ![-1, -2, 0, 3], ![0, 1, 2, -3]]

def raw8815step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, 0, -2, 1]]

def raw8816 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 1, -3, 3], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw8816step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 1, 1, -1], ![1, -3, 1, 1], ![0, 3, -2, -1]]

def raw8816step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![1, -1, -1, 1], ![-1, 3, -1, -1], ![0, -3, 2, 1]]

def raw8816step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 0, 1], ![0, 1, 2, -3], ![1, 1, -1, -1]]

def raw8817 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 1, -3, 3], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def raw8817step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 1, 1, -1], ![1, -3, 2, 0], ![0, 3, -3, 0]]

def raw8817step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -3, 3], ![0, 1, 0, -1], ![1, 0, 2, -3]]

def raw8818 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 1, -2, 2], ![0, 1, 2, -3], ![1, -1, -1, 1]]

def raw8818step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 1, 1, -1], ![1, -2, 2, -1], ![0, 2, -3, 1]]

def raw8818step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -3, 2], ![0, 1, 0, -1], ![1, -1, 2, -2]]

def raw8819 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 1, 0, 0], ![1, 0, -1, 0]]

def raw8819step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 1, 0], ![1, 0, -1]]

def raw8819step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![1, -1, 0]]

def raw8820 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 2, -2, 1], ![1, -1, 1, -1]]

def raw8820step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 2, -1], ![1, -2, 1], ![0, 1, -1]]

def raw8820step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2]]

def raw8821 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 2, 1, -2], ![1, -1, -2, 2]]

def raw8821step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 2, -1], ![1, 1, -2], ![0, -2, 2]]

def raw8821step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1]]

def raw8822 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, -1, -2, 3], ![0, 2, 1, -3]]

def raw8822step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 0, 0], ![-1, -1, 2], ![1, -2, 1], ![0, 3, -3]]

def raw8822step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![1, -2, 1], ![0, 3, -3]]

def raw8822step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 3, -3], ![1, -2, 1]]

def raw8823 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![-2, 2, 0, 0], ![2, 0, 2, -4]]

def raw8823step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 1, 1, -2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![2, -2, 0, 0], ![-2, 0, -2, 4]]

def raw8823step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -2, 0, 0]]

def raw8824 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-2, 0, 1, 1], ![2, 1, 1, -4]]

def raw8824step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 1, 1, -2], ![0, 0, 1, -1], ![0, -1, 1, 0], ![2, 0, -1, -1], ![-2, -1, -1, 4]]

def raw8824step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def raw8825 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-2, 1, 0, 1], ![2, 0, 2, -4]]

def raw8825step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 1, 1, -2], ![0, 0, 1, -1], ![0, -1, 1, 0], ![2, -1, 0, -1], ![-2, 0, -2, 4]]

def raw8825step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -1, 0, -1]]

def raw8826 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, -1, -1, 2], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 0, 1, 1], ![1, 2, 1, -4]]

def raw8826step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 1, 1, -2], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![2, 0, -1, -1], ![-1, -2, -1, 4]]

def raw8826step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw8827 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, -1, -1, 2], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![1, 1, 2, -4]]

def raw8827step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw8828 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, -1, -1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![-2, 0, 0, 2], ![2, 0, 2, -4]]

def raw8828step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 1, 1, -2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![2, 0, 0, -2], ![-2, 0, -2, 4]]

def raw8828step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, 0, -2]]

def raw8829 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![1, 1, 2, -4]]

def raw8829step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw8830 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, -1, -1, 2], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![0, 2, 2, -4]]

def raw8830step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 1, 1, -2], ![-1, 0, 1, 0], ![-1, 0, 1, 0], ![2, 0, 0, -2], ![0, -2, -2, 4]]

def raw8830step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw8831 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![-1, 2, 2, -3], ![1, -1, -2, 2]]

def raw8831step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 2, -1], ![1, -1, 2, -2], ![0, 1, -3, 2]]

def raw8831step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, 0, -2, 1], ![-1, 1, -2, 2], ![0, -1, 3, -2]]

def raw8831step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, -1, 2, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical276
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8832 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![-2, 2, 0, 0], ![2, 0, 2, -4]]

def raw8832step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 0, 1, -1], ![0, 1, 1, -2], ![0, 0, 1, -1], ![2, -2, 0, 0], ![-2, 0, -2, 4]]

def raw8832step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -2, 0, 0]]

def raw8833 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![-2, 0, 1, 1], ![2, 1, 1, -4]]

def raw8833step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 0, 1, -1], ![0, 1, 1, -2], ![0, -1, 1, 0], ![2, 0, -1, -1], ![-2, -1, -1, 4]]

def raw8833step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def raw8834 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![-2, 1, 0, 1], ![2, 0, 2, -4]]

def raw8834step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 0, 1, -1], ![0, 1, 1, -2], ![0, -1, 1, 0], ![2, -1, 0, -1], ![-2, 0, -2, 4]]

def raw8834step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -1, 0, -1]]

def raw8835 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, -1, -1, 2], ![1, 0, -1, 0], ![-2, 0, 1, 1], ![1, 2, 1, -4]]

def raw8835step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 0, 1, -1], ![0, 1, 1, -2], ![-1, 0, 1, 0], ![2, 0, -1, -1], ![-1, -2, -1, 4]]

def raw8835step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw8836 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, -1, -1, 2], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![1, 1, 2, -4]]

def raw8836step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw8837 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, -1, -1, 2], ![-2, 2, 0, 0], ![2, 0, 2, -4]]

def raw8837step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, -2, 0, 0], ![-2, 0, -2, 4]]

def raw8837step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -2, 0, 0]]

def raw8838 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![-2, 0, 1, 1], ![2, 1, 1, -4]]

def raw8838step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![2, 0, -1, -1], ![-2, -1, -1, 4]]

def raw8838step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def raw8839 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![-2, 1, 0, 1], ![2, 0, 2, -4]]

def raw8839step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -2, 0, 1]]

def raw8840 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![-2, 2, 0, 0], ![2, -1, 2, -3]]

def raw8840step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![2, -2, 0, 0], ![-2, 1, -2, 3]]

def raw8840step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -2, 0, 0]]

def raw8841 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-2, -1, 1, 2], ![2, 1, 1, -4]]

def raw8841step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -1, 1, 0], ![2, 1, -1, -2], ![-2, -1, -1, 4]]

def raw8841step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, -1, -2]]

def raw8842 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-2, 0, 0, 2], ![2, 0, 2, -4]]

def raw8842step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -1, 1, 0], ![2, 0, 0, -2], ![-2, 0, -2, 4]]

def raw8842step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw8843 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-2, 0, 1, 1], ![2, 0, 1, -3]]

def raw8843step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -3, 1], ![1, 0, 0, -1]]

def raw8844 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-2, 1, 0, 1], ![2, -1, 2, -3]]

def raw8844step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -1, 1, 0], ![2, -1, 0, -1], ![-2, 1, -2, 3]]

def raw8844step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -1, 0, -1]]

def raw8845 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![-2, 0, 1, 1], ![1, 2, 1, -4]]

def raw8845step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 1, -1], ![2, 0, -1, -1], ![-1, -2, -1, 4]]

def raw8845step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw8846 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![-2, 1, 0, 1], ![1, 1, 2, -4]]

def raw8846step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, 1, 2, -4]]

def raw8847 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, -1, 1, 2], ![1, 2, 1, -4]]

def raw8847step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![2, 1, -1, -2], ![-1, -2, -1, 4]]

def raw8847step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 2, -1, -2]]

def raw8848 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![1, 1, 2, -4]]

def raw8848step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![2, 0, 0, -2], ![-1, -1, -2, 4]]

def raw8848step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw8849 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 0, 1, 1], ![1, 1, 1, -3]]

def raw8849step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![2, 0, -1, -1], ![-1, -1, -1, 3]]

def raw8849step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def raw8850 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![1, 0, 2, -3]]

def raw8850step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -3, 2], ![0, 1, 0, -1], ![1, -2, 1, 0]]

def raw8851 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 0, -1, 1], ![-2, 0, 0, 2], ![2, 0, 2, -4]]

def raw8851step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 0, 1, -1], ![0, -1, 1, 0], ![0, 0, 1, -1], ![2, 0, 0, -2], ![-2, 0, -2, 4]]

def raw8851step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw8852 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![-2, -1, 0, 3], ![2, 0, 2, -4]]

def raw8852step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 2, -4]]

def raw8853 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![-2, 0, 0, 2], ![2, -1, 2, -3]]

def raw8853step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 2, -3]]

def raw8854 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![-2, 0, 0, 2], ![1, 1, 2, -4]]

def raw8854step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 2, -4]]

def raw8855 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-2, -1, 0, 3], ![1, 1, 2, -4]]

def raw8855step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw8856 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![1, 0, 2, -3]]

def raw8856step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![0, 0, 1, -1], ![0, 1, -3, 2], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw8857 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 2, 2, -4], ![0, -1, -2, 3]]

def raw8857step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 0, 1, -1], ![0, -2, -2, 4], ![0, 1, 2, -3]]

def raw8857step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![0, 1, -1], ![-2, -2, 4], ![1, 2, -3]]

def raw8857step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def raw8858 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![0, 2, 2, -4]]

def raw8858step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 0, 1, -1], ![-1, 1, 1, -1], ![-1, 0, 1, 0], ![2, 0, 0, -2], ![0, -2, -2, 4]]

def raw8858step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw8859 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, -1, -1, 1], ![-2, 0, 0, 2], ![0, 2, 2, -4]]

def raw8859step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![-1, 1, 1, -1], ![2, 0, 0, -2], ![0, -2, -2, 4]]

def raw8859step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw8860 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-2, -1, 0, 3], ![0, 2, 2, -4]]

def raw8860step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw8861 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![0, 1, 2, -3]]

def raw8861step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![-1, 0, 1, 0], ![2, 0, 0, -2], ![0, -1, -2, 3]]

def raw8861step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw8862 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def raw8862step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 0, -1, 1], ![1, -1, 0, 0], ![0, -1, 0, 1], ![-1, 1, 2, -2]]

def raw8862step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw8863 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, 1, -1], ![-1, 2, 0, -1], ![1, -1, -2, 2]]

def raw8863step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 2, -1], ![1, 1, 0, -2], ![0, -1, -1, 2]]

def raw8863step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, 0, -2, 1], ![-1, -1, 0, 2], ![0, 1, 1, -2]]

def raw8863step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 0, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical277
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8864 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, 1, -1], ![-1, 2, 1, -2], ![1, -1, -3, 3]]

def raw8864step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 2, -1], ![1, 1, 1, -3], ![0, -1, -2, 3]]

def raw8864step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, 0, -2, 1], ![-1, -1, -1, 3], ![0, 1, 2, -3]]

def raw8864step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 0, 2, -3]]

def raw8865 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 1, -1, 2]]

def raw8865step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw8866 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-1, 1, 0, 0], ![1, -1, -2, 2]]

def raw8866step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 0, -1, 1], ![0, -1, 0, 1], ![1, -1, 0, 0], ![-1, 1, 2, -2]]

def raw8866step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw8867 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![0, -1, -2, 3]]

def raw8867step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-1, -2, 3]]

def raw8867step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw8868 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![0, -1, -2, 3]]

def raw8868step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![-1, -2, 3]]

def raw8868step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw8869 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 1, -3], ![0, -1, -3, 4]]

def raw8869step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 0, -1, 1], ![0, -2, -1, 3], ![0, 1, 3, -4]]

def raw8869step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![0, -1, 1], ![-2, -1, 3], ![1, 3, -4]]

def raw8869step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

def raw8870 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, 2, -2], ![-1, 2, 0, -1], ![1, -1, -3, 3]]

def raw8870step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 2, -1], ![1, 2, 0, -3], ![0, -2, -1, 3]]

def raw8870step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, 0, -2, 1], ![-1, -2, 0, 3], ![0, 2, 1, -3]]

def raw8870step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def raw8871 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, 2, -2], ![0, 2, 0, -2], ![0, -1, -3, 4]]

def raw8871step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 0, -2, 2], ![0, -2, 0, 2], ![0, 1, 3, -4]]

def raw8871step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![0, -2, 2], ![-2, 0, 2], ![1, 3, -4]]

def raw8871step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, -1, 0], ![1, 3, -4]]

def raw8872 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 1, -3, 2], ![-1, 1, 1, -1], ![1, -1, 1, -1]]

def raw8872step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, 1, -1], ![1, -3, 1, 1], ![0, 2, -1, -1]]

def raw8872step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, -1, -1, 1], ![-1, 3, -1, -1], ![0, -2, 1, 1]]

def raw8872step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def raw8873 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 1, -3, 2], ![-1, 1, 2, -2], ![1, -1, 0, 0]]

def raw8873step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, 1, -1], ![1, -3, 2, 0], ![0, 2, -2, 0]]

def raw8873step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, 0, 2, -3]]

def raw8874 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 1, -3, 2], ![0, 1, 1, -2], ![0, -1, 1, 0]]

def raw8874step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, -1, 3, -2], ![0, -1, -1, 2], ![0, 1, -1, 0]]

def raw8874step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-1, 3, -2], ![-1, -1, 2], ![1, -1, 0]]

def raw8874step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def raw8875 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 1, -3, 2], ![0, 1, 2, -3], ![0, -1, 0, 1]]

def raw8875step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, -1, 3, -2], ![0, -1, -2, 3], ![0, 1, 0, -1]]

def raw8875step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-1, 3, -2], ![-1, -2, 3], ![1, 0, -1]]

def raw8875step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1]]

def raw8876 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 1, -2, 1], ![-1, 1, 2, -2], ![1, -1, -1, 1]]

def raw8876step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def raw8877 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 1, -2, 1], ![0, 1, 2, -3], ![0, -1, -1, 2]]

def raw8877step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, -1, 2, -1], ![0, -1, -2, 3], ![0, 1, 1, -2]]

def raw8877step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-1, 2, -1], ![-1, -2, 3], ![1, 1, -2]]

def raw8877step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2]]

def raw8878 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-2, -1, 1, 2]]

def raw8878step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw8879 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 0, -1, 1]]

def raw8879step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 1, 0], ![1, 0, -1], ![0, -1, 1]]

def raw8879step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![1, -1, 0]]

def raw8880 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 1, 0], ![1, -2, 2, -1], ![-1, 3, -3, 1]]

def raw8880step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -2, 3], ![1, 2, -3], ![0, -1, 1]]

def raw8880step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3]]

def raw8881 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 1, 0], ![1, -1, 1, -1], ![-1, 2, -2, 1]]

def raw8881step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -1, 2], ![1, 1, -2], ![0, -1, 1]]

def raw8881step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2]]

def raw8882 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 1, 0], ![1, -1, 2, -2], ![-1, 2, -3, 2]]

def raw8882step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -1, 2], ![1, 2, -3], ![0, -2, 2]]

def raw8882step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![1, 1, -2], ![-1, -2, 3], ![0, 2, -2]]

def raw8882step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2]]

def raw8883 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 1, 0], ![2, -1, 1, -2], ![-2, 2, -2, 2]]

def raw8883step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![-1, -1, 2], ![1, 1, -2], ![0, -2, 2]]

def raw8883step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2]]

def raw8884 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-4, 2, -1, 3], ![4, -1, -1, -2]]

def raw8884step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![-1, 2, -1], ![2, -1, -1], ![-1, 3, -2]]

def raw8884step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -2, 1], ![-2, 1, 1], ![1, -3, 2]]

def raw8884step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -4, 4], ![1, 1, -2], ![1, 2, -3]]

def raw8885 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-4, 2, 0, 2], ![4, -1, -2, -1]]

def raw8885step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![-1, 2, -1], ![2, 0, -2], ![-1, 2, -1]]

def raw8885step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -2, 1], ![-2, 0, 2], ![1, -2, 1]]

def raw8885step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 4, -4], ![1, -2, 1], ![1, -2, 1]]

def raw8886 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-3, -1, 0, 4], ![3, 2, -2, -3]]

def raw8886step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![-1, -1, 2], ![2, 0, -2], ![-1, 4, -3]]

def raw8886step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, 1, -2], ![-2, 0, 2], ![1, -4, 3]]

def raw8886step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -4, 3], ![1, 1, -2]]

def raw8887 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-3, 2, -1, 2], ![3, -1, -1, -1]]

def raw8887step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![-1, 2, -1], ![2, -1, -1], ![-1, 2, -1]]

def raw8887step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -2, 1], ![-2, 1, 1], ![1, -2, 1]]

def raw8887step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 1, -2], ![1, 1, -2]]

def raw8888 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-3, 2, 0, 1], ![3, -1, -2, 0]]

def raw8888step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![-1, 2, -1], ![2, 0, -2], ![-1, 1, 0]]

def raw8888step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -2, 1], ![-2, 0, 2], ![1, -1, 0]]

def raw8888step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -2, 1], ![1, -1, 0]]

def raw8889 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-3, 2, 1, 0], ![3, -1, -3, 1]]

def raw8889step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![-1, 2, -1], ![2, 1, -3], ![-1, 0, 1]]

def raw8889step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -2, 1], ![-2, -1, 3], ![1, 0, -1]]

def raw8889step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

def raw8890 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-3, 3, 0, 0], ![3, -2, -2, 1]]

def raw8890step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![-1, 3, -2], ![2, 0, -2], ![-1, 0, 1]]

def raw8890step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -3, 2], ![-2, 0, 2], ![1, 0, -1]]

def raw8890step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -3, 2], ![1, 0, -1]]

def raw8891 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-2, -2, 2, 2], ![2, 3, -4, -1]]

def raw8891step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-1, -2, 3], ![2, 2, -4], ![-1, 2, -1]]

def raw8891step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, 2, -3], ![-2, -2, 4], ![1, -2, 1]]

def raw8891step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, -2, 1], ![1, 2, -3]]

def raw8892 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-2, -1, -2, 5], ![2, 2, 0, -4]]

def raw8892step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-1, -1, 2], ![2, -2, 0], ![-1, 5, -4]]

def raw8892step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![-2, 2, 0], ![1, -5, 4]]

def raw8892step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, -2, 1], ![1, 4, -5]]

def raw8893 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-2, -1, -1, 4], ![2, 2, -1, -3]]

def raw8893step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-1, -1, 2], ![2, -1, -1], ![-1, 4, -3]]

def raw8893step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![-2, 1, 1], ![1, -4, 3]]

def raw8893step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -2, 1], ![1, 3, -4]]

def raw8894 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-2, -1, 0, 3], ![2, 2, -2, -2]]

def raw8894step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-1, -1, 2], ![2, 0, -2], ![-1, 3, -2]]

def raw8894step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![-2, 0, 2], ![1, -3, 2]]

def raw8894step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -3, 2], ![1, 1, -2]]

def raw8895 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-2, -1, 3, 0], ![2, 2, -5, 1]]

def raw8895step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-1, -1, 2], ![2, 3, -5], ![-1, 0, 1]]

def raw8895step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![-2, -3, 5], ![1, 0, -1]]

def raw8895step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical278
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8896 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-2, 2, -1, 1], ![2, -1, -1, 0]]

def raw8896step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-1, 2, -1], ![2, -1, -1], ![-1, 1, 0]]

def raw8896step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, -2, 1], ![-2, 1, 1], ![1, -1, 0]]

def raw8896step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw8897 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![-2, 2, 1, -1], ![2, -1, -3, 2]]

def raw8897step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-1, 2, -1], ![2, 1, -3], ![-1, -1, 2]]

def raw8897step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, -2, 1], ![-2, -1, 3], ![1, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end


