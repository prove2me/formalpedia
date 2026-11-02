-- Prove2me | Definitions.Def_OAIQ106D029
-- name    : OAIQ106D029
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T12:14:33.824106+00:00
-- url     : https://prove2.me/theorems/40e544d4-6feb-415a-9f5c-ad01fb4c9b6d
-- title:
--   Definitions bundle OAIQ106D029 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 7317 declarations of OpenAI's Lean: 7317 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSemantics.raw3382`, `OAI.MUB6.Certificate.MixedSemantics.raw33820Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw33820step0`, `OAI.MUB6.Certificate.MixedSemantics.raw33820step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw33820step1`, `OAI.MUB6.Certificate.MixedSemantics.raw33820step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw33820step2`, `OAI.MUB6.Certificate.MixedSemantics.raw33820step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw33820step3`, `OAI.MUB6.Certificate.MixedSemantics.raw33820step3Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw33821`, `OAI.MUB6.Certificate.MixedSemantics.raw33821Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw33821step0`, `OAI.MUB6.Certificate.MixedSemantics.raw33821step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw33821step1`, `OAI.MUB6.Certificate.MixedSemantics.raw33821step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw33821step2`, `OAI.MUB6.Certificate.MixedSemantics.raw33821step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw33822`, `OAI.MUB6.Certificate.MixedSemantics.raw33822Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw33822step0`, `OAI.MUB6.Certificate.MixedSemantics.raw33822step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw33822step1`, `OAI.MUB6.Certificate.MixedSemantics.raw33822step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw33822step2`, `OAI.MUB6.Certificate.MixedSemantics.raw33822step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw33823`, `OAI.MUB6.Certificate.MixedSemantics.raw33823Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw33823step0`, `OAI.MUB6.Certificate.MixedSemantics.raw33823step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw33823step1`, `OAI.MUB6.Certificate.MixedSemantics.raw33823step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw33823step2`, `OAI.MUB6.Certificate.MixedSemantics.raw33823step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw33824`, `OAI.MUB6.Certificate.MixedSemantics.raw33824Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw33824step0`, `OAI.MUB6.Certificate.MixedSemantics.raw33824step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw33824step1`, `OAI.MUB6.Certificate.MixedSemantics.raw33824step1Labels` and 7277 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_MixedSemantics_Canonical0`, `MutuallyUnbiased_MixedSemantics_Canonical2`, `MutuallyUnbiased_MixedSemantics_Canonical26`, `MutuallyUnbiased_MixedSemantics_Canonical264`, `MutuallyUnbiased_MixedSemantics_Canonical265`, `MutuallyUnbiased_MixedSemantics_Canonical266`, `MutuallyUnbiased_MixedSemantics_Canonical267`, `MutuallyUnbiased_MixedSemantics_Canonical268`, `MutuallyUnbiased_MixedSemantics_Canonical269`, `MutuallyUnbiased_MixedSemantics_Canonical27`, `MutuallyUnbiased_MixedSemantics_Canonical270`, `MutuallyUnbiased_MixedSemantics_Canonical271`, `MutuallyUnbiased_MixedSemantics_Canonical272`, `MutuallyUnbiased_MixedSemantics_Canonical273`, `MutuallyUnbiased_Moments_SmallPartitions`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ106D140`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_SmallPartitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.EqualityPatterns

def blocks2 : Fin 2 → ℕ := ![1, 2]

end MUB6.EqualityPatterns

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw33Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw33step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw33step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw34 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]

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

def raw338Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw338step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw338step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw338step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw338step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw339 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw339Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw339step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw339step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw340 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw340Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw340step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw340step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw340step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw340step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw341 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw341Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw341step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw341step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw344 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![0, 2, -2], ![-2, 2, 0]]
def raw344Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw344step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw344step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw344step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw344step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw345 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![0, 2, -2], ![-2, 2, 0]]
def raw345Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw345step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw345step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw346 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw346Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw346step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw346step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw346step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw346step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw347 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw347Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw347step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw347step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw348 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw348Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw348step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw348step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw348step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw348step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw349 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw3382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3382Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3382step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw3382step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3382step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3382step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3382step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3382step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3383Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3383step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3383step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3383step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3383step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1]]
def raw3384Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3384step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3384step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3384step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3384step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3384step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3384step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3385 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1]]
def raw3385Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3385step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3385step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3385step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3385step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3386 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3386Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3386step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3386step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3386step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3386step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3387 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3387Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3387step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3387step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3387step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3387step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3388 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3388Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3388step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw3388step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3389 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1]]
def raw3389Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3389step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3389step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3389step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw3389step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3389step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3389step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3390 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![0, 1, -1]]
def raw3390Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3390step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3390step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3391 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw3391Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3391step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw3391step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3391step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3391step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3391step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3391step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3392 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw3392Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3392step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw3392step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3392step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw3392step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3393 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw3393Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3393step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw3393step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3393step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3393step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3393step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3393step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3394 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 2, -1], ![2, -2, 0], ![1, 0, -1]]
def raw3394Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3394step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3394step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3394step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3394step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3395 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![0, 1, -1]]
def raw3395Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3395step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3395step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3395step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3395step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3396Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3396step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3396step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3396step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3396step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3397 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3397Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3397step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3397step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3397step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3397step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3398Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3398step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw3398step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3398step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3398step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3398step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3398step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3399 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3399Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3399step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw3399step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3399step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw3399step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3399step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw3399step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3400 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw3400Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3400step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw3400step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3400step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw3400step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3400step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3400step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3401 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 0, 0], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3401Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3401step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3401step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3401step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3401step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3402 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 0, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3402Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3402step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3402step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3402step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw3402step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3402step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3402step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3403 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 0, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3403Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3403step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3403step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3403step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3403step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3403step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]
def raw3403step2Labels : Fin 2 → Fin 3 := ![0, 2]

def raw3403step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]
def raw3403step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3404 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 0, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3404Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3404step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3404step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3404step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3404step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3404step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3404step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3404step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3404step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3405 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 0, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1]]
def raw3405Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3405step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1]]
def raw3405step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3405step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1]]
def raw3405step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3405step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3405step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3405step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3405step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3406 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3406Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3406step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3406step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3406step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw3406step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3406step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw3406step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3407 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3407Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3407step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0]]
def raw3407step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3407step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw3407step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3408 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3408Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3408step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3408step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3408step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw3408step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3408step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3408step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3409 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3409Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3409step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3409step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3409step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3409step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3409step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3409step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3410 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1]]
def raw3410Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3410step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1]]
def raw3410step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3410step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3410step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3410step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3410step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3411 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3411Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3411step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3411step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3411step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3411step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3412 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3412Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3412step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3412step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3412step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3412step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3413 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3413Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3413step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw3413step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3414 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3414Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3414step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3414step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3415 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1]]
def raw3415Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3415step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3415step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3416 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3416Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3416step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3416step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3416step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3416step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3416step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3416step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3417 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3417Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3417step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3417step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3417step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3417step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3417step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3417step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3418 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3418Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3418step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw3418step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3418step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw3418step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3419 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3419Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3419step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3419step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3419step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3419step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3419step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3419step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3420 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1]]
def raw3420Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3420step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1]]
def raw3420step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3420step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3420step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3420step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3420step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3421 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw3421Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3421step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw3421step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3421step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3421step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3421step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3421step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3422 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw3422Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3422step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw3422step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3422step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3422step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3422step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3422step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3423 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw3423Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3423step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw3423step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3423step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3423step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3424 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1]]
def raw3424Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3424step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1]]
def raw3424step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3424step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw3424step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3424step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw3424step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3425 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1]]
def raw3425Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3425step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1]]
def raw3425step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3425step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw3425step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3425step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3425step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3426 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw3426Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3426step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw3426step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3426step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3426step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3426step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3426step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3427 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw3427Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3427step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw3427step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3427step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3427step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3427step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3427step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw3428Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3428step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw3428step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3428step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3428step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3429 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw3429Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3429step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw3429step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3429step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw3429step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3429step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw3429step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3430 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw3430Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3430step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw3430step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3430step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw3430step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3430step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3430step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3431 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 0, 0], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3431Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3431step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 0, 0], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3431step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3431step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 0, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3431step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3431step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3431step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3431step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def raw3431step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3432 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3432Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3432step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3432step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3432step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3432step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3432step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]
def raw3432step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3433 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3433Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3433step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3433step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3433step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3433step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3433step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]
def raw3433step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3434 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0]]
def raw3434Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3434step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0]]
def raw3434step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3434step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw3434step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3434step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 0, 0], ![-1, 1, 0], ![1, -1, 0]]
def raw3434step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3434step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![-1, 1, 0], ![1, -1, 0]]
def raw3434step3Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3434step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]
def raw3434step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3435 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0]]
def raw3435Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3435step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0]]
def raw3435step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3435step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw3435step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3435step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 0, 0], ![-1, 1, 0], ![1, -1, 0]]
def raw3435step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3435step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![-1, 1, 0], ![1, -1, 0]]
def raw3435step3Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3435step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]
def raw3435step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3436 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3436Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3436step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3436step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3436step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![1, -1]]
def raw3436step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3436step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw3436step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3437 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3437Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3437step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![-1, 1], ![1, -1], ![1, -1]]
def raw3437step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3437step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw3437step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3438 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0]]
def raw3438Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3438step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw3438step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3438step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3438step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3438step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]
def raw3438step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3439 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0]]
def raw3439Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3439step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw3439step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3439step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3439step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3439step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]
def raw3439step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3440 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3440Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3440step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3440step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3440step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![1, -1]]
def raw3440step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3440step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw3440step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3441 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3441Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3441step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw3441step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3442 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw3442Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3442step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3442step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3442step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3442step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3442step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]
def raw3442step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3443 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0]]
def raw3443Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3443step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3443step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3443step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3443step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3443step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]
def raw3443step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3444 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0]]
def raw3444Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3444step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0]]
def raw3444step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3444step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0]]
def raw3444step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3444step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![2, -2], ![1, -1]]
def raw3444step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3444step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw3444step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3445 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0]]
def raw3445Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3445step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw3445step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3445step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![2, -2], ![1, -1]]
def raw3445step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3445step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw3445step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3445step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw3445step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3446 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw3446Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3446step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw3446step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3446step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![2, -2], ![1, -1]]
def raw3446step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3446step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw3446step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3446step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw3446step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3447 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0]]
def raw3447Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3447step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw3447step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3447step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0]]
def raw3447step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3447step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw3447step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3447step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]
def raw3447step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3447step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![2, -2], ![-1, 1], ![-1, 1]]
def raw3447step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3447step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def raw3447step5Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3448 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw3448Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3448step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw3448step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3448step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0]]
def raw3448step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3448step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![2, -2]]
def raw3448step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3448step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw3448step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3449 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw3449Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3449step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw3449step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3449step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2]]
def raw3449step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3449step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw3449step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3449step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw3449step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3450 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw3450Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3450step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw3450step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3450step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2]]
def raw3450step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3450step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw3450step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3450step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw3450step3Labels : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical264
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw33820Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33820step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw33820step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33820step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw33820step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33820step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33820step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33820step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33820step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33821 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33821Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33821step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw33821step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33821step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw33821step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33821step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw33821step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33822 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33822Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33822step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw33822step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33822step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw33822step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33822step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw33822step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33823 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33823Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33823step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw33823step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33823step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33823step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33823step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33823step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33824 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw33824Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33824step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw33824step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33824step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33824step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33824step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33824step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33825 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw33825Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33825step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw33825step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33825step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw33825step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33825step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw33825step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33826 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33826Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33826step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw33826step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33826step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33826step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33826step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33826step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33827 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33827Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33827step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw33827step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33827step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33827step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33827step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33827step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33828 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33828Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33828step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33828step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33828step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33828step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33828step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33828step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33829 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw33829Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33829step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw33829step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33829step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33829step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33829step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33829step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33830 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw33830Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33830step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw33830step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33830step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33830step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33830step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33830step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33831 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33831Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33831step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw33831step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33831step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33831step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33831step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33831step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33832 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33832Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33832step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw33832step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33832step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33832step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33832step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33832step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33833 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33833Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33833step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33833step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33833step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33833step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33833step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33833step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33834 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33834Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33834step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw33834step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33834step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33834step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33834step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33834step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33835 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw33835Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33835step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw33835step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33835step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33835step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33835step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33835step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33836 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33836Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33836step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -3, 3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw33836step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33836step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33836step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33836step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33836step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33837 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33837Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33837step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -3, 3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw33837step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33837step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33837step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33837step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33837step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33838 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33838Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33838step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw33838step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33838step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw33838step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33839 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33839Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33840 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33840Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33841 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33841Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33842 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33842Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33842step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33842step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33843 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33843Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33843step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33843step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33844 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33844Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33845 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33845Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33845step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33845step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33845step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33845step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33846 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33846Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33846step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw33846step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33846step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33846step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw33847Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33847step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw33847step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33847step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw33847step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33847step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33847step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33848Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33848step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw33848step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33848step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw33848step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33849Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33849step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw33849step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33849step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw33849step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33850Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33850step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw33850step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33850step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw33850step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw33851Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33851step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw33851step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33851step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw33851step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33851step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw33851step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33852Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33852step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw33852step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33852step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw33852step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33853Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33853step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33853step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33853step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33853step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![0, -1, 1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33854Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33854step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33854step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33854step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33854step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33855Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33855step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33855step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33855step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33855step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![0, 0, 0], ![2, 0, -2]]
def raw33856Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33856step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw33856step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33856step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33856step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33856step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33856step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33857Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33857step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw33857step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33857step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw33857step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33858 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33858Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33858step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33858step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33858step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33858step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33859Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33859step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33859step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33859step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33859step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33860Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33860step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33860step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33860step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33860step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw33861Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33861step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw33861step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33861step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33861step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33861step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33861step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33863 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw33863Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33863step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw33863step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33863step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33863step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33863step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33863step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33864 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw33864Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33864step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw33864step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33864step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw33864step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw33866Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33866step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw33866step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33866step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33866step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33866step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33866step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33867 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw33867Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33867step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw33867step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33867step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw33867step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33868 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw33868Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33868step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw33868step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33868step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw33868step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33869 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw33869Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33869step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw33869step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33869step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw33869step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33871 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw33871Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33871step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw33871step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33871step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw33871step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw33873Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33873step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33873step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33873step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw33873step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33873step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw33873step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33874Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33874step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw33874step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33874step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33874step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33874step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33874step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33875Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33875step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33875step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33875step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33875step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33875step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33875step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33876Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33876step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw33876step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33876step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33876step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33876step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33876step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw33877Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33877step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33877step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33877step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw33877step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33877step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33877step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33877step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33877step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33878Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33878step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw33878step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33878step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33878step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33878step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33878step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33879Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33879step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33879step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33879step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33879step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33880Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33880step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33880step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33880step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33880step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33881 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33881Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33881step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33881step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw33882Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33882step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33882step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33882step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33882step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33883Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33883step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33883step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33883step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33883step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33884Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33884step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33884step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33885 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33885Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33885step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33885step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33886 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33886Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33886step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33886step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw33887Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33887step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33887step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33888 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33888Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33888step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw33888step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33889Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33889step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw33889step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33890 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33890Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33890step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw33890step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33891 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33891Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33891step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw33891step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33892 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw33892Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33892step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw33892step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33893 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33893Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33893step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33893step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33894 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33894Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33895 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33895Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33896 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33896Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33897 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33897Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33898 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw33898Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33898step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33898step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33899 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw33899Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33899step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw33899step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33900 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw33900Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33900step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw33900step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33901 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw33901Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33901step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw33901step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33902 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw33902Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33903 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![3, -2, -1]]
def raw33903Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33903step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33903step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33904 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33904Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33904step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw33904step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33904step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw33904step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33905 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33905Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33905step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw33905step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33905step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw33905step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33906 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33906Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33906step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw33906step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33906step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw33906step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33907 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw33907Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33907step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33907step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33907step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw33907step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33907step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw33907step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33908 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33908Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33908step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw33908step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33908step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw33908step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33909Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33909step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33909step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33909step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33909step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33910Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33910step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33910step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33910step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33910step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33911 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33911Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33911step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33911step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33911step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw33911step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33912 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw33912Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33912step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33912step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33912step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33912step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33912step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw33912step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33913 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33913Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33913step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33913step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33913step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw33913step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33914 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33914Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33914step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33914step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33915 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33915Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33915step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33915step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33916 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33916Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33916step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33916step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33917 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw33917Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33917step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33917step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33917step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw33917step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33918 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33918Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33918step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw33918step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33919 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33919Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33919step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw33919step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical265
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw33920 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33920Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33920step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw33920step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33921 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33921Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33921step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw33921step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33922 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw33922Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33922step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw33922step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33922step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw33922step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33923 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33923Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33923step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33923step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33924 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33924Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33924step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33924step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33925 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33925Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33925step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33925step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33926 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33926Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33926step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33926step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33927 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33927Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33927step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw33927step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw33928Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33928step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33928step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw33929Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33929step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw33929step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw33930Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33930step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2], ![-3, 3, 0]]
def raw33930step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33930step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw33930step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw33931Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33931step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw33931step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33931step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw33931step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw33932Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33932step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw33932step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33932step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33932step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33933 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![3, -2, -1]]
def raw33933Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33933step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33933step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33933step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw33933step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33933step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33933step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33934 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33934Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33934step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw33934step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33934step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33934step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33934step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33934step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33935Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33935step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33935step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33935step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33935step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33935step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33935step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33936Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33936step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw33936step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33936step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33936step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33936step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33936step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw33937Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33937step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33937step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33937step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw33937step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33937step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33937step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33937step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33937step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33938Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33938step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw33938step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33938step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33938step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33938step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33938step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33939Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33939step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33939step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33939step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw33939step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33939step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33939step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33939step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33939step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33940Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33940step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33940step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33940step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33940step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33940step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33940step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33940step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33940step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33941Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33941step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33941step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33941step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw33941step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33941step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33941step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33941step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33941step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw33942Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33942step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33942step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33942step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33942step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33942step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw33942step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33942step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33942step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33942step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33942step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33943Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33943step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33943step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33943step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw33943step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33943step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33943step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33943step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33943step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33944Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33944step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33944step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33944step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw33944step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33944step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw33944step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33945Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33945step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33945step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33945step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw33945step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33945step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw33945step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33946Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33946step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw33946step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33946step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33946step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33946step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33946step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw33947Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33947step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33947step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33947step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33947step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33947step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw33947step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33947step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw33947step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33948Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33948step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw33948step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33948step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw33948step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33948step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw33948step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33949Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33949step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw33949step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33949step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw33949step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33949step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw33949step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33950Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33950step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw33950step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33950step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw33950step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33950step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw33950step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33951 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33951Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33951step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw33951step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33951step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw33951step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33951step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw33951step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw33952Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33952step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw33952step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33952step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw33952step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33952step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw33952step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33952step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw33952step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33953Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33953step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw33953step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33953step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33953step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33953step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33953step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33954Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33954step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw33954step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33954step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33954step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33954step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33954step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33955Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33955step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw33955step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33955step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33955step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33955step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33955step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33956Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33956step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33956step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33956step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33956step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33956step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33956step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33957Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33957step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw33957step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33957step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33957step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33957step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33957step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw33958Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33958step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw33958step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33958step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33958step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33958step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33958step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw33959Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33959step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw33959step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33959step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw33959step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33959step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw33959step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw33960Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33960step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw33960step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33960step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw33960step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33960step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw33960step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw33961Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33961step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -2, 3]]
def raw33961step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33961step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw33961step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33961step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw33961step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw33962Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33962step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw33962step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33962step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw33962step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33962step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw33962step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![3, -2, -1]]
def raw33963Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33963step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33963step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33963step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw33963step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33963step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw33963step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33963step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw33963step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33964Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33964step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33964step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33965Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33965step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33965step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33966Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33966step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33966step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33967Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33967step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw33967step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33968Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33969 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw33969Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33969step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw33969step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33970Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33970step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33970step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33970step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33970step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33971Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33971step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33971step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33971step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33971step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw33972Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33972step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33972step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33972step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33972step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33973Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33973step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw33973step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33973step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw33973step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33974Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33974step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw33974step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33974step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw33974step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw33975Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33975step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw33975step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33975step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw33975step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33976Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33976step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33976step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33976step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33976step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![0, -1, 1], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33977Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33977step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33977step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33977step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33977step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33978Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33978step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33978step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33978step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33978step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![0, 1, -1], ![2, -1, -1]]
def raw33979Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33979step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw33979step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33979step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw33979step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw33980Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33980step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw33980step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33980step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw33980step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw33981Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33981step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw33981step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33981step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw33981step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw33982Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33982step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw33982step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33982step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw33982step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw33983Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33983step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw33983step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33983step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw33983step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33984Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33984step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw33984step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33984step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw33984step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33984step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw33984step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33985 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![2, -2, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw33985Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33985step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw33985step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33985step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw33985step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33986Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33986step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw33986step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33986step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw33986step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33986step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw33986step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33987 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw33987Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33987step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw33987step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33987step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw33987step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw33988Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33988step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw33988step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33988step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw33988step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33988step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw33988step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33989Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33989step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw33989step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33989step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33989step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33989step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33989step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33990Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33990step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw33990step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33990step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw33990step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33990step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw33990step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33991Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33991step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33991step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33991step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw33991step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33991step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33991step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33991step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33991step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw33992Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33992step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33992step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33992step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw33992step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33992step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33992step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33992step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33992step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33993Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33993step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw33993step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33993step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33993step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33993step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33993step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33994Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33994step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33994step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33995Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33995step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33995step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33996Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33996step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33996step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33996step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33996step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw33997Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33997step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33997step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33997step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33997step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33998Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33998step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33998step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33998step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw33998step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33998step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33998step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33998step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33998step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33999Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33999step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw33999step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34000Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34000step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34000step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34001 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34001Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34001step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34001step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34001step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34001step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34002 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw34002Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34002step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34002step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34002step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34002step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34003Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34003step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34003step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34004 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34004Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34004step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34004step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34005 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34005Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34005step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34005step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34006 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34006Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34006step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34006step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![2, 0, -2]]
def raw34007Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34007step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34007step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34008 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34008Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34008step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw34008step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34009Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34010 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34010Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34011 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34011Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34012 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34012Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34012step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34012step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34013 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw34013Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34013step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw34013step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34014 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw34014Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34015 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw34015Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34016 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw34016Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw34017Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw34017step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34018 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw34018Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34018step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw34018step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34019 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34019Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34019step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw34019step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34019step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34019step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34020Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34020step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw34020step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34020step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34020step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34021Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34021step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34021step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34021step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw34021step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34021step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34021step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34022 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw34022Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34022step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34022step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34022step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw34022step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34022step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34022step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34023 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34023Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34023step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34023step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34023step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34023step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34024Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34024step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34024step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34024step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34024step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34025Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34025step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34025step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34025step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34025step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34026Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34026step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34026step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34026step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34026step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34026step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw34026step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw34027Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34027step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34027step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34027step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34027step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34027step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw34027step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34028 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34028Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34028step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34028step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34028step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34028step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34028step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34028step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34029 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34029Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34029step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34029step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34030 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34030Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34030step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34030step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34031 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34031Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34031step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34031step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34031step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw34031step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34032 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw34032Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34032step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34032step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34032step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw34032step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34033 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34033Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34033step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34033step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34034 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34034Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34034step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34034step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34035 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34035Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34035step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34035step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34036 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34036Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34036step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34036step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34037 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![2, 0, -2]]
def raw34037Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34037step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34037step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34037step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw34037step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34038 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34038Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34038step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34038step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34039 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34039Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34039step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34039step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34040 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34040Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34040step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34040step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34041 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34041Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34041step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34041step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34042 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34042Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34042step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34042step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34042step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw34042step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34043 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw34043Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34043step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34043step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34044 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw34044Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34044step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw34044step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34045 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw34045Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34045step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![-2, 0, 2], ![-3, 3, 0]]
def raw34045step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34045step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw34045step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34046 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw34046Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34046step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw34046step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34046step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw34046step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34047 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw34047Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34047step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw34047step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34047step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw34047step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34047step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw34047step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical266
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw34048 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw34048Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34048step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw34048step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34048step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw34048step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34048step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw34048step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34049 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34049Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34049step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw34049step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34049step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34049step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34049step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34049step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34050 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34050Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34050step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw34050step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34050step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw34050step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34050step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw34050step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34051 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34051Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34051step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34051step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34051step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw34051step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34051step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34051step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34051step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34051step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34052 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw34052Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34052step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34052step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34052step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw34052step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34052step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34052step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34052step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34052step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34053 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34053Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34053step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw34053step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34053step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw34053step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34053step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw34053step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34054 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34054Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34054step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34054step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34054step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw34054step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34054step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34054step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34054step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34054step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34055 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34055Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34055step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34055step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34055step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw34055step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34055step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw34055step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34055step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw34055step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34056 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34056Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34056step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34056step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34056step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34056step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34056step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw34056step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34056step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34056step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34056step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34056step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34057 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw34057Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34057step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34057step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34057step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34057step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34057step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw34057step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34057step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34057step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34057step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34057step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34058 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34058Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34058step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34058step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34058step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw34058step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34058step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw34058step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34058step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw34058step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34059 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34059Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34059step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34059step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34059step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34059step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34059step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34059step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34060 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34060Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34060step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34060step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34060step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34060step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34060step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34060step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34061 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34061Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34061step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34061step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34061step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34061step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34061step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34061step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34061step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34061step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34062 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw34062Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34062step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34062step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34062step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34062step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34062step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34062step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34062step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34062step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34063 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34063Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34063step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34063step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34063step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34063step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34063step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34063step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34064 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34064Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34064step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw34064step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34064step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34064step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34064step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34064step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34065 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34065Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34065step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw34065step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34065step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34065step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34065step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34065step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34066 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34066Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34066step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw34066step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34066step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw34066step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34066step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw34066step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34067 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![2, 0, -2]]
def raw34067Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34067step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34067step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34067step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw34067step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34067step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34067step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34067step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34067step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34068 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34068Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34068step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw34068step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34068step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34068step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34068step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34068step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34069 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34069Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34069step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw34069step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34069step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34069step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34069step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34069step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34070 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34070Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34070step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw34070step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34070step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34070step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34070step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34070step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34071 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34071Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34071step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw34071step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34071step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw34071step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34071step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw34071step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34072 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34072Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34072step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34072step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34072step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw34072step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34072step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34072step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34072step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34072step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34073 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw34073Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34073step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw34073step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34073step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34073step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34073step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34073step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34074 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw34074Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34074step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw34074step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34074step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw34074step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34074step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw34074step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34075 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw34075Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34075step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw34075step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34075step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw34075step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34075step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw34075step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34076 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw34076Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34076step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, -1, 3]]
def raw34076step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34076step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw34076step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34076step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw34076step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34077 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw34077Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34077step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw34077step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34077step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw34077step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34077step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw34077step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34077step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw34077step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34078 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw34078Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34078step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw34078step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34078step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw34078step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34078step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw34078step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34078step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw34078step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34079 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34079Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34079step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34079step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34079step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34079step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34080 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34080Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34080step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34080step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34080step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34080step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34081 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw34081Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34081step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw34081step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34081step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34081step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34081step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34081step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34082 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34082Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34082step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw34082step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34082step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw34082step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34083 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34083Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34083step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw34083step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34083step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw34083step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34084 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw34084Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34084step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw34084step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34084step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw34084step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34084step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw34084step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34085 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34085Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34085step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw34085step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34085step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw34085step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34086 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34086Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34086step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw34086step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34086step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw34086step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34087 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34087Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34087step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw34087step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34087step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw34087step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34088 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw34088Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34088step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw34088step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34088step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw34088step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34089 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw34089Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34089step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw34089step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34089step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw34089step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34090 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw34090Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34090step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw34090step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34090step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw34090step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34091 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw34091Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34091step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw34091step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34091step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw34091step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34092 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw34092Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34092step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw34092step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34092step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw34092step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34093 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw34093Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34093step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw34093step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34093step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw34093step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34094 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw34094Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34094step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw34094step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34094step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw34094step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34095 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw34095Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34095step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw34095step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34095step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw34095step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34096 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw34096Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34096step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34096step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34096step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34096step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34096step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34096step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34097 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw34097Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34097step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw34097step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34097step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw34097step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34098 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw34098Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34098step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw34098step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34098step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw34098step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34099 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw34099Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34099step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw34099step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34099step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34099step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34099step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34099step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34100 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw34100Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34100step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34100step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34100step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34100step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34101 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw34101Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34101step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw34101step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34101step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw34101step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34101step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw34101step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34102 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw34102Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34102step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw34102step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34102step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw34102step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34103 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw34103Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34103step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw34103step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34103step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw34103step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34104Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34104step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34104step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34104step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw34104step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34104step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw34104step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34104step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw34104step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34105Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34105step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw34105step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34105step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw34105step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34105step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw34105step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34106 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34106Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34106step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34106step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34106step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw34106step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34106step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34106step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34106step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34106step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34107 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw34107Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34107step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw34107step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34107step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw34107step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34107step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34107step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34107step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34107step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw34108Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34108step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw34108step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34108step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34108step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34108step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34108step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34108step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34108step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34109 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34109Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34109step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34109step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34109step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34109step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34109step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34109step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34110 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34110Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34110step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34110step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34111 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34111Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34111step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw34111step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw34112Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34112step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw34112step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34113 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw34113Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34113step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34113step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34114Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34114step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34114step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34114step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34114step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34115 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34115Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34115step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34115step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34116 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![0, 1, -1], ![2, -2, 0]]
def raw34116Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34116step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 0, -2], ![0, 1, -1], ![2, -2, 0]]
def raw34116step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34116step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34116step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34117 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw34117Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34117step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw34117step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34117step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34117step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34118 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw34118Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34118step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw34118step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34118step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34118step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34119 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw34119Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34119step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34119step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34120 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw34120Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34120step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw34120step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34120step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34120step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34121 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw34121Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34121step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw34121step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34121step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34121step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34122 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw34122Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34122step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw34122step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34122step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw34122step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34123 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw34123Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34123step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw34123step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34124 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw34124Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34124step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw34124step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34125 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![3, -3, 0]]
def raw34125Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34125step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![0, 1, -1], ![3, -3, 0]]
def raw34125step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34125step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw34125step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34126 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34126Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34126step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34126step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34126step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw34126step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34126step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw34126step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34126step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw34126step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34127 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34127Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34127step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw34127step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34127step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw34127step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34127step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw34127step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34128 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34128Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34128step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34128step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34128step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw34128step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34128step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34128step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34128step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34128step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34129 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw34129Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34129step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw34129step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34129step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw34129step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34129step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34129step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34129step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34129step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34130 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw34130Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34130step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw34130step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34130step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34130step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34130step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34130step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34130step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34130step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34131 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34131Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34131step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34131step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34131step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34131step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34131step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw34131step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34131step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw34131step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34131step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw34131step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34132 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34132Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34132step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw34132step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34132step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw34132step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34132step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw34132step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34133 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34133Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34133step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw34133step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34133step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34133step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34133step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34133step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34134 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw34134Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34134step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw34134step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34134step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34134step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34134step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34134step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34135 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw34135Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34135step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34135step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34135step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34135step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34135step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34135step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34136 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34136Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34136step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34136step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34136step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw34136step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34136step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw34136step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34136step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw34136step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34137 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34137Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34137step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw34137step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34137step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw34137step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34137step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw34137step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34138 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![0, 1, -1], ![2, -2, 0]]
def raw34138Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34138step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 0, -2], ![0, 1, -1], ![2, -2, 0]]
def raw34138step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34138step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw34138step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34138step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34138step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34138step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34138step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw34139Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34139step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw34139step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34139step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34139step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34139step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34139step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34139step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34139step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34140 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw34140Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34140step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw34140step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34140step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw34140step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34140step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw34140step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34140step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw34140step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34141 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw34141Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34141step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw34141step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34141step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw34141step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34141step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw34141step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34142 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw34142Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34142step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw34142step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34142step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw34142step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34142step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw34142step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34142step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw34142step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34143 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw34143Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34143step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw34143step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34143step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw34143step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34143step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34143step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34143step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34143step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34144 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw34144Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34144step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw34144step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34144step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -3, 3], ![-1, 0, 1], ![-2, 1, 1]]
def raw34144step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34144step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw34144step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34144step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw34144step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34145 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw34145Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34145step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -3, 3], ![-1, 0, 1], ![-2, 1, 1]]
def raw34145step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34145step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw34145step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34145step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw34145step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34146 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw34146Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34146step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw34146step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34146step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw34146step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34146step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw34146step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34147 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![3, -3, 0]]
def raw34147Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34147step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![0, 1, -1], ![3, -3, 0]]
def raw34147step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34147step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -3, 3], ![-1, 1, 0], ![-2, 1, 1]]
def raw34147step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34147step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw34147step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34147step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw34147step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34148 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34148Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34148step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34148step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34148step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34148step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34149 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34149Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34149step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34149step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34149step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34149step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34150Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34150step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34150step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34151 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34151Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34151step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34151step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34151step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34151step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34152 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw34152Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34152step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw34152step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34152step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34152step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34153 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw34153Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34153step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw34153step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34153step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw34153step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34154 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![2, -2], ![1, -1], ![0, 0]]
def raw34154Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34154step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![2, -2], ![1, -1]]
def raw34154step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34154step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![2, -2], ![1, -1]]
def raw34154step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34154step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![1, -1]]
def raw34154step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34154step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw34154step3Labels : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical267
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw34185 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![0, 0, 0], ![2, -3, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw34185Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34185step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![2, -3, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw34185step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34185step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw34185step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34185step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw34185step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34185step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw34185step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34186 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![0, 0, 0], ![2, -3, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw34186Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34186step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![2, -3, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw34186step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34186step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw34186step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34186step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw34186step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34186step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw34186step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34187 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, 1, 0], ![2, -3, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw34187Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34187step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw34187step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34187step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw34187step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34187step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw34187step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34188 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![2, -3, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34188Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34188step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![2, -3, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34188step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34188step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw34188step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34188step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw34188step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34189 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![2, -3, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw34189Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34189step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![2, -3, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw34189step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34189step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw34189step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34189step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw34189step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34190 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw34190Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34190step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![1, -2, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw34190step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34190step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -2, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw34190step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34190step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw34190step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34190step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw34190step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34191 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw34191Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34191step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw34191step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34191step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw34191step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34191step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw34191step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34191step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw34191step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34192 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw34192Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34192step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw34192step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34192step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw34192step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34192step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw34192step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34193 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw34193Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34193step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -2, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw34193step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34193step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2], ![2, -3, 1]]
def raw34193step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34193step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2], ![2, -3, 1]]
def raw34193step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34194 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw34194Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34194step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw34194step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34194step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw34194step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34194step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34194step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34194step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34194step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34195 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw34195Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34195step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw34195step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34195step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw34195step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34195step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34195step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34195step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34195step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34196 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34196Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34196step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34196step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34196step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw34196step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34196step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34196step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34196step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34196step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34197 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34197Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34197step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw34197step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34197step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34197step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34197step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34197step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34198 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34198Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34198step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34198step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34198step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw34198step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34198step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34198step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34198step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34198step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34199 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![0, 0, 0], ![2, -1, -1]]
def raw34199Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34199step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34199step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34199step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34199step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34199step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw34199step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34199step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw34199step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34199step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw34199step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw34200Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34200step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw34200step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34200step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34200step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34200step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34200step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34200step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34200step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34201Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34201step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34201step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34201step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34201step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34201step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34201step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34202Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34202step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34202step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34203 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34203Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34203step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw34203step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34204 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![0, 0, 0], ![2, -1, -1]]
def raw34204Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34204step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34204step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34205 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw34205Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34205step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34205step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34206 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34206Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34206step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34206step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34206step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw34206step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34207 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34207Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34207step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw34207step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34208 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![0, 0, 0], ![2, -1, -1]]
def raw34208Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34208step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw34208step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34208step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw34208step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34208step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw34208step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34209 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0], ![1, 0, -1]]
def raw34209Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34209step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 0, -2], ![1, -1, 0], ![1, 0, -1]]
def raw34209step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34209step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34209step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34210 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34210Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34210step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34210step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34211 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34211Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34212 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34212Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34212step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34212step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34213 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![1, 0, -1]]
def raw34213Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34213step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![1, 0, -1]]
def raw34213step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34213step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34213step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34214 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw34214Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34214step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw34214step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34214step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw34214step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34215 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw34215Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34215step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw34215step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34216 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw34216Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34216step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw34216step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34217 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![0, 0, 0], ![3, -2, -1]]
def raw34217Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34217step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw34217step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34217step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw34217step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34218 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34218Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34218step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34218step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34218step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw34218step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34218step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34218step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34218step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34218step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34219 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34219Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34219step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw34219step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34219step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34219step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34219step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34219step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34220 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34220Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34220step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34220step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34220step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw34220step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34220step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34220step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34220step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34220step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![0, 0, 0], ![2, -1, -1]]
def raw34221Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34221step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34221step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34221step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34221step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34221step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw34221step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34221step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw34221step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34221step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw34221step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34222 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw34222Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34222step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw34222step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34222step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34222step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34222step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34222step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34222step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34222step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34223Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34223step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34223step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34223step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34223step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34223step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw34223step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34223step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34223step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34223step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34223step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34224 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34224Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34224step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw34224step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34224step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34224step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34224step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34224step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34225 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34225Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34225step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw34225step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34225step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34225step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34225step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34225step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34226 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![0, 0, 0], ![2, -1, -1]]
def raw34226Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34226step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34226step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34226step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw34226step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34226step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34226step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34226step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34226step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34227 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw34227Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34227step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34227step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34227step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34227step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34227step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34227step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34228 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34228Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34228step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34228step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34228step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw34228step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34228step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw34228step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34228step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw34228step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34229 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34229Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34229step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw34229step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34229step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw34229step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34229step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw34229step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34230 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![0, 0, 0], ![2, -1, -1]]
def raw34230Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34230step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw34230step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34230step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw34230step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34230step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw34230step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34230step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw34230step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34230step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw34230step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34231 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0], ![1, 0, -1]]
def raw34231Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34231step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 0, -2], ![1, -1, 0], ![1, 0, -1]]
def raw34231step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34231step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34231step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34231step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34231step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34231step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34231step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34232Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34232step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34232step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34232step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw34232step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34232step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw34232step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34232step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw34232step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34233 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34233Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34233step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw34233step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34233step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw34233step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34233step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw34233step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34234 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34234Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34234step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34234step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34234step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw34234step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34234step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw34234step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34234step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw34234step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34235 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![1, 0, -1]]
def raw34235Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34235step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![1, 0, -1]]
def raw34235step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34235step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw34235step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34235step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw34235step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34235step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw34235step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34236 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw34236Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34236step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw34236step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34236step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw34236step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34236step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw34236step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34236step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw34236step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34237 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw34237Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34237step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw34237step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34237step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw34237step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34237step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw34237step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34238 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw34238Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34238step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw34238step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34238step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw34238step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34238step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw34238step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34238step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw34238step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34239 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![0, 0, 0], ![3, -2, -1]]
def raw34239Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34239step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw34239step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34239step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw34239step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34239step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, -2, 3], ![-2, 1, 1]]
def raw34239step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34239step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw34239step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34239step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw34239step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34240 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34240Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34240step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34240step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34240step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34240step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34241 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34241Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34241step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34241step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34242 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34242Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34242step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34242step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34242step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw34242step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34243 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34243Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34243step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34243step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34243step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34243step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34243step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34243step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34244 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34244Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34244step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34244step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34244step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34244step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34245 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw34245Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34245step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw34245step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34245step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw34245step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34245step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34245step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34245step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34245step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34246 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34246Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34246step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34246step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34246step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw34246step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34246step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw34246step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34246step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw34246step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34247 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34247Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34247step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34247step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34247step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34247step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![1, -1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34248Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34248step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34248step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34248step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34248step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34249 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw34249Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34249step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34249step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34249step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34249step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34250Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34250step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34250step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34250step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34250step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34251 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![0, 0, 0], ![2, -3, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34251Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34251step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![2, -3, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34251step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34251step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw34251step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34251step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw34251step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34252 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![0, 0, 0], ![2, -3, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34252Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34252step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![2, -3, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34252step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34252step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw34252step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34252step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw34252step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34253 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 1, 0], ![2, -3, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34253Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34253step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw34253step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34253step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw34253step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34254 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![2, -3, 1], ![0, 1, -1], ![2, -1, -1]]
def raw34254Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34254step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![2, -3, 1], ![0, 1, -1], ![2, -1, -1]]
def raw34254step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34254step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-3, 1, 2]]
def raw34254step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34254step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw34254step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34254step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw34254step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34255 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![2, -3, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34255Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34255step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![2, -3, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34255step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34255step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34255step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34255step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34255step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34256 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1], ![2, -1, -1]]
def raw34256Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34256step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![1, -2, 1], ![2, -1, -1], ![2, -1, -1]]
def raw34256step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34256step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw34256step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34256step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw34256step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34257 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1], ![2, -1, -1]]
def raw34257Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34257step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![1, -2, 1], ![2, -1, -1], ![2, -1, -1]]
def raw34257step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34257step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw34257step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34257step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw34257step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34258 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1], ![2, -1, -1]]
def raw34258Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34258step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw34258step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34258step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw34258step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34259 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1], ![1, 0, -1]]
def raw34259Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34259step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![2, -1, -1], ![1, 0, -1]]
def raw34259step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34259step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34259step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34259step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34259step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34260 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -2, -1]]
def raw34260Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34260step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, -2, -1]]
def raw34260step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34260step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw34260step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34260step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw34260step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34261 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -2, -1]]
def raw34261Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34261step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![3, -2, -1]]
def raw34261step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34261step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw34261step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34261step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw34261step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34262 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, -2, -1]]
def raw34262Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34262step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw34262step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34262step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw34262step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34263 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![3, -2, -1]]
def raw34263Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34263step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![0, 1, -1], ![3, -2, -1]]
def raw34263step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34263step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw34263step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34263step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw34263step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34264 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![0, 0, 0], ![2, -3, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw34264Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34264step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![2, -3, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw34264step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34264step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw34264step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34264step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw34264step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34264step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw34264step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34265 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![0, 0, 0], ![2, -3, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw34265Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34265step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![2, -3, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw34265step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34265step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw34265step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34265step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw34265step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34265step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw34265step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34266 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, 1, 0], ![2, -3, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw34266Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34266step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw34266step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34266step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw34266step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34266step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw34266step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34267 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![2, -3, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw34267Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34267step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![2, -3, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw34267step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34267step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw34267step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34267step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw34267step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34268 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw34268Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34268step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw34268step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34268step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw34268step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34268step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw34268step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34268step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw34268step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34269 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw34269Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34269step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -2, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw34269step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34269step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw34269step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34269step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw34269step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34269step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw34269step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34270 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34270Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34270step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34270step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34270step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw34270step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34270step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34270step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34270step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34270step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34271 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34271Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34271step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw34271step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34271step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34271step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34271step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34271step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34272 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34272Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34272step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34272step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34272step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw34272step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34272step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34272step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34272step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34272step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34273 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw34273Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34273step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw34273step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34273step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw34273step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34273step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34273step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34273step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34273step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34274 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34274Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34274step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34274step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34274step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34274step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34274step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34274step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34274step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34274step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34275 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34275Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34275step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34275step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34275step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34275step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34276 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34276Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34277 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34277Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34277step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34277step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34278 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw34278Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34278step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34278step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34279 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34279Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34280 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34280Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34280step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34280step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34280step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34280step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34281 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34281Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34281step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34281step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34282 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw34282Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34282step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw34282step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34282step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34282step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34283 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34283Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34283step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34283step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34283step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34283step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34284 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34284Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34284step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34284step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34285 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34285Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34286 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34286Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34286step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34286step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34287 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw34287Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34287step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw34287step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34287step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34287step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34288 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw34288Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34288step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw34288step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34289 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw34289Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34290 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw34290Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34290step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw34290step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34291 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw34291Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34291step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw34291step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34291step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw34291step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34292 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34292Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34292step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34292step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34292step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34292step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34292step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34292step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34292step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34292step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34293 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34293Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34293step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34293step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34293step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34293step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34293step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34293step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34294 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34294Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34294step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34294step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34294step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw34294step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34294step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34294step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34294step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34294step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34295 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw34295Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34295step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34295step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34295step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34295step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34295step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34295step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34295step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34295step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34295step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34295step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34296 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw34296Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34296step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw34296step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34296step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34296step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34296step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34296step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34296step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34296step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34297 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34297Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34297step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34297step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34297step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34297step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34297step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34297step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34298 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34298Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34298step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34298step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34299 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34299Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34299step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34299step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34300 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw34300Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34300step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34300step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34301 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw34301Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34301step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34301step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34302 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34302Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34302step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34302step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34302step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw34302step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34303 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34303Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34303step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw34303step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical268
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw34304 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw34304Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34304step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, 0, -2]]
def raw34304step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34304step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw34304step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34305 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw34305Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34305step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw34305step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34305step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34305step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34306 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34306Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34306step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34306step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34307 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34307Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34308 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34308Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34308step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34308step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34309 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw34309Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34309step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw34309step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34309step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34309step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34310 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw34310Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34310step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw34310step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34310step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw34310step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34311 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw34311Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34311step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw34311step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34312 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw34312Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34312step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw34312step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34313 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![3, -1, -2]]
def raw34313Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34313step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw34313step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34313step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw34313step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34314 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34314Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34314step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34314step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34314step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw34314step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34314step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw34314step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34314step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw34314step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34315 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34315Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34315step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw34315step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34315step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw34315step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34316 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw34316Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34316step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34316step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34316step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34316step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34316step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw34316step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34316step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw34316step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34317 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw34317Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34317step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw34317step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34317step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw34317step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34317step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw34317step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34318 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34318Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34319 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw34319Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34319step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34319step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34320 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw34320Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34321 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34321Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34321step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34321step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34321step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw34321step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34322Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34322step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw34322step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34323 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![2, 1, -3]]
def raw34323Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34323step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw34323step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34323step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw34323step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34324 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 2, -3]]
def raw34324Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34324step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 2, -3]]
def raw34324step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34324step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw34324step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34325 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw34325Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34325step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw34325step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34326 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw34326Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34327 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 2, -3]]
def raw34327Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34327step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 2, -3]]
def raw34327step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34327step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw34327step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34350 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34350Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34350step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34350step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34350step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw34350step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34350step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw34350step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34350step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw34350step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34351 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34351Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34351step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw34351step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34351step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw34351step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34352 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw34352Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34352step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34352step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34352step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34352step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34352step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw34352step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34352step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw34352step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34353 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw34353Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34353step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw34353step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34353step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw34353step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34353step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw34353step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34353step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw34353step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34354 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34354Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34354step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw34354step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34354step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw34354step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34354step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw34354step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34355 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw34355Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34355step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34355step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34355step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw34355step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34355step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw34355step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34355step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw34355step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34356 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw34356Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34356step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw34356step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34356step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw34356step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34356step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw34356step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34357 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34357Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34357step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34357step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34357step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw34357step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34357step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw34357step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34357step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw34357step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34358 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34358Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34358step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw34358step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34358step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw34358step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34358step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw34358step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34359 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![2, 1, -3]]
def raw34359Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34359step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw34359step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34359step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw34359step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34359step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-3, 1, 2]]
def raw34359step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34359step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw34359step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34359step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw34359step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34360 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 2, -3]]
def raw34360Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34360step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 2, -3]]
def raw34360step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34360step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw34360step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34360step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw34360step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34360step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw34360step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34361 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw34361Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34361step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw34361step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34361step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw34361step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34361step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw34361step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34361step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw34361step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34362 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw34362Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34362step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw34362step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34362step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw34362step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34362step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw34362step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34363 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 2, -3]]
def raw34363Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34363step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 2, -3]]
def raw34363step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34363step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw34363step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34363step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw34363step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34363step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw34363step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34364 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34364Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34364step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34364step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34365 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34365Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34365step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34365step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34366 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34366Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34367 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34367Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34367step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34367step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34367step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw34367step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34368 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw34368Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34368step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw34368step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34369 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34369Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34370 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34370Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34370step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34370step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34371 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw34371Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34371step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34371step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34372 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw34372Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34373 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34373Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34373step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34373step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34373step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34373step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34373step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34373step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34374 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34374Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34374step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34374step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34374step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34374step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34374step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34374step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34375 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34375Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34375step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw34375step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34375step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34375step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34375step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34375step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34376 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, 0, -2]]
def raw34376Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34376step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw34376step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34376step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34376step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34376step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34376step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34377 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34377Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34377step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34377step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34377step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34377step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34377step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34377step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34378 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34378Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34378step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34378step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34379 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34379Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34380 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34380Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34380step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34380step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34381 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![2, 0, -2]]
def raw34381Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34381step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34381step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34382Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34383Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34383step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw34383step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34384Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34384step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw34384step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34385 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![2, 0, -2]]
def raw34385Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34385step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw34385step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34386 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34386Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34386step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34386step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34387 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw34387Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34388 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw34388Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34388step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw34388step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34389 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw34389Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34390 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, 1, -2]]
def raw34390Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34390step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34390step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34391 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw34391Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34392 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw34392Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34392step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw34392step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34393 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw34393Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34394 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![3, -1, -2]]
def raw34394Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34394step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw34394step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34395 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![0, 1, -1], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw34395Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34395step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw34395step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34395step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34395step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34395step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34395step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34396 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw34396Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34396step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw34396step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34396step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34396step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34396step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34396step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34397 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw34397Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34397step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw34397step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34397step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34397step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34397step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34397step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw34398Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34398step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw34398step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34398step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34398step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34398step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34398step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34399 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw34399Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34399step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw34399step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34399step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34399step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34399step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34399step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34400 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw34400Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34400step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw34400step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34400step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34400step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34400step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34400step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34401 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw34401Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34401step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw34401step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34401step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34401step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34401step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34401step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34402 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw34402Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34402step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw34402step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34402step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw34402step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34402step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34402step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34402step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34402step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34403 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw34403Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34403step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw34403step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34403step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34403step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34403step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34403step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34404 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw34404Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34404step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34404step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34404step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34404step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34404step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34404step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34405 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw34405Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34405step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]
def raw34405step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34406 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0]]
def raw34406Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34406step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw34406step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34406step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw34406step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34407 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, -2, 0]]
def raw34407Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34407step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![2, -2, 0]]
def raw34407step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34407step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![2, -2], ![1, -1], ![2, -2]]
def raw34407step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34407step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![2, -2], ![2, -2]]
def raw34407step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34408 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, -2, 0]]
def raw34408Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34408step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![-1, 1], ![2, -2], ![1, -1], ![2, -2]]
def raw34408step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34408step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2], ![2, -2]]
def raw34408step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34409 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![2, -2, 0]]
def raw34409Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34409step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0]]
def raw34409step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34409step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw34409step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34409step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw34409step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34410 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw34410Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34410step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34410step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34411 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw34411Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34411step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34411step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34412 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw34412Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34412step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34412step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34413 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw34413Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34413step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34413step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34414 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw34414Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34414step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34414step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34415 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34415Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34416 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-3, 3], ![1, -1], ![1, -1], ![1, -1], ![0, 0]]
def raw34416Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34416step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw34416step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34416step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw34416step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34417 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34417Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34417step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw34417step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34421 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34421Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34421step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw34421step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34424 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw34424Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34424step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw34424step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34426 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34426Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34427 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34427Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34427step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34427step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw34428Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34428step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw34428step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34429 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw34429Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34429step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw34429step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34430 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34430Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34430step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34430step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34431 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34431Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34431step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34431step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34431step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34431step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical269
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw34432 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw34432Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34432step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw34432step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34433 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw34433Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34433step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw34433step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34434 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34434Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34434step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34434step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34435 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![0, 1, -1], ![1, 0, -1]]
def raw34435Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34435step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw34435step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34436 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1], ![0, 1, -1]]
def raw34436Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34436step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw34436step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34437 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw34437Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34437step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34437step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34438 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1], ![0, 1, -1]]
def raw34438Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34438step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw34438step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34439 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34439Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34439step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34439step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34440 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw34440Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34440step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw34440step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34440step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34440step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34441 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw34441Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34441step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw34441step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34441step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34441step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34442 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34442Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34442step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34442step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34442step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34442step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34443 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34443Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34443step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34443step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34443step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34443step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34444 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34444Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34444step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34444step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34444step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34444step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34445 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw34445Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34445step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw34445step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34445step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw34445step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34445step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw34445step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34446 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw34446Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34446step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw34446step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34446step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw34446step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34446step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw34446step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34447 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34447Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34447step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34447step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34447step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34447step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34448 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34448Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34448step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34448step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34448step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34448step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34449 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34449Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34449step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34449step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34449step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34449step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34450 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw34450Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34450step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw34450step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34450step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34450step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34450step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34450step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34451 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw34451Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34451step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw34451step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34451step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34451step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34451step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34451step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34452 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34452Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34452step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34452step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34452step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34452step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34453 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34453Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34453step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34453step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34453step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34453step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34454 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34454Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34454step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34454step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34454step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34454step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34455 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0]]
def raw34455Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34455step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw34455step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34455step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34455step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34455step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34455step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34456 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0]]
def raw34456Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34456step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw34456step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34456step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34456step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34456step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34456step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34457 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0]]
def raw34457Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34457step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34457step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34457step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34457step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0]]
def raw34458Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34458step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34458step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34458step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34458step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0]]
def raw34459Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34459step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34459step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34459step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34459step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw34460Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34460step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34460step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34460step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34460step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34461 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0], ![0, 0, 0]]
def raw34461Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34461step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34461step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34461step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34461step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34461step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34461step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw34462Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34462step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34462step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34462step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34462step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw34463Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34463step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34463step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34463step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34463step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0]]
def raw34464Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34464step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34464step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34464step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34464step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34464step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34464step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34478 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw34478Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34478step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34478step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34479 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw34479Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34479step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34479step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34480 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw34480Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34480step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34480step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34481 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw34481Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34481step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34481step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34482 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw34482Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34482step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34482step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34483 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw34483Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34483step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw34483step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34483step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34483step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34484 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw34484Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34484step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34484step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34485 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw34485Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34485step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34485step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34486 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw34486Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34486step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34486step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34487 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw34487Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34487step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34487step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34488 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw34488Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34488step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34488step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34489 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw34489Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34489step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34489step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34490 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![0, 1, -1], ![1, -2, 1]]
def raw34490Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34490step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34490step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34491 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![0, -1, 1]]
def raw34491Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34491step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34491step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34492 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw34492Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34492step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34492step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34493 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw34493Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34493step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34493step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34494 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1], ![1, -2, 1]]
def raw34494Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34494step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34494step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34495 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![0, -1, 1]]
def raw34495Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34495step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34495step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34496 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw34496Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34497 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw34497Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34497step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw34497step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34498 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw34498Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34498step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34498step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34498step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34498step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34498step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34498step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34499 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw34499Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34499step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw34499step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34499step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34499step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34499step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34499step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34500 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw34500Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34500step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw34500step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34500step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34500step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34500step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34500step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw34501Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34501step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw34501step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34501step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34501step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34501step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34501step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw34502Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34502step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34502step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34502step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34502step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34502step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34502step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34503 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw34503Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34503step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw34503step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34503step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34503step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34503step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34503step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34503step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34503step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34504 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw34504Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34504step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw34504step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34504step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34504step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34504step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34504step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34505 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw34505Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34505step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw34505step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34505step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34505step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34505step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34505step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34506 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw34506Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34506step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw34506step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34506step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34506step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34506step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34506step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34507 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw34507Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34507step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw34507step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34507step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34507step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34507step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34507step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34508 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw34508Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34508step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw34508step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34508step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34508step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34508step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34508step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34509 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw34509Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34509step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw34509step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34509step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34509step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34509step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34509step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34510 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![0, 1, -1], ![1, -2, 1]]
def raw34510Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34510step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw34510step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34510step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34510step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34510step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34510step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34511 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![0, -1, 1]]
def raw34511Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34511step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw34511step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34511step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34511step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34511step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34511step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34512 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw34512Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34512step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw34512step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34512step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34512step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34512step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34512step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34513 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw34513Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34513step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw34513step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34513step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34513step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34513step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34513step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34514 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1], ![1, -2, 1]]
def raw34514Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34514step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw34514step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34514step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34514step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34514step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34514step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34515 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![0, -1, 1]]
def raw34515Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34515step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw34515step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34515step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34515step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34515step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34515step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34516 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw34516Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34516step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw34516step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34516step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw34516step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34517 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw34517Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34517step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw34517step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34517step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw34517step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34518 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34518Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34518step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34518step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34518step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34518step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34519 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34519Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34519step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34519step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34519step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34519step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34520 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34520Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34520step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34520step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34520step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34520step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34520step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34520step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34521 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw34521Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34521step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34521step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34521step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34521step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34521step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34521step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34522 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw34522Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34522step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34522step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34522step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34522step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34523 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34523Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34523step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34523step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34523step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34523step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34524 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34524Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34524step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34524step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34524step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34524step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0], ![1, 1, -2]]
def raw34525Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34525step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw34525step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34525step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34525step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34525step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34525step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![0, 2, -2]]
def raw34526Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34526step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34526step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34526step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34526step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34527 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw34527Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34527step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34527step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34527step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34527step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34528 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw34528Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34528step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34528step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34528step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34528step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34529 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw34529Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34529step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw34529step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34529step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34529step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34529step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34529step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![0, 2, -2]]
def raw34530Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34530step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34530step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34530step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34530step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34536 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw34536Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34536step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34536step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34536step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34536step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34536step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34536step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34539 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34539Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34539step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34539step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34539step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34539step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34556 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw34556Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34556step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34556step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34556step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34556step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw3471 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw3471Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3471step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw3471step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3471step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw3471step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3471step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 2, -3], ![3, -3, 0]]
def raw3471step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3472 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw3472Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3472step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw3472step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3472step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw3472step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3475 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw3475Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3475step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw3475step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3475step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw3475step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3475step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![2, -2, 0]]
def raw3475step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3475step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-3, 2, 1]]
def raw3475step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw3475step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw3475step4Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw3475step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw3475step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical270
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw34560 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34560Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34560step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34560step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34560step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34560step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34604 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34604Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34604step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1]]
def raw34604step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34604step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw34604step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34604step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw34604step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34605 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34605Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34605step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw34605step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34605step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw34605step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34605step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw34605step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34606 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw34606Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34606step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw34606step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34606step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34606step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34606step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34606step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34606step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34606step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34607 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw34607Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34607step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw34607step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34607step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34607step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34607step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34607step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34607step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34607step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34608 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34608Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34608step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34608step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34609 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34609Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34609step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw34609step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34610 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw34610Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34610step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw34610step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34610step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34610step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34611 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw34611Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34611step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw34611step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34611step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34611step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34612 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34612Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34612step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34612step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34613 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0]]
def raw34613Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34613step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw34613step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34613step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34613step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34614 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0]]
def raw34614Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34614step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw34614step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34614step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34614step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34615 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0]]
def raw34615Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34615step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34615step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34616 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw34616Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34616step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw34616step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34617 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0], ![0, 0, 0]]
def raw34617Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34617step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34617step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34618 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw34618Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34618step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34618step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34619 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0]]
def raw34619Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34619step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34619step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34620 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34620Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34620step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1]]
def raw34620step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34620step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw34620step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34620step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw34620step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34621 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34621Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34621step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw34621step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34621step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw34621step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34621step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw34621step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34622 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw34622Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34622step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw34622step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34622step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34622step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34622step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34622step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34622step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34622step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34623 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw34623Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34623step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw34623step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34623step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34623step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34623step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34623step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34623step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34623step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34624 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34624Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34624step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2]]
def raw34624step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34624step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw34624step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34624step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw34624step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34625 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34625Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34625step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw34625step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34625step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw34625step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34625step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw34625step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34626 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw34626Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34626step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw34626step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34626step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw34626step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34626step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw34626step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34626step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw34626step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34627 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw34627Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34627step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw34627step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34627step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw34627step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34627step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw34627step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34627step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw34627step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34628 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34628Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34628step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2]]
def raw34628step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34628step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw34628step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34628step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw34628step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34629 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0]]
def raw34629Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34629step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw34629step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34629step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw34629step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34629step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw34629step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34629step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw34629step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34630 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0]]
def raw34630Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34630step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw34630step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34630step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw34630step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34630step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw34630step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34630step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw34630step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34631 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0]]
def raw34631Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34631step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1]]
def raw34631step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34631step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw34631step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34631step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw34631step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34632 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw34632Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34632step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw34632step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34632step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw34632step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34632step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw34632step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34633 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0], ![0, 0, 0]]
def raw34633Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34633step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34633step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34633step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34633step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34633step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34633step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34633step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34633step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34634 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw34634Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34634step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1]]
def raw34634step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34634step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw34634step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34634step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw34634step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34635 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0]]
def raw34635Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34635step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34635step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34635step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34635step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34635step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34635step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34635step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34635step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34636 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34636Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34636step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34636step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34637 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw34637Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34637step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34637step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34637step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34637step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34637step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34637step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34638 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw34638Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34638step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34638step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34638step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34638step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34638step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34638step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34639 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34639Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34639step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw34639step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34639step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34639step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34639step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34639step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34640 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw34640Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34640step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw34640step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34640step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34640step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34640step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34640step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34641 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw34641Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34641step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw34641step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34641step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34641step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34641step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34641step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34642 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34642Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34642step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34642step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34642step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34642step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34643 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34643Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34643step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34643step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34643step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34643step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34644 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -2, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34644Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34644step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34644step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34644step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34644step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34644step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34644step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34645 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -2, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw34645Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34645step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34645step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34645step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34645step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34645step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34645step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34646 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw34646Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34646step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34646step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34646step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34646step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34646step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34646step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34647 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34647Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34647step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34647step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34647step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34647step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34648 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34648Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34648step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34648step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34648step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34648step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34649 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![2, -2, 0], ![0, 1, -1], ![1, 0, -1]]
def raw34649Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34649step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34649step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34649step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34649step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34649step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34649step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34650 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1], ![0, 1, -1]]
def raw34650Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34650step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34650step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34650step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34650step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34650step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34650step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34651 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw34651Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34651step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34651step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34651step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34651step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34652 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw34652Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34652step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34652step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34652step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34652step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34653 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1], ![0, 1, -1]]
def raw34653Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34653step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw34653step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34653step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34653step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34653step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34653step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34654 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34654Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34654step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw34654step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34654step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw34654step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34655 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34655Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34655step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw34655step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34655step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw34655step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34656 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw34656Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34656step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34656step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34656step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34656step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34657 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![3, -2, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34657Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34657step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 3, -1]]
def raw34657step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34657step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw34657step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34657step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw34657step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34658 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34658Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34658step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw34658step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34658step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw34658step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34659 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34659Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34659step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw34659step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34659step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw34659step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34660 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw34660Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34660step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 3, -1]]
def raw34660step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34660step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw34660step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34660step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw34660step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34661 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34661Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34661step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 3, -1]]
def raw34661step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34661step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw34661step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34661step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw34661step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34662 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34662Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34662step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34662step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34662step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34662step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34662step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34662step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34663 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34663Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34663step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34663step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34663step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34663step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34664 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34664Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34664step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34664step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34664step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34664step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34665 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw34665Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34665step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34665step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34665step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34665step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34665step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34665step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34666 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34666Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34666step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34666step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34666step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34666step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34666step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34666step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34667 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![0, -1, 1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34667Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34667step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34667step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34667step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34667step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34667step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34667step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34668 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, -1, 1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34668Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34668step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34668step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34668step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34668step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34669 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 0, 1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34669Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34669step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34669step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34669step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34669step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34670 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, -1, 1], ![1, -2, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw34670Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34670step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34670step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34670step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34670step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34670step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34670step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34671 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, -1, 1], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34671Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34671step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34671step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34671step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34671step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34671step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34671step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34672 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw34672Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34672step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34672step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34672step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34672step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34672step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34672step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34673 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw34673Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34673step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34673step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34673step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34673step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34674 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw34674Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34674step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34674step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34674step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34674step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34675 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw34675Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34675step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34675step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34675step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34675step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34675step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34675step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34676 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw34676Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34676step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34676step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34676step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34676step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34677 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw34677Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34677step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34677step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34677step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34677step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34678 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw34678Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34678step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34678step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34678step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34678step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34679 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw34679Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34679step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34679step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34679step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34679step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34679step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34679step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34680 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34680Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34680step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34680step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34680step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34680step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34680step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34680step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34681 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34681Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34681step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw34681step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34681step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34681step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34681step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34681step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34682 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34682Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34682step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw34682step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34682step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw34682step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34682step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw34682step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34683 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw34683Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34683step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw34683step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34683step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34683step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34683step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34683step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34683step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34683step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34684 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw34684Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34684step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw34684step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34684step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34684step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34684step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34684step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34684step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34684step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34685 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34685Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34685step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34685step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34685step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34685step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34686 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34686Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34686step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34686step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34687 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34687Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34687step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34687step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical271
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw34688 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw34688Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34688step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw34688step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34688step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34688step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34689 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw34689Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34689step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw34689step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34689step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34689step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34690 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34690Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34690step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34690step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34691 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34691Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34691step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw34691step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34692 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0]]
def raw34692Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34692step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw34692step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34692step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34692step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34693 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0]]
def raw34693Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34693step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw34693step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34693step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34693step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34694 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0]]
def raw34694Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34694step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34694step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34695 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0]]
def raw34695Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34695step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw34695step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34696 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw34696Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34696step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw34696step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34697 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0], ![0, 0, 0]]
def raw34697Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34697step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34697step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34697step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34698 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw34698Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34698step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34698step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34699 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw34699Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34699step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw34699step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34700 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw34700Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34700step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw34700step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34701 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0]]
def raw34701Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34701step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34701step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34701step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34701step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34702 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34702Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34702step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34702step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34702step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34702step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34702step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34702step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34703 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34703Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34703step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw34703step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34703step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34703step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34703step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34703step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34704 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34704Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34704step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw34704step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34704step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw34704step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34704step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw34704step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34705 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw34705Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34705step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw34705step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34705step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34705step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34705step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34705step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34705step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34705step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34706 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw34706Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34706step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw34706step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34706step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34706step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34706step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34706step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34706step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34706step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34707 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34707Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34707step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34707step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34707step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34707step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34707step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34707step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34707step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34707step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34708 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34708Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34708step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34708step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34708step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34708step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34708step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34708step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34709 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34709Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34709step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw34709step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34709step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34709step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34709step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34709step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34710 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw34710Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34710step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw34710step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34710step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34710step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34710step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34710step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34710step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34710step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34711 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw34711Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34711step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw34711step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34711step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34711step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34711step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34711step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34711step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34711step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34712 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34712Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34712step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw34712step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34712step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34712step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34712step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34712step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34713 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34713Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34713step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw34713step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34713step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34713step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34713step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34713step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34714 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0]]
def raw34714Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34714step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw34714step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34714step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw34714step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34714step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34714step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34714step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34714step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34715 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0]]
def raw34715Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34715step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw34715step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34715step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw34715step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34715step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34715step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34715step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34715step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34716 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0]]
def raw34716Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34716step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw34716step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34716step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw34716step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34716step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw34716step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34717 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0]]
def raw34717Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34717step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw34717step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34717step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34717step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34717step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34717step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34718 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw34718Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34718step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw34718step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34718step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34718step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34718step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34718step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34719 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0], ![0, 0, 0]]
def raw34719Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34719step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34719step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34719step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw34719step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34719step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw34719step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34719step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw34719step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34720 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw34720Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34720step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw34720step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34720step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw34720step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34720step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw34720step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34721 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw34721Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34721step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw34721step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34721step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34721step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34721step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34721step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34722 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw34722Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34722step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw34722step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34722step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34722step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34722step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34722step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0]]
def raw34723Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34723step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34723step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34723step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw34723step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34723step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw34723step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34723step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw34723step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34724 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw34724Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34724step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![2, -2], ![1, -1], ![1, -1], ![1, -1]]
def raw34724step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34724step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]
def raw34724step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34725 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw34725Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34725step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw34725step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34725step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![1, -1], ![1, -1]]
def raw34725step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34725step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw34725step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34726 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw34726Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34726step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw34726step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34726step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![1, -1], ![1, -1]]
def raw34726step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34726step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw34726step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34727 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0]]
def raw34727Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34727step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw34727step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34727step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![1, -1], ![1, -1]]
def raw34727step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34727step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw34727step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34728 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw34728Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34728step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![2, -2], ![1, -1], ![1, -1]]
def raw34728step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34728step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]
def raw34728step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34729 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0]]
def raw34729Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw34729step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34729step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![2, -2], ![1, -1]]
def raw34729step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34729step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw34729step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34730 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0]]
def raw34730Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34730step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw34730step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34730step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![2, -2], ![1, -1]]
def raw34730step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34730step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw34730step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34731 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw34731Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34731step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![2, -2], ![1, -1]]
def raw34731step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34731step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]
def raw34731step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34732 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0]]
def raw34732Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34732step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw34732step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34732step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw34732step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34733 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34733Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34733step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34733step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34734 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-3, 3, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34734Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34734step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-3, 3, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34734step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34734step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34734step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34735 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34735Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34736Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34736step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34736step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34737 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34737Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34737step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34737step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34737step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34737step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34738 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw34738Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34738step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw34738step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34738step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34738step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34739 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![1, -1], ![0, 0], ![2, -2]]
def raw34739Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34739step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![1, -1], ![2, -2]]
def raw34739step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34739step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![2, -2]]
def raw34739step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34739step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw34739step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34740 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -2, 0]]
def raw34740Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34740step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-2, 0, 2], ![-1, 0, 1], ![2, 0, -2], ![2, -2, 0]]
def raw34740step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34740step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34740step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34740step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34740step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -2, 0]]
def raw34741Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34741step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![-1, 0, 1], ![2, 0, -2], ![2, -2, 0]]
def raw34741step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34741step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw34741step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34741step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34741step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34742 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-2, 0, 2], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -2, 0]]
def raw34742Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34742step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw34742step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34742step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw34742step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -2, 0]]
def raw34743Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34743step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-2, 0, 2], ![0, -1, 1], ![2, 0, -2], ![2, -2, 0]]
def raw34743step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34743step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw34743step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34743step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34743step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34744 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2], ![2, -2, 0]]
def raw34744Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34744step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-2, 0, 2], ![-1, 0, 1], ![3, -1, -2], ![2, -2, 0]]
def raw34744step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34744step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 0, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw34744step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34744step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw34744step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -3, 0]]
def raw34745Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34745step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-2, 0, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -3, 0]]
def raw34745step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34745step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-3, 3, 0]]
def raw34745step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34745step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw34745step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34746 : Matrix (Fin 6) (Fin 2) ℤ := ![![1, -1], ![-2, 2], ![0, 0], ![-1, 1], ![2, -2], ![0, 0]]
def raw34746Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34746step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![1, -1], ![-2, 2], ![0, 0], ![-1, 1], ![2, -2]]
def raw34746step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34746step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![1, -1], ![-2, 2], ![-1, 1], ![2, -2]]
def raw34746step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34746step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw34746step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 2, 1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34760Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34760step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 2, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34760step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34760step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34760step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34761Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34762Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34762step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34763Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34763step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34763step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34763step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34763step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34764 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![1, 0, -1]]
def raw34764Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34764step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 1, -2], ![2, -2, 0], ![1, 0, -1]]
def raw34764step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34764step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34764step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 2, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw34765Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34765step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw34765step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34766 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw34766Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34767 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw34767Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34767step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw34767step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34768 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw34768Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34768step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34768step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34769 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw34769Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34769step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34769step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34770 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34770Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34770step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw34770step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34770step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34770step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34771 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34771Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34772 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34772Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34773 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![3, -3, 0], ![2, 0, -2]]
def raw34773Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34773step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![2, 0, -2], ![0, 1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34773step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34773step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34773step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34774 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw34774Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34774step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34774step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34774step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34774step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34775 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34775Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34775step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw34775step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34775step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34775step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34776 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34776Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34777 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34777Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![3, -2, -1], ![2, -1, -1]]
def raw34778Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34778step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34778step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34778step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34778step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34779 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw34779Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34779step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34779step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34779step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34779step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34780 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34780Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34780step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34780step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34781 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw34781Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34781step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34781step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34782 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34782Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34782step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 3, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34782step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34782step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 3, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34782step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34782step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34782step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34782step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34782step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34783 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34783Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34783step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34783step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34783step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34783step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34783step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34783step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34783step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34783step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34784Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34784step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34784step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34784step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34784step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34784step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34784step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34784step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34784step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34785 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw34785Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34785step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw34785step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34785step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![2, -2, 0], ![1, 1, -2]]
def raw34785step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34785step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw34785step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34785step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw34785step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34786Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34786step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34786step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34786step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34786step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34786step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34786step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34787Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34787step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34787step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34787step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34787step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34788 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw34788Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34788step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw34788step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34788step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34788step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34788step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34788step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34789 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34789Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34789step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34789step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34789step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34789step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34789step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34789step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34790 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34790Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34790step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34790step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34790step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34790step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw34791Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34791step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw34791step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34791step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![3, -3, 0], ![2, 0, -2]]
def raw34791step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34791step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -2, 0], ![3, 0, -3]]
def raw34791step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34791step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -2, 0], ![3, 0, -3]]
def raw34791step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw34792Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34792step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw34792step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34792step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34792step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34792step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34792step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34792step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34792step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw34793Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34793step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw34793step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34793step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34793step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34793step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34793step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34793step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34793step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34794 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![1, 1, -2]]
def raw34794Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34794step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![3, -3, 0], ![1, 1, -2]]
def raw34794step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34794step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![3, -3, 0], ![1, 1, -2]]
def raw34794step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34794step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34794step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34794step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34794step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34794step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34794step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34795 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw34795Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34795step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw34795step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34795step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![2, -2, 0], ![3, -1, -2]]
def raw34795step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34795step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![3, -2, -1]]
def raw34795step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34795step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![3, -2, -1]]
def raw34795step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34796 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw34796Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34796step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw34796step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34796step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw34796step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34796step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34796step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34797 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw34797Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34797step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw34797step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34797step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw34797step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34797step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34797step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34798 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34798Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34798step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 3, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34798step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34798step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 3, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34798step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34798step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34798step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34799 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34799Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34799step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34799step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34799step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34799step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34799step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34799step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34800 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34800Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34800step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34800step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34800step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34800step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34800step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34800step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34801 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34801Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34801step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34801step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34801step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34801step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34801step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34801step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34802 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw34802Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34802step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw34802step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34802step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![2, -2, 0], ![1, 1, -2]]
def raw34802step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34802step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw34802step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34803Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34803step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34803step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34803step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34803step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34804 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34804Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34804step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34804step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34805 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34805Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34805step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34805step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34805step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34805step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34806 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw34806Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34806step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw34806step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34806step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34806step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34807 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34807Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34807step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34807step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34807step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34807step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34808 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34808Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34808step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34808step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34809 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw34809Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34809step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw34809step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34809step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34809step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34810 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw34810Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34810step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw34810step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34810step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![3, -3, 0], ![2, 0, -2]]
def raw34810step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34810step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -2, 0], ![3, 0, -3]]
def raw34810step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw34811Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34811step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw34811step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34811step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34811step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34811step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34811step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34812 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw34812Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34812step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw34812step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34812step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34812step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34812step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34812step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34813 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![1, 1, -2]]
def raw34813Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34813step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![3, -3, 0], ![1, 1, -2]]
def raw34813step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34813step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![3, -3, 0], ![1, 1, -2]]
def raw34813step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34813step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34813step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34813step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34813step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34814 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw34814Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34814step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw34814step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34814step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![2, -2, 0], ![3, -1, -2]]
def raw34814step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34814step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![3, -2, -1]]
def raw34814step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34815 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw34815Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34815step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw34815step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34815step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![2, 0, -2], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34815step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34815step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34815step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical272
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw34816 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw34816Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34816step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw34816step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34816step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![2, 0, -2], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34816step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34816step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34816step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34817 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw34817Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34817step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw34817step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34817step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-2, 0, 2], ![0, -2, 2]]
def raw34817step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34817step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw34817step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34817step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34817step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34817step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34817step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34818 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw34818Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34818step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw34818step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34818step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34818step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34818step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34818step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34819 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw34819Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34819step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw34819step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34819step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34819step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34819step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34819step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34820 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![0, 0, 0], ![0, 0, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw34820Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34820step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![0, 0, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw34820step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34820step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![-3, 1, 2], ![0, -2, 2]]
def raw34820step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34820step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw34820step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34821 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw34821Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34821step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw34821step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34821step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![-2, 0, 2], ![-1, -1, 2]]
def raw34821step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34821step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw34821step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34821step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw34821step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34822 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -1, -2], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw34822Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34822step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -1, -2], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw34822step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34822step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -1, -2], ![-2, 0, 2], ![0, -2, 2]]
def raw34822step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34822step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 3, -2], ![-2, 0, 2]]
def raw34822step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34822step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw34822step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34823 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw34823Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34823step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw34823step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34823step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw34823step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34823step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34823step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34824 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw34824Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34824step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw34824step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34824step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw34824step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34824step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34824step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34825 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![0, 0, 0], ![0, 0, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw34825Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34825step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![0, 0, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw34825step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34825step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![-3, 1, 2], ![0, -2, 2]]
def raw34825step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34825step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]
def raw34825step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34826 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw34826Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34826step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw34826step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34826step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![-2, 0, 2], ![-1, -1, 2]]
def raw34826step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34826step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, -1, 2], ![-2, 0, 2]]
def raw34826step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34826step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw34826step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34827 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw34827Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34827step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw34827step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34827step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw34827step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34827step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34827step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34827step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34827step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34828 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw34828Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34828step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw34828step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34828step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34828step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34828step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34828step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34829 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw34829Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34829step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34829step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34829step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34829step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34830 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![1, -1, 0], ![0, 0, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw34830Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34830step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw34830step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34830step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34830step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34831 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw34831Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34831step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw34831step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34831step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34831step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34831step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34831step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34831step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34831step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34832 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw34832Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34832step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw34832step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34832step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw34832step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34832step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34832step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34832step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34832step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34833 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw34833Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34833step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw34833step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34833step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34833step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34833step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34833step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34834 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-1, 1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw34834Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34834step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34834step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34834step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34834step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34835 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw34835Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34835step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw34835step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34835step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34835step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34836 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw34836Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34836step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw34836step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34836step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34836step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34836step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34836step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34836step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34836step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34837 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw34837Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34837step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw34837step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34837step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![-1, -1, 2], ![0, -2, 2]]
def raw34837step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34837step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, -1, 2], ![-2, 0, 2]]
def raw34837step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34837step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw34837step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34837step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw34837step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34838 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw34838Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34838step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw34838step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34838step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![-1, -1, 2], ![0, -2, 2]]
def raw34838step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34838step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw34838step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34838step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw34838step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34839 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw34839Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34839step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw34839step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34839step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34839step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34839step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34839step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34839step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34839step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34840 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw34840Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34840step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw34840step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34840step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34840step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34840step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34840step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34840step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34840step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34841 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34841Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34841step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34841step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34841step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-1, -1, 2], ![-1, -1, 2]]
def raw34841step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34841step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34841step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34841step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34841step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34842 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw34842Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34842step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw34842step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34842step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![-2, 0, 2], ![1, -3, 2]]
def raw34842step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34842step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]
def raw34842step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34842step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]
def raw34842step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34843 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw34843Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34843step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw34843step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34843step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![-2, 0, 2], ![1, -3, 2]]
def raw34843step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34843step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw34843step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34843step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw34843step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34844 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw34844Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34844step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw34844step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34844step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34844step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34844step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34844step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34845 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw34845Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34845step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw34845step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34845step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34845step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34845step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34845step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34846 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![0, 0, 0], ![-3, 1, 2], ![1, -3, 2]]
def raw34846Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34846step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![-3, 1, 2], ![1, -3, 2]]
def raw34846step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34846step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-3, 1, 2], ![1, -3, 2]]
def raw34846step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34846step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw34846step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34847Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34847step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 3, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34847step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34847step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 3, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34847step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34847step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34847step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34847step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34847step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34848Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34848step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34848step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34848step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34848step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34848step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34848step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34849Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34849step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34849step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34849step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34849step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34849step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34849step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34850Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34850step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34850step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34850step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34850step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34850step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw34850step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34850step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw34850step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw34851Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34851step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw34851step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34851step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![2, -1, -1], ![1, 0, -1]]
def raw34851step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34851step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw34851step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34851step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw34851step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34852Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34852step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34852step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34852step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34852step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34852step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34852step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34853Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34853step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34853step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34853step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34853step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34854Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34854step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34854step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw34855Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34855step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw34855step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34855step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34855step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34856Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34856step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34856step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34856step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34856step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34856step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34856step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34857Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34857step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34857step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34857step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34857step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34858 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw34858Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34858step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw34858step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34858step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34858step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw34859Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34859step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw34859step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34859step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![3, -2, -1], ![2, -1, -1]]
def raw34859step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34859step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def raw34859step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34859step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def raw34859step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw34860Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34860step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw34860step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34860step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34860step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34860step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34860step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34860step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34860step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw34861Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34861step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw34861step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34861step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34861step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34861step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34861step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34861step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34861step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw34862Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34862step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw34862step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34862step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![3, -2, -1], ![1, 0, -1]]
def raw34862step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34862step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw34862step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34862step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34862step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34862step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34862step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw34863Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34863step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw34863step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34863step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![2, -1, -1], ![3, -2, -1]]
def raw34863step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34863step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def raw34863step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34863step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def raw34863step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw34864Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34864step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw34864step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34864step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34864step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34864step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34864step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34864step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34864step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw34865Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34865step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw34865step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34865step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34865step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34865step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34865step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34865step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34865step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34866Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34866step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 3, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34866step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34866step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 3, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34866step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34866step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34866step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34867Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34867step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34867step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34867step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34867step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34868Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34868step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34868step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34868step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34868step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34869Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34869step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34869step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34869step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34869step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34869step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw34869step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw34870Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34870step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw34870step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34870step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![2, -1, -1], ![1, 0, -1]]
def raw34870step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34870step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw34870step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34871Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34871step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34871step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34871step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34871step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34872Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34872step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34872step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34873Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34873step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34873step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34873step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34873step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw34874Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34874step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw34874step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34874step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34874step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34875Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34875step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34875step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34875step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34875step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34876Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34876step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34876step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw34877Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34877step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw34877step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34877step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34877step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw34878Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34878step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw34878step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34878step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![3, -2, -1], ![2, -1, -1]]
def raw34878step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34878step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def raw34878step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw34879Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34879step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw34879step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34879step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34879step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34879step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34879step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw34880Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34880step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw34880step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34880step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34880step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34880step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34880step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34881 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw34881Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34881step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw34881step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34881step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![3, -2, -1], ![1, 0, -1]]
def raw34881step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34881step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw34881step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34881step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34881step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw34882Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34882step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw34882step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34882step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![2, -1, -1], ![3, -2, -1]]
def raw34882step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34882step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def raw34882step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw34883Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34883step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw34883step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34883step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34883step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34883step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34883step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw34884Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34884step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw34884step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34884step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34884step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34884step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34884step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34885 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34885Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34885step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34885step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34885step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-1, -1, 2], ![-1, -1, 2]]
def raw34885step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34885step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw34885step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34885step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw34885step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34886 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34886Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34886step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34886step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34886step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34886step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34886step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34886step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34887 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34887Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34887step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34887step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34887step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34887step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34887step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34887step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34888 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw34888Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34888step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw34888step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34888step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![-1, -1, 2], ![-2, 0, 2]]
def raw34888step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34888step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw34888step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34888step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw34888step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -1, -2], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34889Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34889step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -1, -2], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34889step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34889step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -1, -2], ![-1, -1, 2], ![-1, -1, 2]]
def raw34889step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34889step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 3, -2], ![-1, -1, 2], ![-1, -1, 2]]
def raw34889step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34889step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![1, 1, -2], ![1, 1, -2]]
def raw34889step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34890 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34890Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34890step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34890step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34890step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34890step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34890step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw34890step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34891 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34891Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34891step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34891step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34891step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34891step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34891step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw34891step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34892 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw34892Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34892step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw34892step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34892step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![-1, -1, 2], ![-2, 0, 2]]
def raw34892step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34892step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, -1, 2], ![-2, 0, 2]]
def raw34892step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34892step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw34892step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34893 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34893Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34893step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34893step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34893step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34893step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34893step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw34893step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34893step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw34893step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34894 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34894Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34894step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34894step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34894step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34894step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34894step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34894step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34895 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34895Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34895step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34895step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34895step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34895step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34896 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw34896Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34896step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw34896step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34896step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34896step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34896step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34896step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34896step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34896step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34897 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34897Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34897step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34897step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34897step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34897step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34897step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw34897step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34897step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw34897step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34898 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34898Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34898step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34898step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34898step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34898step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34898step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34898step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34899 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34899Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34899step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34899step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34899step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34899step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34900 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw34900Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34900step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw34900step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34900step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34900step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34900step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34900step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34900step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34900step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34901 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw34901Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34901step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw34901step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34901step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![0, -2, 2], ![-1, -1, 2]]
def raw34901step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34901step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, -1, 2], ![-2, 0, 2]]
def raw34901step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34901step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw34901step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34901step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw34901step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34902 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw34902Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34902step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw34902step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34902step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![0, -2, 2], ![-1, -1, 2]]
def raw34902step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34902step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw34902step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34902step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw34902step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34903 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw34903Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34903step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw34903step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34903step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34903step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34903step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34903step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34903step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34903step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34904 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw34904Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34904step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw34904step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34904step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34904step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34904step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34904step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34904step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34904step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34905 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw34905Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34905step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw34905step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34905step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, -2, 2], ![-2, 0, 2]]
def raw34905step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34905step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34905step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34905step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34905step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34906 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw34906Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34906step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw34906step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34906step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-2, 0, 2], ![0, -2, 2]]
def raw34906step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34906step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34906step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34906step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34906step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34941Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34941step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 1, 2], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34941step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34941step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw34941step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34942Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34942step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw34942step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34942step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34942step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34943Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34943step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34943step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34943step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw34943step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34943step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34943step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical273
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw34944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw34944Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34944step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw34944step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34944step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw34944step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34944step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34944step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw34945Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34945step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw34945step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34945step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw34945step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34945step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw34945step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34946Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34946step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw34946step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34946step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw34946step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34947Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34947step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw34947step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34948Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34948step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34948step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34948step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34948step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw34949Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34949step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34949step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34950Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34950step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34950step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34950step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34950step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34950step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34950step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34951 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34951Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34951step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34951step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34951step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw34951step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34952Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34952step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, -2, 1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw34952step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34952step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34952step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw34953Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34953step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw34953step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34953step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34953step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw34954Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34954step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw34954step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34954step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw34954step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34954step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw34954step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw34955Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34955step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw34955step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34955step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw34955step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34955step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw34955step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw34956Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34956step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw34956step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34956step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34956step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw34957Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34957step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw34957step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34957step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34957step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34957step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34957step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw34958Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34958step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw34958step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34958step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34958step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34958step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34958step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw34959Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34959step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw34959step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34959step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw34959step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34959step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw34959step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw34960Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34960step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw34960step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34960step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw34960step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw34961Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34961step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34961step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34961step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34961step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34961step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34961step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw34962Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34962step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw34962step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34962step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw34962step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34962step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34962step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34962step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34962step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34963Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34963step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 1, 2], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34963step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34963step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw34963step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34964Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34964step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw34964step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34964step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34964step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34965Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34965step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34965step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34965step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw34965step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34965step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw34965step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw34966Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34966step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw34966step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34966step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw34966step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw34967Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34967step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw34967step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34967step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw34967step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34968Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34968step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw34968step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34969 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34969Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34969step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw34969step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34970Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34970step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw34970step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw34971Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34971step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw34971step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34972Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34972step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34972step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34972step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34972step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34973Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34973step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34973step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34973step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34973step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34974Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34974step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34974step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw34975Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34975step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw34975step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34975step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw34975step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw34976Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34976step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw34976step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34976step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw34976step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw34977Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34977step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw34977step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34977step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw34977step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw34978Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34978step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34978step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34978step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34978step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw34979Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34979step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw34979step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34979step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![2, -1, -1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw34979step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34979step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34979step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw34980Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34980step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw34980step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34980step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, -1, 0], ![0, 1, -1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34980step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34980step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw34980step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw34981Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34981step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw34981step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34981step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw34981step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw34982Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34982step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw34982step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34982step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![0, 1, -1], ![-2, 0, 2], ![-3, 2, 1]]
def raw34982step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34982step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw34982step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw34983Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34983step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34983step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34983step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34983step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw34984Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34984step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw34984step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34984step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw34984step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34984step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34984step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34985Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34985step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 1, 2], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34985step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34985step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw34985step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34985step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw34985step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34985step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw34985step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34986Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34986step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34986step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34986step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34986step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34987Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34987step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34987step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34987step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34987step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34987step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34987step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw34988Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34988step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw34988step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34988step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34988step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34988step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34988step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw34989Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34989step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw34989step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34989step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw34989step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34989step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw34989step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34989step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw34989step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34990Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34990step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw34990step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34990step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34990step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34990step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34990step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34991Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34991step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw34991step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34991step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw34991step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34991step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw34991step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34992Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34992step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw34992step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34992step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw34992step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw34993Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34993step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34993step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34993step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34993step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34994Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34994step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34994step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34994step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw34994step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34994step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw34994step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34994step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw34994step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34995Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34995step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34995step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34995step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 2, -2], ![-1, -1, 2], ![-2, 0, 2]]
def raw34995step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34995step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw34995step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34995step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw34995step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34996Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34996step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw34996step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34996step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw34996step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw34997Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34997step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw34997step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34997step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw34997step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34997step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw34997step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw34998Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34998step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw34998step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34998step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw34998step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34998step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw34998step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34998step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw34998step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw34999Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34999step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw34999step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34999step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw34999step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34999step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]

end MUB6.Certificate.MixedSemantics

end OAI
end


