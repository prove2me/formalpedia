-- Prove2me | Definitions.Def_OAIQ106D059
-- name    : OAIQ106D059
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T12:27:33.862295+00:00
-- url     : https://prove2.me/theorems/482eeb0e-4d9b-451c-a4bb-bd4c3a50ba48
-- title:
--   Definitions bundle OAIQ106D059 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1907 declarations of OpenAI's Lean: 1907 definitions. The definitions and types are `OAI.MUB6.Certificate.PairSemantics.raw3628step0`, `OAI.MUB6.Certificate.PairSemantics.raw3628step1`, `OAI.MUB6.Certificate.PairSemantics.raw3629`, `OAI.MUB6.Certificate.PairSemantics.raw3629step0`, `OAI.MUB6.Certificate.PairSemantics.raw362step0`, `OAI.MUB6.Certificate.PairSemantics.raw362step1`, `OAI.MUB6.Certificate.PairSemantics.raw362step2`, `OAI.MUB6.Certificate.PairSemantics.raw363`, `OAI.MUB6.Certificate.PairSemantics.raw3630`, `OAI.MUB6.Certificate.PairSemantics.raw3630step0`, `OAI.MUB6.Certificate.PairSemantics.raw3630step1`, `OAI.MUB6.Certificate.PairSemantics.raw3630step2`, `OAI.MUB6.Certificate.PairSemantics.raw3631`, `OAI.MUB6.Certificate.PairSemantics.raw3631step0`, `OAI.MUB6.Certificate.PairSemantics.raw3631step1`, `OAI.MUB6.Certificate.PairSemantics.raw3631step2`, `OAI.MUB6.Certificate.PairSemantics.raw3632`, `OAI.MUB6.Certificate.PairSemantics.raw3632step0`, `OAI.MUB6.Certificate.PairSemantics.raw3632step1`, `OAI.MUB6.Certificate.PairSemantics.raw3633`, `OAI.MUB6.Certificate.PairSemantics.raw3633step0`, `OAI.MUB6.Certificate.PairSemantics.raw3633step1`, `OAI.MUB6.Certificate.PairSemantics.raw3634`, `OAI.MUB6.Certificate.PairSemantics.raw3634step0`, `OAI.MUB6.Certificate.PairSemantics.raw3634step1`, `OAI.MUB6.Certificate.PairSemantics.raw3635`, `OAI.MUB6.Certificate.PairSemantics.raw3635step0`, `OAI.MUB6.Certificate.PairSemantics.raw3636`, `OAI.MUB6.Certificate.PairSemantics.raw3636step0`, `OAI.MUB6.Certificate.PairSemantics.raw3636step1`, `OAI.MUB6.Certificate.PairSemantics.raw3637`, `OAI.MUB6.Certificate.PairSemantics.raw3637step0`, `OAI.MUB6.Certificate.PairSemantics.raw3637step1`, `OAI.MUB6.Certificate.PairSemantics.raw3638`, `OAI.MUB6.Certificate.PairSemantics.raw3638step0`, `OAI.MUB6.Certificate.PairSemantics.raw3639`, `OAI.MUB6.Certificate.PairSemantics.raw3639step0`, `OAI.MUB6.Certificate.PairSemantics.raw3639step1`, `OAI.MUB6.Certificate.PairSemantics.raw363step0`, `OAI.MUB6.Certificate.PairSemantics.raw363step1` and 1867 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_PairSemantics_Canonical0`, `MutuallyUnbiased_PairSemantics_Canonical1`, `MutuallyUnbiased_PairSemantics_Canonical11`, `MutuallyUnbiased_PairSemantics_Canonical113`, `MutuallyUnbiased_PairSemantics_Canonical114`, `MutuallyUnbiased_PairSemantics_Canonical115`, `MutuallyUnbiased_PairSemantics_Canonical116`, `MutuallyUnbiased_PairSemantics_Canonical117`, `MutuallyUnbiased_PairSemantics_Canonical118`, `MutuallyUnbiased_PairSemantics_Canonical119`, `MutuallyUnbiased_PairSemantics_Canonical12`, `MutuallyUnbiased_PairSemantics_Canonical120`, `MutuallyUnbiased_PairSemantics_Canonical121`, `MutuallyUnbiased_PairSemantics_Canonical122`, `MutuallyUnbiased_PairSemantics_Canonical123`, `MutuallyUnbiased_PairSemantics_Canonical124`, `MutuallyUnbiased_PairSemantics_Canonical125`, `MutuallyUnbiased_PairSemantics_Canonical126`, `MutuallyUnbiased_PairSemantics_Canonical127`, `MutuallyUnbiased_PairSemantics_Canonical128`, `MutuallyUnbiased_PairSemantics_Canonical129`, `MutuallyUnbiased_PairSemantics_Canonical13`, `MutuallyUnbiased_PairSemantics_Canonical130`, `MutuallyUnbiased_PairSemantics_Canonical131`, `MutuallyUnbiased_PairSemantics_Canonical132`, `MutuallyUnbiased_PairSemantics_Canonical133`, `MutuallyUnbiased_PairSemantics_Canonical134`, `MutuallyUnbiased_PairSemantics_Canonical135`, `MutuallyUnbiased_PairSemantics_Canonical136`, `MutuallyUnbiased_Tao_TaoArithmetic`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ106D140`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]

def raw3step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]

def raw4 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw36step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]

def raw37 : Matrix (Fin 5) (Fin 2) ℤ := ![![-5, 5], ![0, 0], ![1, -1], ![1, -1], ![3, -3]]

def raw37step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![1, -1], ![3, -3]]

def raw38 : Matrix (Fin 5) (Fin 2) ℤ := ![![-5, 5], ![0, 0], ![1, -1], ![2, -2], ![2, -2]]

def raw38step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![2, -2], ![2, -2]]

def raw39 : Matrix (Fin 4) (Fin 2) ℤ := ![![-5, 5], ![0, 0], ![1, -1], ![4, -4]]

def raw39step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![4, -4]]

def raw40 : Matrix (Fin 4) (Fin 2) ℤ := ![![-5, 5], ![0, 0], ![2, -2], ![3, -3]]

def raw40step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-5, 5], ![2, -2], ![3, -3]]

def raw41 : Matrix (Fin 3) (Fin 2) ℤ := ![![-5, 5], ![0, 0], ![5, -5]]

def raw42 : Matrix (Fin 6) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]

def raw43 : Matrix (Fin 5) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]

def raw44 : Matrix (Fin 5) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![1, -1], ![2, -2], ![1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw362step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![2, 0, -2], ![1, -2, 1]]

def raw362step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-2, 0, 2], ![-1, 2, -1]]

def raw362step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![2, -1, -1]]

def raw363 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 2, 1], ![0, 3, -1, -2], ![3, -3, -1, 1]]

def raw363step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![2, -1, -1], ![1, -2, 1]]

def raw363step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -2, 1], ![2, -1, -1]]

def raw364 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 2, 1], ![0, 4, -2, -2], ![3, -4, 0, 1]]

def raw364step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 4, -4], ![2, -2, 0], ![1, -2, 1]]

def raw364step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 4, -4], ![1, -2, 1], ![2, -2, 0]]

def raw365 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 2, 1], ![1, -2, 0, 1], ![2, 2, -2, -2]]

def raw365step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![2, 0, -2], ![1, 1, -2]]

def raw365step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -3, 2], ![1, 1, -2]]

def raw366 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 2, 1], ![1, 2, -2, -1], ![2, -2, 0, 0]]

def raw366step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0]]

def raw366step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-2, 2, 0], ![-1, 1, 0]]

def raw366step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

def raw367 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 2, 1], ![1, 2, -1, -2], ![2, -2, -1, 1]]

def raw367step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![2, -1, -1], ![1, -2, 1]]

def raw367step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

def raw368 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]

def raw368step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]

def raw368step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]

def raw369 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]

def raw369step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]

def raw369step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]

def raw370 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]

def raw370step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]

def raw370step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]

def raw371 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]

def raw371step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 3, 0]]

def raw371step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]

def raw372 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]

def raw372step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 1, 1]]

def raw372step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

def raw373 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]

def raw373step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-2, 2, 0], ![-3, 1, 2]]

def raw373step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]

def raw374 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]

def raw374step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-2, 1, 1], ![-3, 2, 1]]

def raw374step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]

def raw375 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]

def raw375step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]

def raw376 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]

def raw376step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]

def raw376step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def raw377 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]

def raw377step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]

def raw377step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]

def raw378 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]

def raw378step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-3, 0, 3]]

def raw378step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

def raw379 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]

def raw379step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]

def raw379step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw380 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]

def raw380step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]

def raw380step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 1, -1], ![1, 0, -1], ![1, 2, -3]]

def raw381 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]

def raw381step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, -1, 2], ![-3, 2, 1]]

def raw381step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]

def raw382 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]

def raw382step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-2, 2, 0], ![-2, -1, 3]]

def raw382step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]

def raw383 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]

def raw383step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]

def raw383step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical113
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3628step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -2, -2, 4], ![-1, 1, 1, -1], ![-1, 1, 1, -1]]

def raw3628step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![1, 1, -1, -1], ![1, 1, -1, -1]]

def raw3629 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -3, 3, -1], ![1, 3, -3, -1]]

def raw3629step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 3, -3], ![2, -1, -1]]

def raw3630 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -2, -1, 2], ![0, 1, 3, -4], ![1, 1, -2, 0]]

def raw3630step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -2, 1, 1], ![0, -1, 3, -2], ![2, 2, -4, 0]]

def raw3630step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 2, -1, -1], ![0, 1, -3, 2], ![-2, -2, 4, 0]]

def raw3630step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 2, -1], ![0, 2, 1, -3], ![2, -1, -1, 0]]

def raw3631 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -2, -1, 2], ![0, 2, -2, 0], ![1, 0, 3, -4]]

def raw3631step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -2, 2, 0], ![0, -1, -2, 3], ![2, 2, 0, -4]]

def raw3631step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 2, -2, 0], ![0, 1, 2, -3], ![-2, -2, 0, 4]]

def raw3631step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -2, 2, 0], ![0, 2, 1, -3], ![2, 0, -1, -1]]

def raw3632 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -2, 0, 1], ![0, 1, -2, 1], ![1, 1, 2, -4]]

def raw3632step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 2, 0, -1], ![0, -1, 2, -1], ![-1, -1, -2, 4]]

def raw3632step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def raw3633 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -2, 1, 0], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw3633step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 2, -1, 0], ![0, -1, -1, 2], ![-1, -1, 2, 0]]

def raw3633step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, -1, -1, 0]]

def raw3634 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -2, 1, 0], ![0, 2, -2, 0], ![1, 0, 1, -2]]

def raw3634step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 2, -1, 0], ![0, -2, 2, 0], ![-1, 0, -1, 2]]

def raw3634step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 2, -1, -1], ![2, 0, -1, -1]]

def raw3635 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -2, 2, -1], ![0, 1, 1, -2], ![1, 1, -3, 1]]

def raw3635step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 1, -3, 1]]

def raw3636 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -2, 2, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def raw3636step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -2, 2, 0], ![0, 2, -1, -1], ![2, -1, -1, 0]]

def raw3636step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw3637 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -2, 2, -1], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw3637step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 2, -2, 1], ![0, -2, 0, 2], ![-1, 0, 2, -1]]

def raw3637step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![2, -1, 0, -1]]

def raw3638 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -2, 2, -1], ![1, 2, -2, -1]]

def raw3638step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]

def raw3639 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, -3, 2], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def raw3639step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 0, 3, -2], ![0, -1, -3, 4], ![-1, 1, 0, 0]]

def raw3639step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 3, -2], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def raw3640 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, -2, 1], ![0, 1, 3, -4], ![1, -1, -1, 1]]

def raw3640step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 0, 2, -1], ![0, -1, -3, 4], ![-1, 1, 1, -1]]

def raw3640step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, -1, 1, -1]]

def raw3641 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, -2, 1], ![0, 2, -1, -1], ![1, -2, 3, -2]]

def raw3641step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 2, -2], ![0, -2, -1, 3], ![2, 1, -1, -2]]

def raw3641step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, 0, -2], ![1, -1, 2, -2], ![1, 0, -2, 1]]

def raw3642 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 1, -3, 1], ![0, 1, 1, -2], ![1, -2, 2, -1]]

def raw3642step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 1, -3, 1]]

def raw3643 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 1, -3, 1], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def raw3643step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, 1, -2], ![0, -3, 3, 0], ![2, 1, -4, 1]]

def raw3643step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, -1, -1, 2], ![0, 3, -3, 0], ![-2, -1, 4, -1]]

def raw3643step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 3, -3], ![0, 2, -1, -1], ![2, -1, -1, 0]]

def raw3644 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-3, 2, 1, 0], ![5, -2, -2, -1]]

def raw3644step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![1, 1, -2], ![1, 0, -1]]

def raw3644step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

def raw3645 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 2, -2, 2], ![4, -2, 1, -3]]

def raw3645step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, -2, 1], ![1, 2, -3]]

def raw3646 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 2, 1, -1], ![4, -2, -2, 0]]

def raw3646step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, 1, -2], ![1, -1, 0]]

def raw3646step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

def raw3647 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 3, -2, 1], ![4, -3, 1, -2]]

def raw3647step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![1, -2, 1], ![1, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical114
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3648 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, -2, 1, 2], ![3, 2, -2, -3]]

def raw3648step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 1, -2], ![1, 2, -3]]

def raw3649 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, -2, 2, 1], ![3, 2, -3, -2]]

def raw3649step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 2, -3], ![1, 1, -2]]

def raw3649step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 1, -2], ![1, 2, -3]]

def raw3650 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, -2, 3, 0], ![3, 2, -4, -1]]

def raw3650step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 3, -4], ![1, 0, -1]]

def raw3650step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 3, -4]]

def raw3651 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -2, 1], ![3, -2, 1, -2]]

def raw3651step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

def raw3652 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, 1, -2], ![3, -2, -2, 1]]

def raw3652step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, 1, -2], ![1, -2, 1]]

def raw3652step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

def raw3653 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 3, -2, 0], ![3, -3, 1, -1]]

def raw3653step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

def raw3654 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 4, -2, -1], ![3, -4, 1, 0]]

def raw3654step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 4, -4], ![1, -2, 1], ![1, -1, 0]]

def raw3655 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -3, 1, 2], ![2, 3, -2, -3]]

def raw3655step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 1, -2], ![1, 2, -3]]

def raw3656 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, -2, 4], ![2, 2, 1, -5]]

def raw3656step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, -2, 1], ![1, 4, -5]]

def raw3657 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, -1, 3], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw3657step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -2, 1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw3658 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, -1, 3], ![1, 1, -1, -1], ![1, 1, 1, -3]]

def raw3658step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 1, 1, -3]]

def raw3659 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 0, 2], ![0, 0, -1, 1], ![1, 1, -1, -1], ![1, 1, 1, -3]]

def raw3659step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 0, -1, 1], ![1, 1, -1, -1], ![1, 1, 1, -3]]

def raw3660 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 0, 2], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw3660step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw3661 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 0, 2], ![1, 1, -2, 0], ![1, 1, 1, -3]]

def raw3661step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![1, 0, -2, 1], ![1, 2, 0, -3]]

def raw3661step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 2, -1, -1], ![-1, 0, 2, -1], ![-1, -2, 0, 3]]

def raw3661step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, 0, -1, -1]]

def raw3662 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw3663 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw3664 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![0, 1, -1, 0], ![1, 1, -1, -1], ![1, 0, 0, -1]]

def raw3664step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw3665 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def raw3665step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw3666 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![0, 1, 0, -1], ![2, 1, -2, -1]]

def raw3666step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![1, 1, 0, -2], ![1, 1, -1, -1]]

def raw3666step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 2, -1, -1], ![-1, -1, 0, 2], ![-1, -1, 1, 1]]

def raw3666step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![1, -1, -1, 1]]

def raw3667 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw3667step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 2, -1, -1], ![0, -2, 2, 0], ![-1, 0, 0, 1], ![-1, 0, 0, 1]]

def raw3667step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 2, -1, -1], ![2, 0, -1, -1]]

def raw3668 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw3668step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw3669 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![0, 2, -1, -1], ![2, 0, -1, -1]]

def raw3669step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![1, 1, -1, -1], ![1, 1, -1, -1]]

def raw3670 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![1, 0, -1, 0], ![1, 2, -1, -2]]

def raw3670step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 0, 2], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def raw3670step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 2, 0, -2], ![-1, -1, 1, 1], ![-1, -1, 0, 2]]

def raw3670step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![1, -1, -1, 1]]

def raw3671 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![1, 0, 0, -1], ![1, 2, -2, -1]]

def raw3671step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 0, 2], ![1, 1, 0, -2], ![1, 1, -1, -1]]

def raw3671step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 2, 0, -2], ![-1, -1, 0, 2], ![-1, -1, 1, 1]]

def raw3671step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![1, -1, -1, 1]]

def raw3672 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![1, 1, -2, 0], ![1, 1, 0, -2]]

def raw3673 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![1, 1, -1, -1], ![1, 1, -1, -1]]

def raw3674 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![2, 2, -2, -2]]

def raw3674step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2]]

def raw3675 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 2, 0], ![2, 2, -3, -1]]

def raw3675step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1]]

def raw3675step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![-1, -2, 3], ![-1, 0, 1]]

def raw3675step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]

def raw3676 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 3, -1], ![2, 2, -4, 0]]

def raw3676step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, 3, -4], ![1, -1, 0]]

def raw3676step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, -1, 0], ![1, 3, -4]]

def raw3677 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -2, 3], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw3678 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -2, 3], ![1, -1, 0, 0], ![1, 2, 1, -4]]

def raw3678step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![1, -2, 0, 1], ![1, 3, 0, -4]]

def raw3678step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def raw3679 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -2, 3], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw3679step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, 2, -3], ![-1, 0, 1, 0], ![-1, -1, -2, 4]]

def raw3679step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, 2, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical115
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3680 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw3680step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, 1, -2], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![-1, -1, -2, 4]]

def raw3680step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw3681 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw3682 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, 1, -2, 1], ![2, 0, 2, -4]]

def raw3682step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 1, 1], ![0, 2, 2, -4], ![1, 0, -2, 1]]

def raw3683 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 2, -3]]

def raw3684 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 2, -4]]

def raw3685 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw3686 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 2, -3]]

def raw3686step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw3687 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![2, 0, 1, -3]]

def raw3687step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def raw3688 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def raw3688step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 0, -1]]

def raw3689 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def raw3689step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, 1, 0, -2]]

def raw3690 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, 2, -2, 0], ![2, -1, 2, -3]]

def raw3690step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![1, -1, -2, 2], ![1, 2, 0, -3]]

def raw3690step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 1, -2, 1], ![-1, 1, 2, -2], ![-1, -2, 0, 3]]

def raw3690step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, 0, -2], ![1, -1, 2, -2], ![1, 0, -2, 1]]

def raw3691 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![1, -1, -1, 1], ![1, 2, 1, -4]]

def raw3691step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, 1, -2], ![-1, 1, 1, -1], ![-1, -2, -1, 4]]

def raw3691step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def raw3692 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![1, -1, 0, 0], ![1, 2, 0, -3]]

def raw3692step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def raw3693 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![1, 0, -2, 1], ![1, 1, 2, -4]]

def raw3693step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, 1, -2], ![-1, 0, 2, -1], ![-1, -1, -2, 4]]

def raw3693step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw3694 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw3694step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, 1, -2], ![-1, 0, 1, 0], ![-1, -1, -1, 3]]

def raw3694step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw3695 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw3695step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 0, 1, -2]]

def raw3696 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def raw3696step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw3697 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![1, 1, -1, -1], ![1, 0, 1, -2]]

def raw3697step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw3698 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, -1, -1, 2], ![1, 1, -1, -1], ![1, 1, 1, -3]]

def raw3698step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, -1, 0, 1], ![1, 1, -1, -1], ![1, 1, 1, -3]]

def raw3699 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw3700 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, 2, 1, -3]]

def raw3700step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, 0, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![0, -2, -1, 3]]

def raw3700step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw3701 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw3701step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, 0, -1], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![-1, -1, -1, 3]]

def raw3701step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw3702 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, 1, -1, -1], ![1, 0, 1, -2]]

def raw3702step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, 0, -1], ![0, 0, 1, -1], ![-1, -1, 1, 1], ![-1, 0, -1, 2]]

def raw3702step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw3703 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 1, -3]]

def raw3704 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw3704step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw3705 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw3705step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, 0, -1], ![0, -1, 1, 0], ![-1, 0, 0, 1], ![-1, 0, 0, 1]]

def raw3705step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def raw3706 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw3706step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw3707 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![1, 0, -2, 1], ![1, 1, 1, -3]]

def raw3707step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, 0, -1], ![-1, 0, 2, -1], ![-1, -1, -1, 3]]

def raw3707step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw3708 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw3708step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, 0, -1], ![-1, 0, 1, 0], ![-1, -1, 0, 2]]

def raw3708step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw3709 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw3709step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, 0, -1], ![-1, 0, 0, 1], ![-1, -1, 1, 1]]

def raw3709step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 1, -1]]

def raw3710 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![1, 1, -2, 0], ![1, 0, 1, -2]]

def raw3710step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, 0, -1], ![-1, -1, 2, 0], ![-1, 0, -1, 2]]

def raw3710step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def raw3711 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw3711step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, -1, 0], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![-1, -1, 0, 2]]

def raw3711step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical116
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3712 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw3712step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, -1, 0], ![0, 0, 1, -1], ![-1, 0, 0, 1], ![-1, -1, 1, 1]]

def raw3712step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def raw3713 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 0, -2]]

def raw3713step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def raw3714 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw3714step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, -1, 0], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, -1, 1, 1]]

def raw3714step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 1, -1, -1]]

def raw3715 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw3715step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, -1, 0], ![0, -1, 1, 0], ![-1, 0, 1, 0], ![-1, 0, 0, 1]]

def raw3715step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw3716 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, -1, 0]]

def raw3716step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, -1, 0], ![0, -1, 1, 0], ![-1, 0, 0, 1], ![-1, 0, 1, 0]]

def raw3716step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw3717 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, -1, -1]]

def raw3717step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw3718 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw3718step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, -1, 0], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, -1, 2, 0]]

def raw3718step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def raw3719 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw3719step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw3720 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw3720step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -2, 0]]

def raw3721 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, -1, 0, 0]]

def raw3721step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -2, 0]]

def raw3722 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 1, 0], ![0, 2, -1, -1], ![2, -1, -1, 0]]

def raw3722step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, -1, 0], ![0, -2, 1, 1], ![-2, 1, 1, 0]]

def raw3722step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw3723 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, -1, -2, 1]]

def raw3723step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, -2, 1], ![0, -2, 1, 1], ![-2, 1, 2, -1]]

def raw3723step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -1, 0, -1]]

def raw3724 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -3, 3], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw3724step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 3, -3], ![-1, 1, 0, 0], ![-1, -1, -2, 4]]

def raw3724step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 3, -3], ![0, 2, -1, -1], ![1, -1, 0, 0]]

def raw3725 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -3, 3], ![1, -1, 1, -1], ![1, 1, 1, -3]]

def raw3725step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 3, -3], ![-1, 1, -1, 1], ![-1, -1, -1, 3]]

def raw3725step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 3, -3], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def raw3726 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def raw3727 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -2, 1, -1]]

def raw3728 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 1, 2, -4]]

def raw3729 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![0, 1, -1, 0], ![2, -1, 2, -3]]

def raw3729step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![1, -2, -1, 2], ![1, 2, 0, -3]]

def raw3729step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def raw3730 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -2, 1, -1]]

def raw3730step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 2, -2], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-2, 2, -1, 1]]

def raw3730step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![2, -1, 0, -1]]

def raw3731 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 1, -1, -1]]

def raw3732 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw3732step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 2, -2], ![0, -1, 0, 1], ![-1, 1, -1, 1], ![-1, 0, 0, 1]]

def raw3732step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def raw3733 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![2, -1, 1, -2]]

def raw3733step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 2, -2], ![0, -1, 0, 1], ![-2, 1, -1, 2]]

def raw3733step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw3734 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![0, 1, 1, -2], ![2, -1, 0, -1]]

def raw3734step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 2, -2], ![0, -1, -1, 2], ![-2, 1, 0, 1]]

def raw3734step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw3735 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![0, 2, -1, -1], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw3735step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 2, -2], ![0, -2, 1, 1], ![-1, 2, -2, 1], ![-1, 0, 0, 1]]

def raw3735step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 2, -1, -1], ![2, -1, -2, 1]]

def raw3736 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![0, 2, -1, -1], ![2, -2, 2, -2]]

def raw3736step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![1, -2, -1, 2], ![1, 2, -1, -2]]

def raw3736step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![2, -1, 1, -2]]

def raw3737 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![2, -2, 1, -1]]

def raw3737step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 2, -2], ![0, -2, 0, 2], ![-2, 2, -1, 1]]

def raw3737step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![2, -1, 0, -1]]

def raw3738 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![1, -2, 0, 1], ![1, 2, 1, -4]]

def raw3738step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 2, -2], ![-1, 2, 0, -1], ![-1, -2, -1, 4]]

def raw3738step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def raw3739 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![1, -2, 2, -1], ![1, 2, -1, -2]]

def raw3739step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 2, -2], ![-1, 2, -2, 1], ![-1, -2, 1, 2]]

def raw3739step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 2, -1, -1], ![2, -1, -2, 1]]

def raw3740 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![1, -1, -1, 1], ![1, 1, 2, -4]]

def raw3740step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 2, -2], ![-1, 1, 1, -1], ![-1, -1, -2, 4]]

def raw3740step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, 1, -1]]

def raw3741 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw3741step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 2, -2], ![-1, 1, 0, 0], ![-1, -1, -1, 3]]

def raw3741step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw3742 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![1, -1, 1, -1], ![1, 1, 0, -2]]

def raw3742step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 2, -2], ![-1, 1, -1, 1], ![-1, -1, 0, 2]]

def raw3742step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def raw3743 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![1, -1, 2, -2], ![1, 1, -1, -1]]

def raw3743step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 2, -2], ![-1, 1, -2, 2], ![-1, -1, 1, 1]]

def raw3743step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 2, -1, -1], ![1, -1, 2, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical117
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3744 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![2, -1, 2, -3]]

def raw3744step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -1, 1, 0], ![-2, 1, -2, 3]]

def raw3744step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -2, 3, -2]]

def raw3745 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, 1, 2, -4]]

def raw3745step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 1, -1], ![-1, -1, -2, 4]]

def raw3745step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 1, -1]]

def raw3746 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw3746step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, -1, -1, 3]]

def raw3746step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw3747 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 1, -2, 1], ![1, -2, 0, 1], ![1, 1, 2, -4]]

def raw3748 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 0, -1, 1], ![2, -1, 2, -3]]

def raw3748step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 1, -1], ![0, -1, 1, 0], ![0, 0, 1, -1], ![-2, 1, -2, 3]]

def raw3748step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -2, 3, -2]]

def raw3749 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -2, 2, -2]]

def raw3749step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw3750 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -2, 1, -1]]

def raw3750step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 1, -1], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-2, 2, -1, 1]]

def raw3750step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def raw3751 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -2, -1, 2], ![1, 1, 2, -4]]

def raw3752 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 1, 1, -3]]

def raw3752step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw3753 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 2, -3]]

def raw3753step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 1, -1], ![0, -1, 1, 0], ![-1, 1, 1, -1], ![-1, 0, -2, 3]]

def raw3753step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 3, -2], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def raw3754 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw3754step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw3755 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw3755step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw3756 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw3756step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw3757 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw3757step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 1, -1], ![0, -1, -1, 2], ![-1, 1, 0, 0], ![-1, 0, 1, 0]]

def raw3757step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw3758 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![1, -1, -2, 2], ![1, 1, 2, -4]]

def raw3758step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 1, -1], ![-1, 1, 2, -2], ![-1, -1, -2, 4]]

def raw3758step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 2, -2]]

def raw3759 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, 1, 1, -3]]

def raw3759step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 1, -1], ![-1, 1, 1, -1], ![-1, -1, -1, 3]]

def raw3759step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 1, -1, -1]]

def raw3760 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw3760step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 1, -1], ![-1, 1, -1, 1], ![-1, -1, 1, 1]]

def raw3760step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -1, 1, -1]]

def raw3761 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 0, 0], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -2, 1, -1]]

def raw3761step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![0, 0, 1, 1, -2], ![1, 0, -2, 0, 1], ![1, 0, 1, -1, -1]]

def raw3761step1 : Matrix (Fin 4) (Fin 5) ℤ := ![![2, 0, 0, 0, -2], ![0, 0, -1, -1, 2], ![-1, 0, 2, 0, -1], ![-1, 0, -1, 1, 1]]

def raw3761step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -1, 2], ![-1, 2, 0, -1], ![-1, -1, 1, 1]]

def raw3761step3 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def raw3762 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 0, 0], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def raw3762step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![1, 0, 1, -2], ![1, 0, -1, 0]]

def raw3762step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0]]

def raw3762step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]

def raw3763 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 1, -1], ![0, 0, 0, 0], ![1, -1, -1, 1], ![1, 1, -1, -1]]

def raw3763step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, -1, 1], ![0, 0, 0, 0], ![-1, 1, 1, -1], ![-1, -1, 1, 1]]

def raw3763step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, -1, 1], ![-1, 1, 1, -1], ![-1, -1, 1, 1]]

def raw3763step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -1, 1, -1]]

def raw3764 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 1, -1], ![0, 0, 0, 0], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw3764step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, -1, 1], ![0, 0, 0, 0], ![-1, 1, 0, 0], ![-1, -1, 2, 0]]

def raw3764step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, -1, 2, 0]]

def raw3764step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw3765 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 1, -1], ![0, 1, -3, 2], ![0, 1, 0, -1], ![2, -2, 1, -1]]

def raw3765step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![2, -2, -1, 1]]

def raw3766 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, -1, 0], ![2, -2, 1, -1]]

def raw3766step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw3767 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -2, 0, 0]]

def raw3767step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, -1, 1], ![0, -1, 2, -1], ![0, -1, 0, 1], ![-2, 2, 0, 0]]

def raw3767step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -1, -1, 0]]

def raw3768 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw3768step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, -1, 1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 0, 1, 0]]

def raw3768step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw3769 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -1, -1, 0]]

def raw3769step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw3770 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, -1, 2], ![1, 1, -1, -1]]

def raw3770step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw3771 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 0, 1], ![1, 1, -2, 0]]

def raw3771step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw3772 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw3772step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw3773 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def raw3773step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw3774 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -2, 0, 1], ![1, 0, -1, 0]]

def raw3774step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, -1, 1], ![0, -2, 1, 1], ![-1, 2, 0, -1], ![-1, 0, 1, 0]]

def raw3774step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -1, -1, 0]]

def raw3775 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, -1, -1, 1]]

def raw3775step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical118
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3776 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -2, -1, 1]]

def raw3776step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![1, 1, -1, -1], ![1, -1, -1, 1]]

def raw3776step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -1, 1, -1]]

def raw3777 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 1, -1], ![1, -1, -3, 3], ![1, 1, 1, -3]]

def raw3777step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, -1, 1], ![-1, 1, 3, -3], ![-1, -1, -1, 3]]

def raw3777step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -1, 3, -3]]

def raw3778 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw3778step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, -1, 2, 0]]

def raw3778step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw3779 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 1, -3, 1]]

def raw3779step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, -1, 1], ![-1, 1, -1, 1], ![-1, -1, 3, -1]]

def raw3779step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 1, -1, -1]]

def raw3780 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 2, -2], ![0, 1, -2, 1], ![2, -1, -1, 0]]

def raw3780step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, -2, 2], ![0, -1, 2, -1], ![-2, 1, 1, 0]]

def raw3780step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw3781 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -1, -2, 1]]

def raw3781step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, -2, 2], ![0, -1, 1, 0], ![-2, 1, 2, -1]]

def raw3781step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw3782 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 2, -2], ![0, 2, -1, -1], ![2, -2, -2, 2]]

def raw3782step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![1, 2, -1, -2], ![1, -2, -1, 2]]

def raw3782step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![2, -1, 1, -2]]

def raw3783 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 2, -2], ![1, -1, -3, 3], ![1, 1, 0, -2]]

def raw3783step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, -2, 2], ![-1, 1, 3, -3], ![-1, -1, 0, 2]]

def raw3783step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 2, -1, -1], ![1, -1, 3, -3]]

def raw3784 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 1, -2, 0]]

def raw3784step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, -2, 2], ![-1, 1, 1, -1], ![-1, -1, 2, 0]]

def raw3784step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def raw3785 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 1, -3, 1]]

def raw3785step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, -2, 2], ![-1, 1, 0, 0], ![-1, -1, 3, -1]]

def raw3785step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw3786 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -3, 2], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw3787 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -3, 2], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def raw3787step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![1, -3, 0, 2], ![1, 2, -1, -2]]

def raw3787step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -1, 2], ![-1, 3, 0, -2], ![-1, -2, 1, 2]]

def raw3787step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 3, -2], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw3788 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -3, 2], ![0, 1, 1, -2], ![2, -2, 1, -1]]

def raw3788step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![1, -3, 1, 1], ![1, 2, -2, -1]]

def raw3788step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 1, -3, 1]]

def raw3789 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -3, 2], ![1, -2, 0, 1], ![1, 1, 2, -4]]

def raw3790 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -3, 2], ![1, -2, 1, 0], ![1, 1, 1, -3]]

def raw3791 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -3, 2], ![1, -2, 2, -1], ![1, 1, 0, -2]]

def raw3792 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -3, 2], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw3792step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 3, -2], ![-1, 1, 0, 0], ![-1, 0, -2, 3]]

def raw3792step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, -1, 0, 0]]

def raw3793 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -3, 2], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def raw3793step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 3, -2], ![-1, 1, -1, 1], ![-1, 0, -1, 2]]

def raw3793step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, -1, 1, -1]]

def raw3794 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -3, 2], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def raw3794step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 3, -2], ![-1, 1, -2, 2], ![-1, 0, 0, 1]]

def raw3794step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, -1, 2, -2]]

def raw3795 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![0, 1, -1, 0], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw3795step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw3796 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![0, 1, -1, 0], ![2, -2, 2, -2]]

def raw3796step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![1, -2, -1, 2], ![1, 1, 0, -2]]

def raw3796step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, 1, 0, -2]]

def raw3797 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -2, 1, 0], ![1, 0, 0, -1]]

def raw3797step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw3798 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, -1, 0]]

def raw3798step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw3799 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw3799step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -2, 1, 0], ![1, 1, -1, -1]]

def raw3800 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw3801 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -2, 0, 0]]

def raw3801step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 2, -1], ![0, -1, -1, 2], ![-2, 2, 0, 0]]

def raw3801step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, -1, -1, 0]]

def raw3802 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![0, 1, 2, -3], ![2, -2, -1, 1]]

def raw3802step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 1, -3, 1]]

def raw3803 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![1, -2, -1, 2], ![1, 1, 2, -4]]

def raw3804 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![1, -2, 0, 1], ![1, 1, 1, -3]]

def raw3805 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![1, -2, 2, -1], ![1, 1, -1, -1]]

def raw3805step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 1, 0, -2]]

def raw3806 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw3806step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 2, -1], ![-1, 1, 0, 0], ![-1, 0, -1, 2]]

def raw3806step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def raw3807 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw3807step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 2, -1], ![-1, 1, -1, 1], ![-1, 0, 0, 1]]

def raw3807step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 1, -1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical119
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3808 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![1, 0, 1, -2], ![1, -1, 0, 0]]

def raw3808step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 2, -1], ![-1, 0, -1, 2], ![-1, 1, 0, 0]]

def raw3808step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def raw3809 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw3809step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw3810 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, 0, -1, 1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw3810step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw3811 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, 0, 0, 0], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw3811step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw3811step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw3812 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw3812step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0]]

def raw3812step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw3813 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, 1, -2]]

def raw3813step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw3814 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 0, 0, -1]]

def raw3814step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 1, 0], ![0, -1, 1, 0], ![-1, 2, -1, 0], ![-1, 0, 0, 1]]

def raw3814step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw3815 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw3815step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 1, 0], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 1, -1, 1]]

def raw3815step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1]]

def raw3816 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, -1, 0, 0]]

def raw3816step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 1, 0], ![0, -1, 1, 0], ![-1, 1, -1, 1], ![-1, 1, 0, 0]]

def raw3816step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1]]

def raw3817 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 1, 0], ![1, 0, -1, 0]]

def raw3817step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-1, 2, -1, 0], ![-1, 0, 1, 0]]

def raw3817step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw3818 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, 1, -1]]

def raw3819 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw3819step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 1, 0, 0]]

def raw3819step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, -1, 0]]

def raw3820 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, -1, -1, 1]]

def raw3820step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, 1, -1]]

def raw3821 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -2, 0, 1], ![1, 0, -1, 0]]

def raw3821step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw3822 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw3822step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -2, 1, 0], ![1, 1, -1, -1]]

def raw3823 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, -1, 1]]

def raw3823step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -2, 1, 0], ![1, 1, -1, -1]]

def raw3824 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -2, -1, 1]]

def raw3824step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 0, -2, 1]]

def raw3824step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -1, 2], ![-1, 1, -1, 1], ![-1, 0, 2, -1]]

def raw3824step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def raw3825 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![2, -2, -2, 2]]

def raw3825step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![1, -1, 2, -2], ![1, 0, -3, 2]]

def raw3825step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -1, 2], ![-1, 1, -2, 2], ![-1, 0, 3, -2]]

def raw3825step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 3, -2], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw3826 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![1, -2, -2, 3], ![1, 1, 2, -4]]

def raw3826step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![1, -1, -2, 2], ![1, 0, 3, -4]]

def raw3826step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 2, -1], ![-1, 1, 2, -2], ![-1, 0, -3, 4]]

def raw3826step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 4, -3], ![0, 2, -1, -1], ![1, -1, -2, 2]]

def raw3827 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![1, -2, -1, 2], ![1, 1, 1, -3]]

def raw3827step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![1, -1, -1, 1], ![1, 0, 2, -3]]

def raw3827step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 2, -1], ![-1, 1, 1, -1], ![-1, 0, -2, 3]]

def raw3827step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def raw3828 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 1, -1, -1]]

def raw3828step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 1, 0], ![-1, 2, -1, 0], ![-1, -1, 1, 1]]

def raw3828step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 1, -1, -1]]

def raw3829 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 1, -2]]

def raw3829step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw3830 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw3830step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw3831 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, 0, -1], ![1, -2, 0, 1], ![1, 1, -1, -1]]

def raw3831step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 0, 1], ![-1, 2, 0, -1], ![-1, -1, 1, 1]]

def raw3831step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 1, -1, -1]]

def raw3832 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, 0, -1], ![1, -2, 1, 0], ![1, 1, -2, 0]]

def raw3832step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 0, 1], ![-1, 2, -1, 0], ![-1, -1, 2, 0]]

def raw3832step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def raw3833 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw3833step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw3834 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -2, 1]]

def raw3834step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw3835 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, -1, 1, -1]]

def raw3835step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw3836 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, 1, -2], ![1, -2, 0, 1], ![1, 1, -2, 0]]

def raw3836step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![1, -2, 1, 0], ![1, 1, 0, -2]]

def raw3837 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, 1, -2], ![1, -2, 1, 0], ![1, 1, -3, 1]]

def raw3837step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![1, -2, 0, 1], ![1, 1, 1, -3]]

def raw3838 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw3838step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, -1, 2], ![-1, 1, 1, -1], ![-1, 0, 1, 0]]

def raw3838step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 1, -1, -1]]

def raw3839 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def raw3839step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, -1, 2], ![-1, 1, 0, 0], ![-1, 0, 2, -1]]

def raw3839step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]

def raw384step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]

def raw384step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

def raw385 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]

def raw385step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![2, 0, -2]]

def raw386 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]

def raw386step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2], ![-3, 3, 0]]

def raw386step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]

def raw387 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]

def raw387step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]

def raw387step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

def raw388 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]

def raw388step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]

def raw388step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

def raw389 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]

def raw389step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, -1, 2], ![-2, 2, 0], ![-2, 1, 1]]

def raw389step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]

def raw390 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -2, 0], ![3, 0, -3]]

def raw390step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 3, -3], ![2, 0, -2]]

def raw391 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]

def raw391step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-2, 1, 1], ![-3, 1, 2]]

def raw391step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 1, -2], ![1, 2, -3]]

def raw392 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![3, -2, -1]]

def raw392step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 3, -3], ![2, 0, -2]]

def raw393 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 1, -3], ![3, -3, 0]]

def raw393step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-2, -1, 3], ![-3, 3, 0]]

def raw393step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![3, -1, -2]]

def raw394 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]

def raw394step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]

def raw394step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]

def raw395 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]

def raw395step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]

def raw395step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]

def raw396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]

def raw396step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]

def raw396step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]

def raw397 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]

def raw397step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]

def raw397step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 2, -3]]

def raw398 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]

def raw398step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]

def raw398step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]

def raw399 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]

def raw399step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![3, -1, -2]]

def raw400 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]

def raw400step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 1, 1]]

def raw400step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]

def raw401 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -2, 0], ![3, -1, -2]]

def raw401step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-2, 2, 0], ![-3, 1, 2]]

def raw401step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![2, 1, -3]]

def raw402 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -1, -1], ![3, -2, -1]]

def raw402step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-2, 1, 1], ![-3, 2, 1]]

def raw402step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -3, 2], ![1, 1, -2], ![1, 2, -3]]

def raw411 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]

def raw411step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

def raw412 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]

def raw412step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

def raw413 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]

def raw413step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-3, 3, 0]]

def raw413step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]

def raw414 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]

def raw414step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

def raw415 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]

def raw415step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical120
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3840 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 0, -3, 2]]

def raw3840step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, -1, 2], ![-1, 1, -1, 1], ![-1, 0, 3, -2]]

def raw3840step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def raw3841 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, 2, -3], ![1, -2, 0, 1], ![1, 1, -3, 1]]

def raw3841step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -3, 2], ![1, -2, 1, 0], ![1, 1, 1, -3]]

def raw3842 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 0, -3, 2]]

def raw3842step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, -2, 3], ![-1, 1, 0, 0], ![-1, 0, 3, -2]]

def raw3842step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, -1, 0, 0]]

def raw3843 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -4, 2], ![2, -2, 3, -3]]

def raw3843step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -4, 3], ![1, 2, -3]]

def raw3844 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -3, 1], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw3844step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -2, 0], ![1, -3, 2, 0], ![1, 1, -1, -1]]

def raw3844step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def raw3845 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -3, 1], ![2, -2, 2, -2]]

def raw3845step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -3, 2], ![1, 1, -2]]

def raw3846 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw3846step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -1, -1], ![1, -2, 0, 1], ![1, 0, 0, -1]]

def raw3846step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw3847 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -2, 0], ![2, -2, 1, -1]]

def raw3847step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]

def raw3847step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1]]

def raw3847step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]

def raw3848 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -1, -1], ![1, -2, 1, 0], ![1, 0, -1, 0]]

def raw3848step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw3849 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, -1, 1, -1]]

def raw3850 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw3850step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 1, -2, 0]]

def raw3851 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, -1, -1, 1]]

def raw3851step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, -1, 1, -1]]

def raw3852 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 3, -4, 1], ![2, -3, 3, -2]]

def raw3852step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -4, 3], ![1, 1, -2]]

def raw3853 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 3, -2, -1], ![2, -3, 1, 0]]

def raw3853step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -2, 1], ![1, -1, 0]]

def raw3854 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 4, -2, -2], ![2, -4, 1, 1]]

def raw3854step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 4, -4], ![1, -2, 1], ![1, -2, 1]]

def raw3855 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -3, 1, 1], ![1, 3, -2, -2]]

def raw3855step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 1, -2], ![1, 1, -2]]

def raw3856 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -2, -2, 3], ![1, 2, 1, -4]]

def raw3856step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -2, 1], ![1, 3, -4]]

def raw3857 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -2, -1, 2], ![0, 1, -2, 1], ![1, 1, 2, -4]]

def raw3857step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![1, -2, -1, 2], ![1, 1, 2, -4]]

def raw3858 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -2, 1, 0], ![1, 2, -2, -1]]

def raw3858step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]

def raw3858step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw3859 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -2, 2, -1], ![1, 2, -3, 0]]

def raw3859step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, 2, -3], ![1, -1, 0]]

def raw3859step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -1, 0], ![1, 2, -3]]

def raw3860 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -2, 3, -2], ![1, 2, -4, 1]]

def raw3860step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, 3, -4], ![1, -2, 1]]

def raw3860step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -2, 1], ![1, 3, -4]]

def raw3861 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw3861step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 2, -1], ![0, -1, -1, 2], ![-1, 1, 0, 0]]

def raw3861step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def raw3862 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 2, -3, 0], ![1, -2, 2, -1]]

def raw3862step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1]]

def raw3862step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -1, 0], ![1, 2, -3]]

def raw3863 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 2, -2, -1], ![1, -2, 1, 0]]

def raw3863step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0]]

def raw3863step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw3864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]

def raw3864step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

def raw3865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]

def raw3865step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

def raw3867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]

def raw3867step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0], ![-2, 1, 1]]

def raw3867step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]

def raw3868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]

def raw3868step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, -2, 1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]

def raw3868step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]

def raw3869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]

def raw3869step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]

def raw3870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]

def raw3870step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]

def raw3870step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def raw3871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]

def raw3871step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical121
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]

def raw3872step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

def raw3873 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]

def raw3873step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

def raw3874 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]

def raw3874step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

def raw3875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]

def raw3875step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]

def raw3875step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]

def raw3876 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]

def raw3876step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]

def raw3877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

def raw3877step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]

def raw3877step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw3878 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]

def raw3878step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

def raw3879 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]

def raw3879step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

def raw3880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]

def raw3880step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

def raw3881 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]

def raw3881step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]

def raw3882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]

def raw3882step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]

def raw3882step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw3883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]

def raw3883step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]

def raw3883step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw3884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]

def raw3884step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]

def raw3884step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]

def raw3885 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

def raw3885step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]

def raw3885step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

def raw3886 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]

def raw3886step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]

def raw3886step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def raw3887 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]

def raw3887step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]

def raw3887step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

def raw3888 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]

def raw3888step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]

def raw3888step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]

def raw3889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]

def raw3889step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]

def raw3889step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw3890 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]

def raw3890step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]

def raw3890step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

def raw3891 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]

def raw3891step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]

def raw3891step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw3892 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![2, 0, -2]]

def raw3892step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 2, -2], ![2, 0, -2]]

def raw3893 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![2, -1, -1]]

def raw3893step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-2, 1, 1], ![-2, 1, 1]]

def raw3893step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2]]

def raw3894 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]

def raw3894step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]

def raw3895 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]

def raw3895step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]

def raw3895step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

def raw3896 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]

def raw3896step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]

def raw3896step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

def raw3897 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]

def raw3897step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 2, -1], ![-2, -1, 3]]

def raw3897step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]

def raw3898 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]

def raw3898step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]

def raw3898step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

def raw3899 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]

def raw3899step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]

def raw3899step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

def raw3900 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]

def raw3901 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![2, -2, 0], ![1, 1, -2]]

def raw3901step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]

def raw3902 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]

def raw3902step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -3, 3], ![-1, 2, -1], ![-2, 0, 2]]

def raw3902step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]

def raw3903 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]

def raw3903step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -3, 3], ![-1, 0, 1], ![-2, 2, 0]]

def raw3903step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical122
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3904 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]

def raw3904step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -3, 4]]

def raw3904step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]

def raw3905 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, 1, -2], ![1, -1, 0], ![1, 1, -2]]

def raw3905step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![-1, -1, 2], ![-1, 1, 0], ![-1, -1, 2]]

def raw3905step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

def raw3906 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, 2, -3], ![2, -1, -1]]

def raw3906step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![-1, -2, 3], ![-2, 1, 1]]

def raw3906step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

def raw3907 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, 3, -4], ![2, -2, 0]]

def raw3907step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![-1, -3, 4], ![-2, 2, 0]]

def raw3907step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]

def raw3908 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]

def raw3908step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw3909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]

def raw3909step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]

def raw3910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]

def raw3910step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]

def raw3911 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]

def raw3911step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]

def raw3911step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def raw3912 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]

def raw3912step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]

def raw3912step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw3913 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]

def raw3913step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

def raw3914 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]

def raw3914step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

def raw3916 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]

def raw3916step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-2, -3, 5]]

def raw3916step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]

def raw3917 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]

def raw3917step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -3, 4]]

def raw3917step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

def raw3920 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]

def raw3920step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]

def raw3921 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]

def raw3921step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]

def raw3922 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]

def raw3926 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]

def raw3926step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0]]

def raw3927 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]

def raw3927step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]

def raw3927step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

def raw3928 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]

def raw3928step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

def raw3932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]

def raw3932step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]

def raw3932step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]

def raw3933 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]

def raw3933step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

def raw3934 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]

def raw3934step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]

def raw3934step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw3935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]

def raw3935step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical123
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3936 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]

def raw3936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1]]

def raw3936step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]

def raw3937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]

def raw3937step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]

def raw3938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]

def raw3938step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]

def raw3938step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]

def raw3939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]

def raw3939step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]

def raw3939step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw3940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]

def raw3940step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-2, -2, 4]]

def raw3940step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]

def raw3941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]

def raw3941step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw3942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

def raw3942step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw3943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]

def raw3944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]

def raw3946 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]

def raw3946step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]

def raw3948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]

def raw3949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]

def raw3950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]

def raw3950step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw3951 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]

def raw3951step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw3952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![2, 1, -3]]

def raw3952step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![-2, -1, 3]]

def raw3952step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]

def raw3953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

def raw3953step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]

def raw3953step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw3954 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]

def raw3954step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]

def raw3954step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw3955 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]

def raw3955step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw3956 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

def raw3957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]

def raw3957step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]

def raw3958 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]

def raw3958step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

def raw3959 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]

def raw3959step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw3960 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]

def raw3960step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]

def raw3960step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def raw3963 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]

def raw3963step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]

def raw3963step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]

def raw3964 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]

def raw3964step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

def raw3965 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]

def raw3966 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]

def raw3966step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]

def raw3966step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw3967 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]

def raw3967step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical124
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3968 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]

def raw3968step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]

def raw3968step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]

def raw3969 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]

def raw3969step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]

def raw3970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]

def raw3971 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]

def raw3972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]

def raw3972step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]

def raw3972step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0]]

def raw3973 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]

def raw3973step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]

def raw3974 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]

def raw3974step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]

def raw3974step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]

def raw3975 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]

def raw3975step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def raw3976 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]

def raw3976step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]

def raw3977 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

def raw3977step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]

def raw3977step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]

def raw3978 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]

def raw3978step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]

def raw3978step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw3979 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 1, -2], ![2, -3, 1]]

def raw3979step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

def raw3980 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]

def raw3980step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -3, 2], ![0, 2, -2], ![-1, 0, 1], ![-2, 1, 1]]

def raw3980step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]

def raw3981 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, -3, 2], ![1, -1, 0], ![1, 1, -2]]

def raw3982 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]

def raw3982step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]

def raw3983 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, -3, 2], ![2, 0, -2]]

def raw3983step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]

def raw3984 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]

def raw3984step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -3, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]

def raw3984step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]

def raw3985 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, -2, 1], ![2, -1, -1]]

def raw3985step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -3, 2], ![-1, 2, -1], ![-2, 1, 1]]

def raw3985step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

def raw3986 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![2, -4, 2], ![1, 1, -2]]

def raw3986step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -3, 2], ![-2, 4, -2], ![-1, -1, 2]]

def raw3986step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 2, -3], ![2, -2, 0]]

def raw3987 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 4, -3], ![0, -2, 2], ![1, -1, 0], ![2, -1, -1]]

def raw3988 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 4, -3], ![0, -2, 2], ![2, -2, 0], ![1, 0, -1]]

def raw3988step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -4, 3], ![0, 2, -2], ![-2, 2, 0], ![-1, 0, 1]]

def raw3988step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 3, -4], ![2, -2, 0]]

def raw3989 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 4, -3], ![0, -2, 2], ![3, -2, -1]]

def raw3989step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -4, 3], ![0, 2, -2], ![-3, 2, 1]]

def raw3989step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 3, -4], ![2, -2, 0]]

def raw3990 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 4, -3], ![1, -3, 2], ![1, -1, 0], ![1, 0, -1]]

def raw3991 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 4, -3], ![1, -3, 2], ![2, -1, -1]]

def raw3992 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 4, -3], ![1, -2, 1], ![1, -2, 1], ![1, 0, -1]]

def raw3993 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 4, -3], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]

def raw3993step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]

def raw3994 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 4, -3], ![1, -2, 1], ![2, -2, 0]]

def raw3994step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]

def raw3995 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 4, -3], ![2, -4, 2], ![1, 0, -1]]

def raw3995step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -4, 3], ![-2, 4, -2], ![-1, 0, 1]]

def raw3995step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 3, -4], ![2, -2, 0]]

def raw3996 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 4, -3], ![2, -2, 0], ![1, -2, 1]]

def raw3996step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]

def raw3997 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 1, -1], ![0, 1, -1], ![2, 1, -3]]

def raw3997step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 3, -3], ![0, -1, 1], ![0, -1, 1], ![-2, -1, 3]]

def raw3997step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![2, 0, -2]]

def raw3998 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

def raw3999 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 1, -1], ![1, -1, 0], ![1, 3, -4]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical125
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4000 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 1, -1], ![1, 0, -1], ![1, 2, -3]]

def raw4001 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

def raw4002 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 2, -2], ![0, 1, -1], ![2, 0, -2]]

def raw4002step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

def raw4003 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

def raw4004 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 2, -2], ![1, 1, -2], ![1, 0, -1]]

def raw4004step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

def raw4005 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 2, -2], ![2, 1, -3]]

def raw4005step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 3, -3], ![0, -2, 2], ![-2, -1, 3]]

def raw4005step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 3, -3], ![2, 0, -2]]

def raw4006 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

def raw4007 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 3, -3], ![2, 0, -2]]

def raw4008 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 4, -4], ![1, -1, 0], ![1, 0, -1]]

def raw4009 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 4, -4], ![2, -1, -1]]

def raw4010 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, -1, 0], ![1, 4, -5]]

def raw4011 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 0, -1], ![1, 3, -4]]

def raw4012 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 1, -2], ![1, 2, -3]]

def raw4013 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 2, -3], ![1, 1, -2]]

def raw4013step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 1, -2], ![1, 2, -3]]

def raw4014 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 3, -4], ![1, 0, -1]]

def raw4014step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 0, -1], ![1, 3, -4]]

def raw4015 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![2, 3, -5]]

def raw4015step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![0, 3, -3], ![-2, -3, 5]]

def raw4015step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 3, -3], ![2, 0, -2]]

def raw4016 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![-1, 3, -2], ![1, -1, 0], ![2, 0, -2]]

def raw4016step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![1, -3, 2], ![-1, 1, 0], ![-2, 0, 2]]

def raw4016step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]

def raw4017 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![-1, 3, -2], ![1, 0, -1], ![2, -1, -1]]

def raw4017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![1, -3, 2], ![-1, 0, 1], ![-2, 1, 1]]

def raw4017step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]

def raw4018 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 4, -5]]

def raw4019 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 3, -4]]

def raw4020 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 0, 0], ![0, 2, -2], ![2, 0, -2]]

def raw4020step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 2, -2], ![2, 0, -2]]

def raw4021 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 0, 0], ![1, -1, 0], ![1, 3, -4]]

def raw4021step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, -1, 0], ![1, 3, -4]]

def raw4022 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![1, 2, -3]]

def raw4022step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]

def raw4022step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![-1, 0, 1], ![-1, -2, 3]]

def raw4022step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]

def raw4023 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

def raw4024 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

def raw4025 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![1, -2, 1], ![1, 3, -4]]

def raw4026 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def raw4027 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw4028 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1]]

def raw4028step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw4029 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![2, 1, -3]]

def raw4029step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![0, -1, 1], ![-2, -1, 3]]

def raw4029step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]

def raw4030 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 2, -2], ![0, 0, 0], ![2, 0, -2]]

def raw4030step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 2, -2], ![2, 0, -2]]

def raw4031 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 2, -2], ![0, 1, -1], ![2, -1, -1]]

def raw4031step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical126
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4032 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

def raw4033 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def raw4033step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

def raw4034 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 2, -2], ![2, 0, -2]]

def raw4035 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw4036 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1], ![1, -1, 0]]

def raw4036step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw4037 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![2, -1, -1]]

def raw4038 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 4, -4], ![1, -2, 1], ![1, 0, -1]]

def raw4039 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 4, -4], ![1, -1, 0], ![1, -1, 0]]

def raw4040 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 4, -4], ![2, -2, 0]]

def raw4041 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, -2, 1], ![1, 4, -5]]

def raw4042 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, -1, 0], ![1, 3, -4]]

def raw4043 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, 0, -1], ![1, 2, -3]]

def raw4043step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![-1, 0, 1], ![-1, -2, 3]]

def raw4043step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]

def raw4044 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2]]

def raw4045 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1]]

def raw4045step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![-1, -2, 3], ![-1, 0, 1]]

def raw4045step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]

def raw4046 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, 3, -4], ![1, -1, 0]]

def raw4046step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, -1, 0], ![1, 3, -4]]

def raw4047 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, 4, -5], ![1, -2, 1]]

def raw4047step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, -2, 1], ![1, 4, -5]]

def raw4048 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![2, 2, -4]]

def raw4048step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![-2, -2, 4]]

def raw4048step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![2, 0, -2]]

def raw4049 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]

def raw4049step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

def raw4050 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 3, -2], ![1, 0, -1], ![2, -2, 0]]

def raw4050step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -3, 2], ![-1, 0, 1], ![-2, 2, 0]]

def raw4050step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]

def raw4051 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -2, 2], ![1, -1, 0], ![1, 4, -5]]

def raw4051step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 4, -5]]

def raw4052 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 3, -4]]

def raw4052step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 3, -4]]

def raw4053 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 4, -5]]

def raw4054 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def raw4055 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 4, -5]]

def raw4056 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![0, 4, -4]]

def raw4056step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0], ![1, -1, 0]]

def raw4057 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![0, 3, -3]]

def raw4057step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw4058 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

def raw4059 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3]]

def raw4059step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -2, 3]]

def raw4059step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def raw4060 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2]]

def raw4060step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]

def raw4060step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1]]

def raw4061 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]

def raw4061step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]

def raw4062 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![1, -2, 1], ![1, 3, -4]]

def raw4062step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, -2, 1], ![1, 3, -4]]

def raw4063 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3]]

def raw4063step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]

def raw4063step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, -2, 3]]

def raw4063step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical127
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4064 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2]]

def raw4064step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]

def raw4064step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2]]

def raw4064step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

def raw4065 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2]]

def raw4065step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]

def raw4065step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1]]

def raw4066 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw4067 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def raw4068 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

def raw4069 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -3, 2], ![1, 3, -4]]

def raw4070 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 2, -3]]

def raw4071 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw4072 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw4072step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw4073 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]

def raw4073step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw4074 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]

def raw4074step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1]]

def raw4075 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![0, 1, -1], ![2, -2, 0]]

def raw4075step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

def raw4076 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

def raw4077 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw4078 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]

def raw4078step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw4079 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]

def raw4080 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

def raw4081 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def raw4082 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![2, -2, 0]]

def raw4083 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 4, -4], ![1, -3, 2], ![1, 0, -1]]

def raw4084 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 4, -4], ![1, -2, 1], ![1, -1, 0]]

def raw4085 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0], ![1, -2, 1]]

def raw4085step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 4, -4], ![1, -2, 1], ![1, -1, 0]]

def raw4086 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, -3, 2], ![1, 4, -5]]

def raw4087 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, -2, 1], ![1, 3, -4]]

def raw4088 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]

def raw4088step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, -2, 3]]

def raw4088step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw4089 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]

def raw4089step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2]]

def raw4089step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

def raw4090 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]

def raw4090step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, -1, 2], ![-1, 0, 1]]

def raw4090step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

def raw4093 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]

def raw4093step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]

def raw4094 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw4094step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw4095 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw4095step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw4095step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical128
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4096 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]

def raw4096step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]

def raw4096step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![1, -1, 0]]

def raw4097 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]

def raw4097step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 0, 0], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1]]

def raw4097step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1]]

def raw4097step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]

def raw4098 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]

def raw4098step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]

def raw4098step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]

def raw4099 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]

def raw4099step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -2, 0]]

def raw4100 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 3, -3], ![1, -2, 1], ![1, -1, 0]]

def raw4100step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -2, 1], ![1, -1, 0]]

def raw4101 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, -3, 2], ![1, 3, -4]]

def raw4101step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -3, 3], ![2, 0, 2, -4]]

def raw4101step1 : Matrix (Fin 3) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 3, -3], ![-2, 0, -2, 4]]

def raw4101step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -1, -1], ![0, 3, -3], ![-2, -2, 4]]

def raw4101step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![2, -1, -1]]

def raw4102 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, -2, 1], ![1, 2, -3]]

def raw4102step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 0, 0], ![-1, 2, -1], ![-1, -2, 3]]

def raw4102step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![-1, -2, 3]]

def raw4102step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]

def raw4103 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]

def raw4103step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2]]

def raw4103step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![-1, -1, 2]]

def raw4103step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![1, -1, 0]]

def raw4104 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]

def raw4104step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]

def raw4105 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]

def raw4105step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![1, -2, 1], ![-1, 1, 0], ![-2, 2, 0]]

def raw4105step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0]]

def raw4106 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]

def raw4106step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw4107 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0]]

def raw4107step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]

def raw4108 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]

def raw4108step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw4109 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]

def raw4109step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw4109step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0]]

def raw4110 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]

def raw4110step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]

def raw4110step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![1, -1, 0]]

def raw4111 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]

def raw4111step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def raw4112 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]

def raw4112step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]

def raw4113 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1]]

def raw4113step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 3, -1]]

def raw4113step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]

def raw4114 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 1, -2]]

def raw4115 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]

def raw4116 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]

def raw4117 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]

def raw4118 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 2, -2], ![0, -2, 2], ![2, -1, -1]]

def raw4118step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

def raw4119 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 2, -2], ![0, -1, 1], ![2, -2, 0]]

def raw4119step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

def raw4120 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1]]

def raw4121 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0]]

def raw4122 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -2, 1]]

def raw4122step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0]]

def raw4123 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 2, -2], ![2, -3, 1]]

def raw4123step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -2, 2], ![-2, 3, -1]]

def raw4123step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

def raw4124 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 3, -3], ![1, -3, 2], ![1, -1, 0]]

def raw4125 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 3, -3], ![1, -2, 1], ![1, -2, 1]]

def raw4126 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -4, 3], ![1, 3, -4]]

def raw4127 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -3, 2], ![1, 2, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical129
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4128 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2]]

def raw4128step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw4129 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]

def raw4129step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0]]

def raw4130 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw4131 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw4131step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0]]

def raw4132 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-1, 3, -2], ![1, -3, 2]]

def raw4132step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 1, -1], ![1, -3, 2], ![1, -1, 0], ![1, 0, -1]]

def raw4133 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]

def raw4133step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0]]

def raw4134 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]

def raw4134step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![1, -1, 0]]

def raw4135 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1]]

def raw4135step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]

def raw4136 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1]]

def raw4136step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1]]

def raw4137 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0]]

def raw4137step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0]]

def raw4138 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -3, 2], ![1, 1, -2]]

def raw4139 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]

def raw4139step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1]]

def raw4139step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]

def raw4140 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]

def raw4140step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]

def raw4141 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -2, 0]]

def raw4142 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1]]

def raw4142step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw4143 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, -2, 2], ![2, -1, -1]]

def raw4143step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![2, -1, -1]]

def raw4144 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -3, 2], ![1, 0, -1]]

def raw4145 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -2, 1], ![1, -1, 0]]

def raw4146 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -1, 0], ![1, -2, 1]]

def raw4146step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -2, 1], ![1, -1, 0]]

def raw4147 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![2, -3, 1]]

def raw4147step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![0, -3, 3], ![-2, 3, -1]]

def raw4147step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![2, -2, 0]]

def raw4148 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 4, -4], ![1, -4, 3], ![1, 0, -1]]

def raw4149 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 4, -4], ![1, -3, 2], ![1, -1, 0]]

def raw4150 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 4, -4], ![1, -2, 1], ![1, -2, 1]]

def raw4151 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 4, -4], ![2, -4, 2]]

def raw4151step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![0, -4, 4], ![-2, 4, -2]]

def raw4151step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 4, -4], ![2, -2, 0]]

def raw4152 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -4, 3], ![0, 4, -4], ![1, 0, -1]]

def raw4152step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 4, -4], ![1, -4, 3], ![1, 0, -1]]

def raw4153 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -4, 3], ![1, 4, -5]]

def raw4153step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -4, 4], ![2, 3, -5]]

def raw4153step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -1, -1], ![0, 4, -4], ![-2, -3, 5]]

def raw4153step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 4, -4], ![2, -1, -1]]

def raw4154 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -3, 2], ![0, 2, -2], ![1, 1, -2]]

def raw4154step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -3, 2], ![1, 1, -2]]

def raw4155 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -3, 2], ![0, 3, -3], ![1, 0, -1]]

def raw4155step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -3, 2], ![1, 0, -1]]

def raw4156 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -3, 2], ![0, 4, -4], ![1, -1, 0]]

def raw4156step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 4, -4], ![1, -3, 2], ![1, -1, 0]]

def raw4157 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -3, 2], ![1, 3, -4]]

def raw4157step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![2, 2, -4]]

def raw4157step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -1, -1], ![0, 3, -3], ![-2, -2, 4]]

def raw4157step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![2, -1, -1]]

def raw4158 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -2, 1], ![0, 4, -4], ![1, -2, 1]]

def raw4158step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 4, -4], ![1, -2, 1], ![1, -2, 1]]

def raw4159 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -2, 1], ![1, 2, -3]]

def raw4159step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![-1, -2, 3]]

def raw4159step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw416 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]

def raw416step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

def raw417 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]

def raw417step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]

def raw417step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]

def raw418 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]

def raw418step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 1, 1]]

def raw418step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]

def raw419 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]

def raw419step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 2, 0], ![-3, 1, 2]]

def raw419step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]

def raw423 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]

def raw423step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

def raw425 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]

def raw425step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw426 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]

def raw426step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw427 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]

def raw427step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]

def raw428step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw429 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]

def raw429step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw430 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]

def raw430step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]

def raw430step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]

def raw431 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]

def raw431step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw432 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]

def raw432step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw433 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]

def raw433step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]

def raw434 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]

def raw434step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]

def raw434step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]

def raw436 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical130
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4160 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![1, 1, -2]]

def raw4160step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![-1, -1, 2]]

def raw4160step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![1, -1, 0]]

def raw4161 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 2, -3], ![1, -2, 1]]

def raw4161step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![-1, -2, 3], ![-1, 2, -1]]

def raw4161step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]

def raw4162 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 3, -4], ![1, -3, 2]]

def raw4162step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 3, -3], ![2, -4, 2]]

def raw4162step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -1, -1], ![0, -3, 3], ![-2, 4, -2]]

def raw4162step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![2, -1, -1]]

def raw4163 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 4, -5], ![1, -4, 3]]

def raw4163step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 4, -4], ![2, -5, 3]]

def raw4163step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -1, -1], ![0, -4, 4], ![-2, 5, -3]]

def raw4163step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 4, -4], ![2, -1, -1]]

def raw4164 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![-3, 2, -1, 2], ![5, -2, -1, -2]]

def raw4164step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![2, -1, -1], ![0, 2, -2]]

def raw4164step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![0, 2, -2], ![2, -1, -1]]

def raw4165 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![-2, 2, -2, 2], ![4, -2, 0, -2]]

def raw4165step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![2, -2, 0], ![0, 2, -2]]

def raw4165step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 2, -2], ![2, -2, 0]]

def raw4166 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![-2, 2, -1, 1], ![4, -2, -1, -1]]

def raw4166step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![2, -1, -1], ![0, 1, -1]]

def raw4166step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

def raw4167 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![-2, 2, 1, -1], ![4, -2, -3, 1]]

def raw4167step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![2, 1, -3], ![0, -1, 1]]

def raw4167step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 2, -2], ![2, 1, -3]]

def raw4168 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![-2, 3, 0, -1], ![4, -3, -2, 1]]

def raw4168step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![2, 0, -2], ![0, -1, 1]]

def raw4168step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 3, -3], ![2, 0, -2]]

def raw4169 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![-1, -2, 0, 3], ![3, 2, -2, -3]]

def raw4169step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![2, 0, -2], ![0, 3, -3]]

def raw4169step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 3, -3], ![2, 0, -2]]

def raw4170 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![-1, -2, 1, 2], ![3, 2, -3, -2]]

def raw4170step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![2, 1, -3], ![0, 2, -2]]

def raw4170step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![2, 1, -3]]

def raw4171 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![-1, 2, -2, 1], ![3, -2, 0, -1]]

def raw4171step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -2, 0], ![0, 1, -1]]

def raw4171step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

def raw4172 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![-1, 2, 0, -1], ![3, -2, -2, 1]]

def raw4172step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, 0, -2], ![0, -1, 1]]

def raw4172step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]

def raw4173 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![-1, 2, 1, -2], ![3, -2, -3, 2]]

def raw4173step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, 1, -3], ![0, -2, 2]]

def raw4173step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![2, 1, -3]]

def raw4174 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![-1, 3, -1, -1], ![3, -3, -1, 1]]

def raw4174step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![2, -1, -1], ![0, -1, 1]]

def raw4174step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 3, -3], ![2, -1, -1]]

def raw4175 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![-1, 3, 0, -2], ![3, -3, -2, 2]]

def raw4175step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![2, 0, -2], ![0, -2, 2]]

def raw4175step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 3, -3], ![2, 0, -2]]

def raw4176 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![-1, 4, -2, -1], ![3, -4, 0, 1]]

def raw4176step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 4, -4], ![2, -2, 0], ![0, -1, 1]]

def raw4176step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 4, -4], ![2, -2, 0]]

def raw4177 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, -3, 0, 3], ![2, 3, -2, -3]]

def raw4177step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![2, 0, -2], ![0, 3, -3]]

def raw4177step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 3, -3], ![2, 0, -2]]

def raw4178 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, -3, 2, 1], ![2, 3, -4, -1]]

def raw4178step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![2, 2, -4], ![0, 1, -1]]

def raw4178step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 3, -3], ![-2, -2, 4], ![0, -1, 1]]

def raw4178step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 3, -3], ![2, 0, -2]]

def raw4179 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, -2, -2, 4], ![2, 2, 0, -4]]

def raw4179step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![2, -2, 0], ![0, 4, -4]]

def raw4179step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 4, -4], ![2, -2, 0]]

def raw4180 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, -2, -1, 3], ![2, 2, -1, -3]]

def raw4180step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![2, -1, -1], ![0, 3, -3]]

def raw4180step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![2, -1, -1]]

def raw4181 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, -2, 0, 2], ![2, 2, -2, -2]]

def raw4181step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![2, 0, -2], ![0, 2, -2]]

def raw4181step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 2, -2], ![2, 0, -2]]

def raw4182 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, -2, 1, 1], ![2, 2, -3, -1]]

def raw4182step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![2, 1, -3], ![0, 1, -1]]

def raw4182step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![-2, -1, 3], ![0, -1, 1]]

def raw4182step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]

def raw4183 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, -2, 3, -1], ![2, 2, -5, 1]]

def raw4183step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![2, 3, -5], ![0, -1, 1]]

def raw4183step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![-2, -3, 5], ![0, 1, -1]]

def raw4183step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

def raw4184 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, -1, -3, 4], ![0, 1, 1, -2], ![2, 0, 0, -2]]

def raw4184step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -2, 2, 0], ![0, 2, 0, -2], ![1, 0, 1, -2]]

def raw4185 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, -1, -3, 4], ![1, 0, 1, -2], ![1, 1, 0, -2]]

def raw4185step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -2, 0], ![0, 1, 3, -4], ![-1, 0, -1, 2], ![-1, -1, 0, 2]]

def raw4185step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 2, -2, 0], ![1, 0, 3, -4]]

def raw4186 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, -1, -1, 2], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw4186step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw4187 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, -1, -1, 2], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw4187step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 2, -2, 0], ![1, 0, 1, -2]]

def raw4188 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, 0, -2, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -2, 1, -1]]

def raw4188step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw4189 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw4189step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw4190 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, 0, -2, 2], ![0, 1, 0, -1], ![2, -1, 0, -1]]

def raw4190step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def raw4191 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw4191step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -2, 0], ![0, 0, 2, -2], ![-1, 1, 0, 0], ![-1, -1, 0, 2]]

def raw4191step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 0, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical131
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4192 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, 0, 1, -1], ![1, -1, -3, 3], ![1, 1, 0, -2]]

def raw4192step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![2, 1, -3, 0], ![0, -1, 3, -2]]

def raw4192step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 1, -1], ![-2, -1, 3, 0], ![0, 1, -3, 2]]

def raw4192step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, 0, 2, -3]]

def raw4193 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -2, 3], ![1, 0, 0, -1]]

def raw4193step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw4194 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, 2, -4, 2], ![2, -2, 2, -2]]

def raw4194step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -4, 2], ![0, 2, -2]]

def raw4194step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -2, 2], ![-2, 4, -2], ![0, -2, 2]]

def raw4194step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 2, -2], ![2, -2, 0]]

def raw4195 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, 2, -3, 1], ![2, -2, 1, -1]]

def raw4195step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -3, 1], ![0, 1, -1]]

def raw4195step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -2, 2], ![-2, 3, -1], ![0, -1, 1]]

def raw4195step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

def raw4196 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, 2, -1, -1], ![2, -2, -1, 1]]

def raw4196step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -1, -1], ![0, -1, 1]]

def raw4196step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]

def raw4197 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, 2, 0, -2], ![2, -2, -2, 2]]

def raw4197step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, 0, -2], ![0, -2, 2]]

def raw4197step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 2, -2], ![2, 0, -2]]

def raw4198 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, 2, 1, -3], ![2, -2, -3, 3]]

def raw4198step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, 1, -3], ![0, -3, 3]]

def raw4198step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -2, 2], ![-2, -1, 3], ![0, 3, -3]]

def raw4198step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 3, -3], ![2, 0, -2]]

def raw4199 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, 3, -4, 1], ![2, -3, 2, -1]]

def raw4199step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![2, -4, 2], ![0, 1, -1]]

def raw4199step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -3, 3], ![-2, 4, -2], ![0, -1, 1]]

def raw4199step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 3, -3], ![2, -2, 0]]

def raw4200 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, 3, -2, -1], ![2, -3, 0, 1]]

def raw4200step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![2, -2, 0], ![0, -1, 1]]

def raw4200step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![2, -2, 0]]

def raw4201 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, 3, -1, -2], ![2, -3, -1, 2]]

def raw4201step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![2, -1, -1], ![0, -2, 2]]

def raw4201step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![2, -1, -1]]

def raw4202 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, 3, 0, -3], ![2, -3, -2, 3]]

def raw4202step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![2, 0, -2], ![0, -3, 3]]

def raw4202step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 3, -3], ![2, 0, -2]]

def raw4203 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, 4, -3, -1], ![2, -4, 1, 1]]

def raw4203step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 4, -4], ![2, -3, 1], ![0, -1, 1]]

def raw4203step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -4, 4], ![-2, 3, -1], ![0, 1, -1]]

def raw4203step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 4, -4], ![2, -2, 0]]

def raw4204 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, 4, -2, -2], ![2, -4, 0, 2]]

def raw4204step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 4, -4], ![2, -2, 0], ![0, -2, 2]]

def raw4204step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 4, -4], ![2, -2, 0]]

def raw4205 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![1, -3, 1, 1], ![1, 3, -3, -1]]

def raw4205step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![2, 1, -3], ![0, 1, -1]]

def raw4205step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 3, -3], ![-2, -1, 3], ![0, -1, 1]]

def raw4205step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 3, -3], ![2, -1, -1]]

def raw4206 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![1, -2, -3, 4], ![0, 1, 1, -2], ![1, 1, 0, -2]]

def raw4206step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -2, 1, 1], ![2, -3, 1, 0], ![0, 4, -2, -2]]

def raw4206step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -2, 1], ![1, 0, 2, -3], ![1, 1, 0, -2]]

def raw4207 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![1, -2, -1, 2], ![1, 2, -1, -2]]

def raw4207step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![2, -1, -1], ![0, 2, -2]]

def raw4207step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]

def raw4208 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![1, -2, 0, 1], ![1, 2, -2, -1]]

def raw4208step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![2, 0, -2], ![0, 1, -1]]

def raw4208step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 2, -2], ![-2, 0, 2], ![0, -1, 1]]

def raw4208step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]

def raw4209 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![1, -2, 2, -1], ![1, 2, -4, 1]]

def raw4209step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![2, 2, -4], ![0, -1, 1]]

def raw4209step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 2, -2], ![-2, -2, 4], ![0, 1, -1]]

def raw4209step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

def raw4210 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![1, 2, -1, -2], ![1, -2, -1, 2]]

def raw4210step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![2, -1, -1], ![0, -2, 2]]

def raw4210step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]

def raw4211 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![1, 2, 0, -3], ![1, -2, -2, 3]]

def raw4211step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![2, 0, -2], ![0, -3, 3]]

def raw4211step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, -2, 2], ![-2, 0, 2], ![0, 3, -3]]

def raw4211step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![2, -1, -1]]

def raw4212 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![-2, 2, -2, 2], ![4, -2, -1, -1]]

def raw4212step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![3, -2, -1], ![-1, 2, -1]]

def raw4212step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, -2, 2], ![-3, 2, 1], ![1, -2, 1]]

def raw4212step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -4, 2]]

def raw4213 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![-1, 2, -2, 1], ![3, -2, -1, 0]]

def raw4213step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![3, -2, -1], ![-1, 1, 0]]

def raw4213step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -2, 2], ![-3, 2, 1], ![1, -1, 0]]

def raw4213step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]

def raw4214 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, -1, -3, 4], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw4215 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, -1, -3, 4], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw4215step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -2, 3, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw4216 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, -1, -3, 4], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw4216step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -3, 1], ![0, 1, 3, -4], ![0, -2, 0, 2], ![-1, 1, 0, 0], ![-1, 0, 0, 1]]

def raw4216step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, 2, -3, 1], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw4217 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, -1, -3, 4], ![1, -1, 0, 0], ![1, 2, 0, -3]]

def raw4217step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![3, -3, 0, 0], ![-1, 4, 0, -3]]

def raw4217step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, 1, -2], ![-3, 3, 0, 0], ![1, -4, 0, 3]]

def raw4217step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, 0, -3, 3], ![0, 3, 1, -4], ![1, -2, 0, 1]]

def raw4218 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, -1, -3, 4], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw4218step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![3, -3, 0, 0], ![-1, 4, -1, -2]]

def raw4218step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 3, -3], ![0, 1, 0, -1], ![1, 1, -2, 0]]

def raw4219 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, -1, -2, 3], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, 0, -2]]

def raw4220 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, -1, -2, 3], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw4220step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 3, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw4221 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, -1, -2, 3], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw4221step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -3, 1], ![0, 1, 2, -3], ![0, -2, 0, 2], ![-1, 1, 1, -1], ![-1, 0, 0, 1]]

def raw4221step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, 2, -3, 1], ![1, -1, 1, -1], ![1, 0, 2, -3]]

def raw4222 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, -1, -2, 3], ![1, -1, -1, 1], ![1, 2, 0, -3]]

def raw4222step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -3, 1], ![0, 1, 2, -3], ![-1, 1, 1, -1], ![-1, -2, 0, 3]]

def raw4222step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, -3, 1], ![1, -1, 1, -1], ![1, 0, 2, -3]]

def raw4223 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, -1, -2, 3], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw4223step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -3, 1], ![0, 1, 2, -3], ![-1, 0, 1, 0], ![-1, -1, 0, 2]]

def raw4223step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 2, -3, 1], ![1, 0, 2, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical132
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4224 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, 0, -3, 3], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw4224step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -3, 1], ![0, 0, 3, -3], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1]]

def raw4224step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 3, -3], ![0, 2, -3, 1], ![1, -1, 0, 0]]

def raw4225 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, 0, -3, 3], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw4225step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -3, 1], ![0, 0, 3, -3], ![-1, 1, 0, 0], ![-1, -1, 0, 2]]

def raw4225step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 2, -3, 1], ![1, -1, 0, 0]]

def raw4226 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -2, -1, 2], ![1, 1, 0, -2]]

def raw4227 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw4227step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -3, 1], ![0, 0, 2, -2], ![0, -1, 0, 1], ![-1, 1, 1, -1], ![-1, 0, 0, 1]]

def raw4227step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 2, -3, 1], ![1, -1, 1, -1]]

def raw4228 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -2, -1, 2], ![1, 0, 0, -1]]

def raw4228step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -3, 1], ![0, 0, 2, -2], ![0, -2, 0, 2], ![-1, 2, 1, -2], ![-1, 0, 0, 1]]

def raw4228step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 2, -3, 1], ![2, -1, 1, -2]]

def raw4229 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, 0, -2, 2], ![1, -2, -1, 2], ![1, 2, 0, -3]]

def raw4229step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -3, 1], ![0, 0, 2, -2], ![-1, 2, 1, -2], ![-1, -2, 0, 3]]

def raw4229step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 2, -3, 1], ![2, -1, 1, -2]]

def raw4230 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, 0, -2, 2], ![1, -1, -1, 1], ![1, 1, 0, -2]]

def raw4230step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -3, 1], ![0, 0, 2, -2], ![-1, 1, 1, -1], ![-1, -1, 0, 2]]

def raw4230step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -3, 1], ![1, -1, 1, -1]]

def raw4231 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -2, -1, 2], ![1, 0, 0, -1]]

def raw4231step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 0, -1, 0]]

def raw4232 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, 1, -2, 1], ![1, -2, -1, 2], ![1, 1, 0, -2]]

def raw4232step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 1, -2, 0]]

def raw4233 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, -2, 3], ![1, 0, 0, -1]]

def raw4233step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, -1, 0]]

def raw4234 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -2, -2, 3], ![1, 0, 0, -1]]

def raw4234step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, -1, 0]]

def raw4235 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -3, 4], ![1, 0, 0, -1]]

def raw4236 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -2, 3], ![1, 0, -1, 0]]

def raw4236step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def raw4237 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, 1, 0, -1], ![1, -2, -3, 4], ![1, 1, 0, -2]]

def raw4237step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![3, 0, -3, 0], ![-1, -1, 4, -2]]

def raw4237step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, 1, 0, -2]]

def raw4238 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, 1, 0, -1], ![1, -1, -3, 3], ![1, 0, 0, -1]]

def raw4238step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![3, 0, -3, 0], ![-1, -1, 3, -1]]

def raw4238step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, 0, 0, -1]]

def raw4239 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, 2, 0, -2], ![1, -2, -3, 4], ![1, 0, 0, -1]]

def raw4239step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -2, 0], ![3, 0, -3, 0], ![-1, -2, 4, -1]]

def raw4239step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 3, -3], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw4240 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![1, -3, 1, 1], ![1, 3, -4, 0]]

def raw4240step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![3, 1, -4], ![-1, 1, 0]]

def raw4240step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 3, -3], ![-3, -1, 4], ![1, -1, 0]]

def raw4240step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]

def raw4241 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![2, -3, 1, 0], ![0, 3, -4, 1]]

def raw4241step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -3, 3], ![3, 1, -4], ![-1, 0, 1]]

def raw4241step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -2, 0], ![0, 3, -3], ![-3, -1, 4], ![1, 0, -1]]

def raw4241step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]

def raw4242 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![2, -2, 1, -1], ![0, 2, -4, 2]]

def raw4242step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![3, 1, -4], ![-1, -1, 2]]

def raw4242step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -2, 0], ![0, 2, -2], ![-3, -1, 4], ![1, 1, -2]]

def raw4242step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]

def raw4243 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, -2, 2, 0], ![0, 1, 1, -2], ![2, 0, 0, -2]]

def raw4243step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -2, 1, 0], ![-3, 2, 1, 0], ![4, 0, -2, -2]]

def raw4243step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -2, 1], ![0, 1, 2, -3], ![2, 0, 0, -2]]

def raw4244 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw4245 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw4246 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw4247 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw4248 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![2, -1, 0, -1]]

def raw4248step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -1, 1, -1], ![-3, 2, 1, 0], ![4, -1, -2, -1]]

def raw4248step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 2, 0, -3]]

def raw4249 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, -1, 2, -1], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw4249step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![-3, 2, 0, 1], ![4, -1, 0, -3]]

def raw4249step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -3, 4], ![0, 2, 1, -3], ![1, 0, 1, -2]]

def raw4250 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, -1, 2, -1], ![1, -1, 1, -1], ![1, 1, 0, -2]]

def raw4250step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![-3, 2, 1, 0], ![4, -1, -1, -2]]

def raw4250step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, 1, 0, -2]]

def raw4251 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, -1, 2, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw4251step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, 0, 0], ![-3, 2, 0, 1], ![4, -1, -1, -2]]

def raw4251step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, 1, 0, -2]]

def raw4252 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, -1, 2, -1], ![1, 0, 1, -2], ![1, 0, 0, -1]]

def raw4252step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, 0, 0], ![-3, 2, 1, 0], ![4, -1, -2, -1]]

def raw4252step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, 1, 0, -2]]

def raw4253 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw4254 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, -1, 3, -2], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw4254step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![-3, 3, 0, 0], ![4, -2, 0, -2]]

def raw4254step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 1, -1], ![3, -3, 0, 0], ![-4, 2, 0, 2]]

def raw4254step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -3, 3], ![0, 2, 2, -4], ![1, -1, 1, -1]]

def raw4255 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, -1, 3, -2], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw4255step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, 0, 0], ![-3, 3, 0, 0], ![4, -2, -1, -1]]

def raw4255step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, -1, 1], ![0, 0, 3, -3], ![1, 1, 0, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical133
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4256 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 1, -1]]

def raw4257 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, -2, 0, 0]]

def raw4258 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, -2, 0, 0]]

def raw4259 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw4260 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def raw4260step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-3, 1, 0, 2], ![4, -1, -1, -2]]

def raw4260step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 2, -3]]

def raw4261 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw4262 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, -2, 1, -1]]

def raw4262step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-3, 1, 1, 1], ![4, -1, -2, -1]]

def raw4262step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 1, 1, -3]]

def raw4263 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 1, -1], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw4264 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 1, -1], ![0, 1, 2, -3], ![2, -2, 0, 0]]

def raw4264step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-3, 1, 2, 0], ![4, -1, -3, 0]]

def raw4264step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -2, 1, 1], ![0, 2, 0, -2], ![1, 0, 2, -3]]

def raw4265 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 1, -1], ![1, -2, 1, 0], ![1, 1, 1, -3]]

def raw4265step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![-3, 1, 1, 1], ![4, -1, 0, -3]]

def raw4265step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 2, -1], ![3, -1, -1, -1], ![-4, 1, 0, 3]]

def raw4265step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, -1, 2], ![0, 2, -1, -1], ![1, 0, 3, -4]]

def raw4266 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 1, -1], ![1, -2, 2, -1], ![1, 1, 0, -2]]

def raw4266step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![-3, 1, 2, 0], ![4, -1, -1, -2]]

def raw4266step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 0, 2, -3]]

def raw4267 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 2, -2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 0, 0]]

def raw4267step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, -2, 0, 0]]

def raw4268 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, -2, 1, -1]]

def raw4268step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-3, 2, 0, 1], ![4, -2, -1, -1]]

def raw4268step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def raw4269 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw4270 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 2, -2], ![0, 1, 1, -2], ![2, -2, 0, 0]]

def raw4270step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-3, 2, 1, 0], ![4, -2, -2, 0]]

def raw4270step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -2, 1], ![2, 1, 0, -3]]

def raw4271 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 2, -2], ![1, -2, 1, 0], ![1, 1, 0, -2]]

def raw4271step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![-3, 2, 1, 0], ![4, -2, 0, -2]]

def raw4271step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, 0, 1, -3]]

def raw4272 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw4272step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![-3, 2, 0, 1], ![4, -2, 0, -2]]

def raw4272step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 1, 0], ![3, -2, 0, -1], ![-4, 2, 0, 2]]

def raw4272step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -2, 3], ![0, 2, 2, -4], ![1, 0, 0, -1]]

def raw4273 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 2, -2], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw4273step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![-3, 2, 1, 0], ![4, -2, -1, -1]]

def raw4273step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, 1, -2]]

def raw4274 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 2, -2], ![1, 0, 1, -2], ![1, -1, 0, 0]]

def raw4274step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, 0, -1], ![-3, 2, 1, 0], ![4, -2, -2, 0]]

def raw4274step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 0, 1], ![3, -2, -1, 0], ![-4, 2, 2, 0]]

def raw4274step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -2, 3], ![0, 2, 2, -4], ![1, 0, 0, -1]]

def raw4275 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 3, -3], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw4276 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 3, -3], ![0, 1, 0, -1], ![2, -2, 0, 0]]

def raw4276step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-3, 3, 0, 0], ![4, -3, -1, 0]]

def raw4276step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 3, -3], ![0, 2, 0, -2], ![1, -2, 0, 1]]

def raw4277 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 3, -3], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw4277step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![-3, 3, 0, 0], ![4, -3, 0, -1]]

def raw4277step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 1, 0], ![3, -3, 0, 0], ![-4, 3, 0, 1]]

def raw4277step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -3, 3], ![0, 1, 0, -1], ![1, 0, 3, -4]]

def raw4278 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 3, -3], ![1, 0, 0, -1], ![1, -1, 0, 0]]

def raw4278step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, 0, -1], ![-3, 3, 0, 0], ![4, -3, -1, 0]]

def raw4278step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 0, 1], ![3, -3, 0, 0], ![-4, 3, 1, 0]]

def raw4278step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -3, 3], ![0, 1, 0, -1], ![1, 0, 3, -4]]

def raw4279 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, 1, -2]]

def raw4279step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-3, 0, 2, 1], ![4, -1, -1, -2]]

def raw4279step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, 1, -2], ![0, 1, 2, -3], ![1, 0, -2, 1]]

def raw4280 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def raw4280step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-3, 0, 3, 0], ![4, -1, -2, -1]]

def raw4280step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, 0, 1, -2]]

def raw4281 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def raw4281step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![-3, 0, 0, 3], ![4, -1, 0, -3]]

def raw4281step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 3, -3], ![0, 1, 1, -2], ![1, -1, -1, 1]]

def raw4282 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def raw4282step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![-3, 0, 1, 2], ![4, -1, -1, -2]]

def raw4282step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 1, 1, -2], ![0, 1, 2, -3], ![1, -1, -1, 1]]

def raw4283 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw4283step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-3, 1, 2, 0], ![4, -2, -1, -1]]

def raw4283step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, 0, 1, -2]]

def raw4284 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw4284step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![-3, 1, 0, 2], ![4, -2, 0, -2]]

def raw4284step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 1, 1], ![3, -1, 0, -2], ![-4, 2, 0, 2]]

def raw4284step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, -2, 3], ![0, 2, 2, -4], ![1, -1, 1, -1]]

def raw4285 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, -1, 1, -1]]

def raw4285step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![-3, 1, 1, 1], ![4, -2, -1, -1]]

def raw4285step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 1, 1, -3]]

def raw4286 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw4286step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![-3, 2, 0, 1], ![4, -3, 0, -1]]

def raw4286step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 1, 1], ![3, -2, 0, -1], ![-4, 3, 0, 1]]

def raw4286step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -2, 3], ![0, 1, 3, -4], ![1, 1, -1, -1]]

def raw4287 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 1, 2, -3], ![1, -1, 1, -1], ![1, -1, 0, 0]]

def raw4287step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![-3, 2, 1, 0], ![4, -3, -1, 0]]

def raw4287step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 1, 1], ![3, -2, -1, 0], ![-4, 3, 1, 0]]

def raw4287step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -2, 3], ![0, 1, 3, -4], ![1, 1, -1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical134
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4288 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw4288step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![-3, 3, 0, 0], ![4, -4, 0, 0]]

def raw4288step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 1, 1], ![3, -3, 0, 0], ![-4, 4, 0, 0]]

def raw4288step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -3, 3], ![0, 0, 4, -4], ![1, 1, -1, -1]]

def raw4289 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![1, -2, 2, -1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw4289step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -2, 1, 0], ![-3, 2, 1, 0], ![4, -1, -2, -1]]

def raw4289step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, 0, 1, -2]]

def raw4290 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![1, -1, 2, -2], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw4290step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -1, 1, -1], ![-3, 2, 1, 0], ![4, -2, -2, 0]]

def raw4290step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![-1, 1, -1, 1], ![3, -2, -1, 0], ![-4, 2, 2, 0]]

def raw4290step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, -2, 3], ![0, 2, 2, -4], ![1, -1, 1, -1]]

def raw4291 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -2, 1, 1], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw4291step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -2, 0, 1], ![-2, 1, -1, 2], ![3, 1, 0, -4]]

def raw4291step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 2, 0, -1], ![2, -1, 1, -2], ![-3, -1, 0, 4]]

def raw4291step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 4, -3], ![0, 2, -1, -1], ![1, -1, -2, 2]]

def raw4292 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -2, 2, 0], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def raw4292step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -2, 1, 0], ![-2, 2, 1, -1], ![3, 0, -2, -1]]

def raw4292step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, 0, -2], ![1, -1, 2, -2], ![1, 0, -2, 1]]

def raw4293 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -2, 2, 0], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def raw4293step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -2, 0, 1], ![-2, 2, 1, -1], ![3, 0, -2, -1]]

def raw4293step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![1, -1, 2, -2], ![1, 1, 0, -2]]

def raw4294 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 0, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw4294step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 1, -3]]

def raw4295 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 0, 1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 1, 0, -2]]

def raw4295step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def raw4296 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 0, 1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw4296step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, 0, -2]]

def raw4297 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw4297step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw4298 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw4299 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 1, 0], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw4300 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 1, 0], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw4300step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![-2, 1, 0, 1], ![3, 0, 0, -3]]

def raw4300step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -3, 3], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw4301 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 1, 0], ![1, -1, 1, -1], ![1, 1, 0, -2]]

def raw4301step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![-2, 1, 1, 0], ![3, 0, -1, -2]]

def raw4301step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 1, -1], ![2, -1, -1, 0], ![-3, 0, 1, 2]]

def raw4301step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, 2, -3], ![1, 1, -1, -1]]

def raw4302 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw4303 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 0, 0, 0], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw4303step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![1, -1, 0, -1, 1], ![-2, 2, 0, 0, 0], ![3, -1, 0, 0, -2]]

def raw4303step1 : Matrix (Fin 4) (Fin 5) ℤ := ![![2, 0, 0, -1, -1], ![-1, 1, 0, 1, -1], ![2, -2, 0, 0, 0], ![-3, 1, 0, 0, 2]]

def raw4303step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 1, -1], ![2, -2, 0, 0], ![-3, 1, 0, 2]]

def raw4303step3 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -1, 1, -1]]

def raw4304 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -1, 0, -1]]

def raw4305 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, 1, 0, -2]]

def raw4306 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw4307 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw4308 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw4309 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![2, -1, 1, -2]]

def raw4309step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -1, 1, -1], ![-2, 2, -1, 1], ![3, -1, 0, -2]]

def raw4309step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 1, -1, 1], ![2, -2, 1, -1], ![-3, 1, 0, 2]]

def raw4309step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, 0, -2, 2], ![0, 1, 2, -3], ![1, -2, -1, 2]]

def raw4310 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 1, -2]]

def raw4311 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw4311step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw4312 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw4313 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![2, -1, 0, -1]]

def raw4313step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -1, 1, -1], ![-2, 2, 0, 0], ![3, -1, -1, -1]]

def raw4313step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -1, 1]]

def raw4314 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw4315 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw4316 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 1, 1, -2], ![2, -1, -1, 0]]

def raw4316step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -1, 1, -1], ![-2, 2, 1, -1], ![3, -1, -2, 0]]

def raw4316step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 2, -1, -2]]

def raw4317 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![1, -1, -1, 1], ![1, 1, 1, -3]]

def raw4318 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw4318step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![-2, 2, 0, 0], ![3, -1, 0, -2]]

def raw4318step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 1, -1], ![2, -2, 0, 0], ![-3, 1, 0, 2]]

def raw4318step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -1, 1, -1]]

def raw4319 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw4319step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![-2, 2, 1, -1], ![3, -1, -1, -1]]

def raw4319step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 1, -1], ![2, -2, -1, 1], ![-3, 1, 1, 1]]

def raw4319step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![1, 1, -1, -1], ![1, 1, 1, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical135
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4320 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw4320step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, 0, 0], ![-2, 2, -1, 1], ![3, -1, 0, -2]]

def raw4320step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 0, 0], ![2, -2, 1, -1], ![-3, 1, 0, 2]]

def raw4320step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, -2, 2]]

def raw4321 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw4321step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, 0, 0], ![-2, 2, 0, 0], ![3, -1, -1, -1]]

def raw4321step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, 0, -2]]

def raw4322 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![1, 0, 1, -2], ![1, 0, -1, 0]]

def raw4322step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, 0, 0], ![-2, 2, 1, -1], ![3, -1, -2, 0]]

def raw4322step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 0, 0], ![2, -2, -1, 1], ![-3, 1, 2, 0]]

def raw4322step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, -2, 2]]

def raw4323 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![1, 1, 1, -3], ![1, -1, -1, 1]]

def raw4323step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![1, -1, -1, 1], ![1, 1, 1, -3]]

def raw4324 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 3, -2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw4325 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 3, -2], ![0, 1, -1, 0], ![2, -1, 0, -1]]

def raw4325step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -1, 1, -1], ![-2, 3, -1, 0], ![3, -2, 0, -1]]

def raw4325step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 3, -2], ![0, -1, -2, 3], ![0, 2, 0, -2], ![1, -1, -1, 1]]

def raw4326 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw4327 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw4328 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 3, -2], ![1, -1, -1, 1], ![1, 1, 0, -2]]

def raw4329 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 3, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw4329step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![-2, 3, 0, -1], ![3, -2, 0, -1]]

def raw4329step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 1, -1], ![2, -3, 0, 1], ![-3, 2, 0, 1]]

def raw4329step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -3, 2], ![0, 1, 2, -3], ![1, -1, 1, -1]]

def raw4330 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 3, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw4330step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, 0, 0], ![-2, 3, -1, 0], ![3, -2, 0, -1]]

def raw4330step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 0, 0], ![2, -3, 1, 0], ![-3, 2, 0, 1]]

def raw4330step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -3, 2], ![1, 0, 2, -3]]

def raw4331 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 3, -2], ![1, 0, 0, -1], ![1, 0, -1, 0]]

def raw4331step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, 0, 0], ![-2, 3, 0, -1], ![3, -2, -1, 0]]

def raw4331step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 0, 0], ![2, -3, 0, 1], ![-3, 2, 1, 0]]

def raw4331step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -3, 2], ![1, 0, 2, -3]]

def raw4332 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, -1, 1], ![0, -1, 2, -1], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw4332step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw4333 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, -1, 1], ![0, -1, 2, -1], ![1, -1, 1, -1], ![1, 1, 0, -2]]

def raw4333step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 0, -1, 1], ![1, -1, 1, -1], ![1, 1, 0, -2]]

def raw4334 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, -1, 1], ![0, -1, 3, -2], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw4334step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 3, -2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw4335 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def raw4336 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -2, 1, 0], ![1, 1, 1, -3]]

def raw4337 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -2, 2, -1], ![1, 1, 0, -2]]

def raw4338 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw4338step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 2, -3], ![1, -2, -2, 3]]

def raw4339 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def raw4339step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -2, -2, 3]]

def raw4340 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, -2, 1, 0], ![1, 1, 0, -2]]

def raw4341 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw4341step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -2, -2, 3]]

def raw4342 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw4343 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, -1, 1], ![0, 1, 3, -4], ![2, -2, 0, 0]]

def raw4343step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-2, -1, 3, 0], ![3, 1, -4, 0]]

def raw4343step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 0, -1, 2], ![2, 1, -3, 0], ![-3, -1, 4, 0]]

def raw4343step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -2, 2, 0], ![0, 2, -1, -1], ![1, 0, 2, -3]]

def raw4344 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, -1, 1], ![1, -2, 1, 0], ![1, 1, 2, -4]]

def raw4344step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![-2, -1, 1, 2], ![3, 1, 0, -4]]

def raw4344step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 2, -1], ![2, 1, -1, -2], ![-3, -1, 0, 4]]

def raw4344step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, -1, 2, -2]]

def raw4345 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, -1, 1], ![1, -2, 2, -1], ![1, 1, 1, -3]]

def raw4345step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![-2, -1, 2, 1], ![3, 1, -1, -3]]

def raw4345step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 2, -2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -3, -1, 3]]

def raw4346 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 0, 0], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw4346step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![1, 0, 1, -2, 0], ![-2, 0, 0, 2, 0], ![3, 0, -1, -1, -1]]

def raw4346step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-2, 0, 2, 0], ![3, -1, -1, -1]]

def raw4346step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 1, -2]]

def raw4347 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 0, 0], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def raw4347step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-2, 0, 0, 2], ![3, 0, -1, -2]]

def raw4347step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 1, -2], ![-2, 0, 2], ![3, -1, -2]]

def raw4347step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![0, 2, -2], ![1, -2, 1]]

def raw4348 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 0, 0], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw4348step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![1, 0, 1, -1, -1], ![-2, 0, 1, 0, 1], ![3, 0, -2, 0, -1]]

def raw4348step1 : Matrix (Fin 4) (Fin 5) ℤ := ![![2, 0, 0, -1, -1], ![-1, 0, -1, 1, 1], ![2, 0, -1, 0, -1], ![-3, 0, 2, 0, 1]]

def raw4348step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 1, 1], ![2, -1, 0, -1], ![-3, 2, 0, 1]]

def raw4348step3 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, 2, -3], ![1, 1, -1, -1]]

def raw4349 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 0, 0], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw4349step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![1, 0, 1, -1, -1], ![-2, 0, 2, 0, 0], ![3, 0, -3, 0, 0]]

def raw4349step1 : Matrix (Fin 4) (Fin 5) ℤ := ![![2, 0, 0, -1, -1], ![-1, 0, -1, 1, 1], ![2, 0, -2, 0, 0], ![-3, 0, 3, 0, 0]]

def raw4349step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 1, 1], ![2, -2, 0, 0], ![-3, 3, 0, 0]]

def raw4349step3 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 0, 3, -3], ![1, 1, -1, -1]]

def raw4350 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 0, 0], ![1, -2, 1, 0], ![1, 1, 1, -3]]

def raw4350step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![-2, 0, 1, 1], ![3, 0, 0, -3]]

def raw4350step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![-2, 1, 1], ![3, 0, -3]]

def raw4350step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 1, -2], ![1, 1, -2]]

def raw4351 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 0, 0], ![1, -2, 2, -1], ![1, 1, 0, -2]]

def raw4351step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![-2, 0, 2, 0], ![3, 0, -1, -2]]

def raw4351step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![-2, 2, 0], ![3, -1, -2]]

def raw4351step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical136
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4352 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, -1, 1, 0], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw4352step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw4353 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, -1, 2, -1], ![0, 1, -1, 0], ![2, -1, 0, -1]]

def raw4353step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -1, 0, -1]]

def raw4354 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, -1, 2, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw4354step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw4355 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 0, 0], ![2, -1, 0, -1]]

def raw4355step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![1, 0, 0, 0, -1], ![-2, 1, 1, 0, 0], ![3, -1, -1, 0, -1]]

def raw4355step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 0, -1], ![-2, 1, 1, 0], ![3, -1, -1, -1]]

def raw4355step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, 0, -2]]

def raw4356 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -2, 1, -1]]

def raw4357 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 0, 0]]

def raw4357step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw4358 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, -2, -1, 1]]

def raw4359 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -2, 1, 0], ![1, 1, -1, -1]]

def raw4360 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw4360step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -2, 3]]

def raw4361 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw4361step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -2, 3, -2]]

def raw4362 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -2, 0, 0]]

def raw4363 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, -2, -1, 1]]

def raw4364 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, -2, 0, 1], ![1, 1, -1, -1]]

def raw4365 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw4365step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -2, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -2, 3, -2]]

def raw4366 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw4367 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 2, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Tao_TaoArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact arithmetic in `ℤ[ω]`, interpreted in the same complex root as Tao's
matrix.  These definitions are for certificate checking, not assumptions. -/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6.TaoArithmetic

abbrev Coeff := ℤ × ℤ

end MUB6.TaoArithmetic

end

end OAI
end


