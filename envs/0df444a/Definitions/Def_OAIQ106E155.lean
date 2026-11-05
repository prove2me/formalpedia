-- Prove2me | Definitions.Def_OAIQ106E155
-- name    : OAIQ106E155
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T19:39:56.899508+00:00
-- url     : https://prove2.me/theorems/9da0956c-4c78-4b77-969d-d0d5fc577fc7
-- title:
--   Definitions bundle OAIQ106E155 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 7 declarations of OpenAI's Lean: 5 definitions and 2 theorems. The definitions and types are `OAI.MUB6.TaoArithmetic.conjugate`, `OAI.MUB6.TaoArithmetic.counts`, `OAI.MUB6.TaoArithmetic.mul`, `OAI.MUB6.TaoArithmetic.root`, `OAI.MUB6.TaoArithmetic.value`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_Tao_TaoArithmetic`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/Tao/TaoArithmetic.lean).
--
--   **Imports.** It imports the published bundle `Def_MUBSix`; the bundle `OAIQ106E107` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ106E156`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E107

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

def value (z : Coeff) : ℂ := (z.1 : ℂ) + (z.2 : ℂ) * omega

def mul (z w : Coeff) : Coeff :=
  (z.1 * w.1 - z.2 * w.2, z.1 * w.2 + z.2 * w.1 - z.2 * w.2)

def conjugate (z : Coeff) : Coeff := (z.1 - z.2, -z.2)

def root (n : ℤ) : Coeff :=
  if n % 3 = 0 then (1, 0) else if n % 3 = 1 then (0, 1) else (-1, -1)

@[simp] theorem value_zero : value 0 = 0 := by simp [value]

@[simp] theorem value_add (z w : Coeff) : value (z + w) = value z + value w := by
  simp [value]
  ring

def counts (a : Charge) : Coeff :=
  ∑ k, root (∑ i, (taoExponent i k : ℤ) * a i)

end MUB6.TaoArithmetic

end

end OAI
end


