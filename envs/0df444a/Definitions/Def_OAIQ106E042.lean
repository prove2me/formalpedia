-- Prove2me | Definitions.Def_OAIQ106E042
-- name    : OAIQ106E042
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-06T01:04:10.518462+00:00
-- url     : https://prove2.me/theorems/a6091984-664a-4b59-ae40-55d8f81c0c9a
-- title:
--   Definitions bundle OAIQ106E042 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 7 declarations of OpenAI's Lean: 7 definitions. The definitions and types are `OAI.MUB6.Certificate.GramNonnegative.quadratic0`, `OAI.MUB6.Certificate.GramNonnegative.quadratic1`, `OAI.MUB6.Certificate.GramNonnegative.quadratic2`, `OAI.MUB6.Certificate.GramNonnegative.quadratic3`, `OAI.MUB6.Certificate.GramNonnegative.quadratic4`, `OAI.MUB6.Certificate.GramNonnegative.quadratic5`, `OAI.MUB6.Certificate.GramNonnegative.sourceGram`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_Certificate_GramNonnegative`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/Certificate/GramNonnegative.lean).
--
--   **Imports.** It imports the published bundle `Def_MUBSix`; the bundles `OAIQ106E002` and `OAIQ106E018` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.MUB6.Certificate.GramAssembly.Block0.polynomial_interpretation_e`, `OAI.MUB6.Certificate.GramAssembly.Block1.polynomial_interpretation_e`, `OAI.MUB6.Certificate.GramAssembly.Block2.polynomial_interpretation_e`, `OAI.MUB6.Certificate.GramAssembly.Block3.polynomial_interpretation_e`, `OAI.MUB6.Certificate.GramAssembly.Block4.polynomial_interpretation_e`, `OAI.MUB6.Certificate.GramAssembly.interpretation_e`, `OAI.MUB6.Certificate.GramNonnegative.quadratic1_nonneg_e`, `OAI.MUB6.Certificate.GramNonnegative.sourceGram_nonneg_e` and `OAI.MUB6.Certificate.MixedData.false_of_gram_interpretation_e`; the proofs of `OAI.MUB6.Certificate.GramAssembly.Block0.polynomial_interpretation_e`, `OAI.MUB6.Certificate.GramAssembly.Block1.polynomial_interpretation_e`, `OAI.MUB6.Certificate.GramAssembly.Block2.polynomial_interpretation_e`, `OAI.MUB6.Certificate.GramAssembly.Block3.polynomial_interpretation_e`, `OAI.MUB6.Certificate.GramAssembly.Block4.polynomial_interpretation_e`, `OAI.MUB6.Certificate.GramAssembly.interpretation_e`, `OAI.MUB6.Certificate.GramNonnegative.quadratic1_nonneg_e`, `OAI.MUB6.Certificate.GramNonnegative.sourceGram_nonneg_e`, `OAI.MUB6.Certificate.MixedData.false_of_gram_interpretation_e` and `OAI.MUB6.family_size_le_five_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E018

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_GramNonnegative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nonnegativity of the six literal integer Gram forms and the exact
positive scaling used by the mixed certificate. -/

noncomputable section
open scoped BigOperators

namespace MUB6.Certificate.GramNonnegative

def quadratic0 (B : Fin 7 → Basis) : ℝ :=
  ∑ i, ∑ j, realMatrix GramData.Block0.Z i j *
    (GramFunctions.Block0.forms i).mixedGram (GramFunctions.Block0.forms j) B

def quadratic1 (B : Fin 7 → Basis) : ℝ :=
  ∑ i, ∑ j, realMatrix GramData.Block1.Z i j *
    (GramFunctions.Block1.forms i).mixedGram (GramFunctions.Block1.forms j) B

def quadratic2 (B : Fin 7 → Basis) : ℝ :=
  ∑ i, ∑ j, realMatrix GramData.Block2.Z i j *
    (GramFunctions.Block2.forms i).mixedGram (GramFunctions.Block2.forms j) B

def quadratic3 (B : Fin 7 → Basis) : ℝ :=
  ∑ i, ∑ j, realMatrix GramData.Block3.Z i j *
    (GramFunctions.Block3.forms i).mixedGram (GramFunctions.Block3.forms j) B

def quadratic4 (B : Fin 7 → Basis) : ℝ :=
  ∑ i, ∑ j, realMatrix GramData.Block4.Z i j *
    (GramFunctions.Block4.forms i).mixedGram (GramFunctions.Block4.forms j) B

def quadratic5 (B : Fin 7 → Basis) : ℝ :=
  ∑ i, ∑ j, realMatrix GramData.Block5.Z i j *
    (GramFunctions.Block5.forms i).mixedGram (GramFunctions.Block5.forms j) B

def sourceGram (B : Fin 7 → Basis) : ℝ :=
  5 * ((10 : ℝ) ^ (15 - GramFunctions.Block0.decimalExponent) * quadratic0 B +
    (10 : ℝ) ^ (15 - GramFunctions.Block1.decimalExponent) * quadratic1 B +
    (10 : ℝ) ^ (15 - GramFunctions.Block2.decimalExponent) * quadratic2 B +
    (10 : ℝ) ^ (15 - GramFunctions.Block3.decimalExponent) * quadratic3 B +
    (10 : ℝ) ^ (15 - GramFunctions.Block4.decimalExponent) * quadratic4 B +
    (10 : ℝ) ^ (15 - GramFunctions.Block5.decimalExponent) * quadratic5 B)

end MUB6.Certificate.GramNonnegative

end

end OAI
end


