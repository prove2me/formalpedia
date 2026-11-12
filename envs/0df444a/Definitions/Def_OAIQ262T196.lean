-- Prove2me | Definitions.Def_OAIQ262T196
-- name    : OAIQ262T196
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T18:28:44.753204+00:00
-- url     : https://prove2.me/theorems/098dd4fe-8d04-4008-b124-c5ec1fdff3ab
-- title:
--   Definitions bundle OAIQ262T196 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 21 declarations of OpenAI's Lean: 21 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Taylor_TaylorRows00`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorRows00.lean), [`Triangular_Taylor_TaylorSpectrum`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorSpectrum.lean).
--
--   **Imports.** It imports the bundles `OAIQ262T155` and `OAIQ262T161` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ262T261`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ262T155
import Definitions.Def_OAIQ262T161

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma spectrum1_1_2_calc (r : Fin 8) : spectrumBox 1 1 2 r = spectrum1_1_2 r := by
  revert r
  decide +kernel
lemma spectrum1_1_3_calc (r : Fin 8) : spectrumBox 1 1 3 r = spectrum1_1_3 r := by
  revert r
  decide +kernel
lemma spectrum1_1_4_calc (r : Fin 8) : spectrumBox 1 1 4 r = spectrum1_1_4 r := by
  revert r
  decide +kernel
lemma spectrum1_1_5_calc (r : Fin 8) : spectrumBox 1 1 5 r = spectrum1_1_5 r := by
  revert r
  decide +kernel
lemma spectrum1_1_6_calc (r : Fin 8) : spectrumBox 1 1 6 r = spectrum1_1_6 r := by
  revert r
  decide +kernel
lemma spectrum1_1_7_calc (r : Fin 8) : spectrumBox 1 1 7 r = spectrum1_1_7 r := by
  revert r
  decide +kernel
lemma spectrum1_1_8_calc (r : Fin 8) : spectrumBox 1 1 8 r = spectrum1_1_8 r := by
  revert r
  decide +kernel
lemma spectrum1_1_9_calc (r : Fin 8) : spectrumBox 1 1 9 r = spectrum1_1_9 r := by
  revert r
  decide +kernel
lemma spectrum1_1_27_calc (r : Fin 8) : spectrumBox 1 1 27 r = spectrum1_1_27 r := by
  revert r
  decide +kernel
lemma spectrum1_1_28_calc (r : Fin 8) : spectrumBox 1 1 28 r = spectrum1_1_28 r := by
  revert r
  decide +kernel
lemma spectrum1_1_29_calc (r : Fin 8) : spectrumBox 1 1 29 r = spectrum1_1_29 r := by
  revert r
  decide +kernel
lemma spectrum1_1_30_calc (r : Fin 8) : spectrumBox 1 1 30 r = spectrum1_1_30 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorRows00
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma tr0_0_1_0_calc (r : Fin 8) : taylorRowBox 0 0 1 0 r = tr0_0_1_0 r := by
  revert r
  decide +kernel
lemma tr0_0_1_10_calc (r : Fin 8) : taylorRowBox 0 0 1 10 r = tr0_0_1_10 r := by
  revert r
  decide +kernel
lemma tr0_0_1_11_calc (r : Fin 8) : taylorRowBox 0 0 1 11 r = tr0_0_1_11 r := by
  revert r
  decide +kernel
lemma tr0_0_1_12_calc (r : Fin 8) : taylorRowBox 0 0 1 12 r = tr0_0_1_12 r := by
  revert r
  decide +kernel
lemma tr0_0_1_13_calc (r : Fin 8) : taylorRowBox 0 0 1 13 r = tr0_0_1_13 r := by
  revert r
  decide +kernel
lemma tr0_0_1_14_calc (r : Fin 8) : taylorRowBox 0 0 1 14 r = tr0_0_1_14 r := by
  revert r
  decide +kernel
lemma tr0_0_1_15_calc (r : Fin 8) : taylorRowBox 0 0 1 15 r = tr0_0_1_15 r := by
  revert r
  decide +kernel
lemma tr0_0_1_16_calc (r : Fin 8) : taylorRowBox 0 0 1 16 r = tr0_0_1_16 r := by
  revert r
  decide +kernel
lemma tr0_0_1_17_calc (r : Fin 8) : taylorRowBox 0 0 1 17 r = tr0_0_1_17 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end


