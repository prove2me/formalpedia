-- Prove2me | Definitions.Def_OAIQ262T248
-- name    : OAIQ262T248
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T18:52:04.969392+00:00
-- url     : https://prove2.me/theorems/21315990-fc09-4217-8e2d-5b8e6f150ee9
-- title:
--   Definitions bundle OAIQ262T248 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 11 declarations of OpenAI's Lean: 11 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Taylor_TaylorRows15`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorRows15.lean), [`Triangular_Taylor_TaylorRows16`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorRows16.lean).
--
--   **Imports.** It imports the bundle `OAIQ262T161` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ262T264`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ262T161

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorRows15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma tr1_5_1_8_calc (r : Fin 8) : taylorRowBox 1 5 1 8 r = tr1_5_1_8 r := by
  revert r
  decide +kernel
lemma tr1_5_1_9_calc (r : Fin 8) : taylorRowBox 1 5 1 9 r = tr1_5_1_9 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorRows16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma tr1_6_0_0_calc (r : Fin 8) : taylorRowBox 1 6 0 0 r = tr1_6_0_0 r := by
  revert r
  decide +kernel
lemma tr1_6_0_10_calc (r : Fin 8) : taylorRowBox 1 6 0 10 r = tr1_6_0_10 r := by
  revert r
  decide +kernel
lemma tr1_6_0_11_calc (r : Fin 8) : taylorRowBox 1 6 0 11 r = tr1_6_0_11 r := by
  revert r
  decide +kernel
lemma tr1_6_0_12_calc (r : Fin 8) : taylorRowBox 1 6 0 12 r = tr1_6_0_12 r := by
  revert r
  decide +kernel
lemma tr1_6_0_13_calc (r : Fin 8) : taylorRowBox 1 6 0 13 r = tr1_6_0_13 r := by
  revert r
  decide +kernel
lemma tr1_6_0_14_calc (r : Fin 8) : taylorRowBox 1 6 0 14 r = tr1_6_0_14 r := by
  revert r
  decide +kernel
lemma tr1_6_0_15_calc (r : Fin 8) : taylorRowBox 1 6 0 15 r = tr1_6_0_15 r := by
  revert r
  decide +kernel
lemma tr1_6_0_16_calc (r : Fin 8) : taylorRowBox 1 6 0 16 r = tr1_6_0_16 r := by
  revert r
  decide +kernel
lemma tr1_6_0_17_calc (r : Fin 8) : taylorRowBox 1 6 0 17 r = tr1_6_0_17 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end


