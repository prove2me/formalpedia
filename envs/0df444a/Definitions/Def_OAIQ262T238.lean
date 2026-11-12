-- Prove2me | Definitions.Def_OAIQ262T238
-- name    : OAIQ262T238
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T18:56:24.490143+00:00
-- url     : https://prove2.me/theorems/61bd6e8d-5288-487a-a267-74a8079026a5
-- title:
--   Definitions bundle OAIQ262T238 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 10 declarations of OpenAI's Lean: 10 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Taylor_TaylorRows13`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorRows13.lean).
--
--   **Imports.** It imports the bundles `OAIQ262T074`, `OAIQ262T075` and `OAIQ262T161` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ262T264`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ262T074
import Definitions.Def_OAIQ262T075
import Definitions.Def_OAIQ262T161

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorRows13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma tr1_3_0_7_calc (r : Fin 8) : taylorRowBox 1 3 0 7 r = tr1_3_0_7 r := by
  revert r
  decide +kernel
lemma tr1_3_0_8_calc (r : Fin 8) : taylorRowBox 1 3 0 8 r = tr1_3_0_8 r := by
  revert r
  decide +kernel
lemma tr1_3_0_9_calc (r : Fin 8) : taylorRowBox 1 3 0 9 r = tr1_3_0_9 r := by
  revert r
  decide +kernel
lemma tr1_3_1_0_calc (r : Fin 8) : taylorRowBox 1 3 1 0 r = tr1_3_1_0 r := by
  revert r
  decide +kernel
lemma tr1_3_1_10_calc (r : Fin 8) : taylorRowBox 1 3 1 10 r = tr1_3_1_10 r := by
  revert r
  decide +kernel
lemma tr1_3_1_11_calc (r : Fin 8) : taylorRowBox 1 3 1 11 r = tr1_3_1_11 r := by
  revert r
  decide +kernel
lemma tr1_3_1_12_calc (r : Fin 8) : taylorRowBox 1 3 1 12 r = tr1_3_1_12 r := by
  revert r
  decide +kernel
lemma tr1_3_1_13_calc (r : Fin 8) : taylorRowBox 1 3 1 13 r = tr1_3_1_13 r := by
  revert r
  decide +kernel
lemma tr1_3_1_14_calc (r : Fin 8) : taylorRowBox 1 3 1 14 r = tr1_3_1_14 r := by
  revert r
  decide +kernel
lemma tr1_3_1_15_calc (r : Fin 8) : taylorRowBox 1 3 1 15 r = tr1_3_1_15 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end


