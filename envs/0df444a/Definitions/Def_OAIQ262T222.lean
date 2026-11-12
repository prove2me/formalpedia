-- Prove2me | Definitions.Def_OAIQ262T222
-- name    : OAIQ262T222
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T18:48:26.262578+00:00
-- url     : https://prove2.me/theorems/8e2d26f2-6834-470d-897a-d5b6cba2ef94
-- title:
--   Definitions bundle OAIQ262T222 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 11 declarations of OpenAI's Lean: 11 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Taylor_TaylorRows06`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorRows06.lean), [`Triangular_Taylor_TaylorRows15`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorRows15.lean).
--
--   **Imports.** It imports the bundles `OAIQ262T063`, `OAIQ262T064` and `OAIQ262T161` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ262T263` and `OAIQ262T264`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ262T063
import Definitions.Def_OAIQ262T064
import Definitions.Def_OAIQ262T161

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorRows06
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma tr0_6_1_0_calc (r : Fin 8) : taylorRowBox 0 6 1 0 r = tr0_6_1_0 r := by
  revert r
  decide +kernel
lemma tr0_6_1_10_calc (r : Fin 8) : taylorRowBox 0 6 1 10 r = tr0_6_1_10 r := by
  revert r
  decide +kernel
lemma tr0_6_1_11_calc (r : Fin 8) : taylorRowBox 0 6 1 11 r = tr0_6_1_11 r := by
  revert r
  decide +kernel
lemma tr0_6_1_12_calc (r : Fin 8) : taylorRowBox 0 6 1 12 r = tr0_6_1_12 r := by
  revert r
  decide +kernel
lemma tr0_6_1_13_calc (r : Fin 8) : taylorRowBox 0 6 1 13 r = tr0_6_1_13 r := by
  revert r
  decide +kernel
lemma tr0_6_1_14_calc (r : Fin 8) : taylorRowBox 0 6 1 14 r = tr0_6_1_14 r := by
  revert r
  decide +kernel
lemma tr0_6_1_15_calc (r : Fin 8) : taylorRowBox 0 6 1 15 r = tr0_6_1_15 r := by
  revert r
  decide +kernel
lemma tr0_6_1_16_calc (r : Fin 8) : taylorRowBox 0 6 1 16 r = tr0_6_1_16 r := by
  revert r
  decide +kernel
lemma tr0_6_1_17_calc (r : Fin 8) : taylorRowBox 0 6 1 17 r = tr0_6_1_17 r := by
  revert r
  decide +kernel
lemma tr0_6_1_18_calc (r : Fin 8) : taylorRowBox 0 6 1 18 r = tr0_6_1_18 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

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

lemma tr1_5_1_20_calc (r : Fin 8) : taylorRowBox 1 5 1 20 r = tr1_5_1_20 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end


