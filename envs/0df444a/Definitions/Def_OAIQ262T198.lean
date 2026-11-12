-- Prove2me | Definitions.Def_OAIQ262T198
-- name    : OAIQ262T198
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T18:40:06.63655+00:00
-- url     : https://prove2.me/theorems/e52b39fc-05a7-4b03-bf23-a235cadc7bc1
-- title:
--   Definitions bundle OAIQ262T198 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 12 declarations of OpenAI's Lean: 12 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Taylor_TaylorRows00`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorRows00.lean), [`Triangular_Taylor_TaylorRows06`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorRows06.lean).
--
--   **Imports.** It imports the bundles `OAIQ262T046`, `OAIQ262T062` and `OAIQ262T161` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ262T262`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ262T046
import Definitions.Def_OAIQ262T062
import Definitions.Def_OAIQ262T161

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

lemma tr0_0_0_0_calc (r : Fin 8) : taylorRowBox 0 0 0 0 r = tr0_0_0_0 r := by
  revert r
  decide +kernel
lemma tr0_0_0_10_calc (r : Fin 8) : taylorRowBox 0 0 0 10 r = tr0_0_0_10 r := by
  revert r
  decide +kernel
lemma tr0_0_0_11_calc (r : Fin 8) : taylorRowBox 0 0 0 11 r = tr0_0_0_11 r := by
  revert r
  decide +kernel
lemma tr0_0_0_12_calc (r : Fin 8) : taylorRowBox 0 0 0 12 r = tr0_0_0_12 r := by
  revert r
  decide +kernel
lemma tr0_0_0_13_calc (r : Fin 8) : taylorRowBox 0 0 0 13 r = tr0_0_0_13 r := by
  revert r
  decide +kernel
lemma tr0_0_0_14_calc (r : Fin 8) : taylorRowBox 0 0 0 14 r = tr0_0_0_14 r := by
  revert r
  decide +kernel
lemma tr0_0_0_15_calc (r : Fin 8) : taylorRowBox 0 0 0 15 r = tr0_0_0_15 r := by
  revert r
  decide +kernel
lemma tr0_0_0_16_calc (r : Fin 8) : taylorRowBox 0 0 0 16 r = tr0_0_0_16 r := by
  revert r
  decide +kernel
lemma tr0_0_0_17_calc (r : Fin 8) : taylorRowBox 0 0 0 17 r = tr0_0_0_17 r := by
  revert r
  decide +kernel
lemma tr0_0_0_18_calc (r : Fin 8) : taylorRowBox 0 0 0 18 r = tr0_0_0_18 r := by
  revert r
  decide +kernel
lemma tr0_0_1_9_calc (r : Fin 8) : taylorRowBox 0 0 1 9 r = tr0_0_1_9 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

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

lemma tr0_6_0_19_calc (r : Fin 8) : taylorRowBox 0 6 0 19 r = tr0_6_0_19 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end


