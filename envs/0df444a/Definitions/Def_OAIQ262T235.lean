-- Prove2me | Definitions.Def_OAIQ262T235
-- name    : OAIQ262T235
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T18:46:39.540621+00:00
-- url     : https://prove2.me/theorems/d875a69f-aa69-4a42-8ca3-c473c35c4388
-- title:
--   Definitions bundle OAIQ262T235 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 10 declarations of OpenAI's Lean: 10 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Taylor_TaylorRows12`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorRows12.lean).
--
--   **Imports.** It imports the bundles `OAIQ262T072`, `OAIQ262T073` and `OAIQ262T161` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ262T264`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ262T072
import Definitions.Def_OAIQ262T073
import Definitions.Def_OAIQ262T161

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorRows12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma tr1_2_1_1_calc (r : Fin 8) : taylorRowBox 1 2 1 1 r = tr1_2_1_1 r := by
  revert r
  decide +kernel
lemma tr1_2_1_2_calc (r : Fin 8) : taylorRowBox 1 2 1 2 r = tr1_2_1_2 r := by
  revert r
  decide +kernel
lemma tr1_2_1_3_calc (r : Fin 8) : taylorRowBox 1 2 1 3 r = tr1_2_1_3 r := by
  revert r
  decide +kernel
lemma tr1_2_1_4_calc (r : Fin 8) : taylorRowBox 1 2 1 4 r = tr1_2_1_4 r := by
  revert r
  decide +kernel
lemma tr1_2_1_5_calc (r : Fin 8) : taylorRowBox 1 2 1 5 r = tr1_2_1_5 r := by
  revert r
  decide +kernel
lemma tr1_2_1_6_calc (r : Fin 8) : taylorRowBox 1 2 1 6 r = tr1_2_1_6 r := by
  revert r
  decide +kernel
lemma tr1_2_1_7_calc (r : Fin 8) : taylorRowBox 1 2 1 7 r = tr1_2_1_7 r := by
  revert r
  decide +kernel
lemma tr1_2_1_18_calc (r : Fin 8) : taylorRowBox 1 2 1 18 r = tr1_2_1_18 r := by
  revert r
  decide +kernel
lemma tr1_2_1_19_calc (r : Fin 8) : taylorRowBox 1 2 1 19 r = tr1_2_1_19 r := by
  revert r
  decide +kernel
lemma tr1_2_1_20_calc (r : Fin 8) : taylorRowBox 1 2 1 20 r = tr1_2_1_20 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end


