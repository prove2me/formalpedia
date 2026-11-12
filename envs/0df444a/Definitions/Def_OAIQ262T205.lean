-- Prove2me | Definitions.Def_OAIQ262T205
-- name    : OAIQ262T205
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T18:33:11.692218+00:00
-- url     : https://prove2.me/theorems/acef0d1f-d836-41d4-841f-c5b6cd5d9bbf
-- title:
--   Definitions bundle OAIQ262T205 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 11 declarations of OpenAI's Lean: 11 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Taylor_TaylorRows02`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorRows02.lean), [`Triangular_Taylor_TaylorRows04`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorRows04.lean).
--
--   **Imports.** It imports the bundles `OAIQ262T050`, `OAIQ262T051`, `OAIQ262T056` and `OAIQ262T161` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ262T262`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ262T050
import Definitions.Def_OAIQ262T051
import Definitions.Def_OAIQ262T056
import Definitions.Def_OAIQ262T161

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorRows02
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma tr0_2_0_1_calc (r : Fin 8) : taylorRowBox 0 2 0 1 r = tr0_2_0_1 r := by
  revert r
  decide +kernel
lemma tr0_2_0_2_calc (r : Fin 8) : taylorRowBox 0 2 0 2 r = tr0_2_0_2 r := by
  revert r
  decide +kernel
lemma tr0_2_0_3_calc (r : Fin 8) : taylorRowBox 0 2 0 3 r = tr0_2_0_3 r := by
  revert r
  decide +kernel
lemma tr0_2_0_4_calc (r : Fin 8) : taylorRowBox 0 2 0 4 r = tr0_2_0_4 r := by
  revert r
  decide +kernel
lemma tr0_2_0_5_calc (r : Fin 8) : taylorRowBox 0 2 0 5 r = tr0_2_0_5 r := by
  revert r
  decide +kernel
lemma tr0_2_0_6_calc (r : Fin 8) : taylorRowBox 0 2 0 6 r = tr0_2_0_6 r := by
  revert r
  decide +kernel
lemma tr0_2_0_7_calc (r : Fin 8) : taylorRowBox 0 2 0 7 r = tr0_2_0_7 r := by
  revert r
  decide +kernel
lemma tr0_2_0_8_calc (r : Fin 8) : taylorRowBox 0 2 0 8 r = tr0_2_0_8 r := by
  revert r
  decide +kernel
lemma tr0_2_0_19_calc (r : Fin 8) : taylorRowBox 0 2 0 19 r = tr0_2_0_19 r := by
  revert r
  decide +kernel
lemma tr0_2_0_20_calc (r : Fin 8) : taylorRowBox 0 2 0 20 r = tr0_2_0_20 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorRows04
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma tr0_4_0_19_calc (r : Fin 8) : taylorRowBox 0 4 0 19 r = tr0_4_0_19 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end


