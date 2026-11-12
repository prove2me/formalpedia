-- Prove2me | Definitions.Def_OAIQ262T241
-- name    : OAIQ262T241
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T18:55:39.609215+00:00
-- url     : https://prove2.me/theorems/2b3521f9-2f8d-4370-a9bb-0a97725cd6c8
-- title:
--   Definitions bundle OAIQ262T241 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 11 declarations of OpenAI's Lean: 11 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Taylor_TaylorRows14`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorRows14.lean).
--
--   **Imports.** It imports the bundles `OAIQ262T076`, `OAIQ262T077` and `OAIQ262T161` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ262T264`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ262T076
import Definitions.Def_OAIQ262T077
import Definitions.Def_OAIQ262T161

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorRows14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma tr1_4_0_1_calc (r : Fin 8) : taylorRowBox 1 4 0 1 r = tr1_4_0_1 r := by
  revert r
  decide +kernel
lemma tr1_4_0_2_calc (r : Fin 8) : taylorRowBox 1 4 0 2 r = tr1_4_0_2 r := by
  revert r
  decide +kernel
lemma tr1_4_0_3_calc (r : Fin 8) : taylorRowBox 1 4 0 3 r = tr1_4_0_3 r := by
  revert r
  decide +kernel
lemma tr1_4_0_4_calc (r : Fin 8) : taylorRowBox 1 4 0 4 r = tr1_4_0_4 r := by
  revert r
  decide +kernel
lemma tr1_4_0_5_calc (r : Fin 8) : taylorRowBox 1 4 0 5 r = tr1_4_0_5 r := by
  revert r
  decide +kernel
lemma tr1_4_0_6_calc (r : Fin 8) : taylorRowBox 1 4 0 6 r = tr1_4_0_6 r := by
  revert r
  decide +kernel
lemma tr1_4_0_16_calc (r : Fin 8) : taylorRowBox 1 4 0 16 r = tr1_4_0_16 r := by
  revert r
  decide +kernel
lemma tr1_4_0_17_calc (r : Fin 8) : taylorRowBox 1 4 0 17 r = tr1_4_0_17 r := by
  revert r
  decide +kernel
lemma tr1_4_0_18_calc (r : Fin 8) : taylorRowBox 1 4 0 18 r = tr1_4_0_18 r := by
  revert r
  decide +kernel
lemma tr1_4_0_19_calc (r : Fin 8) : taylorRowBox 1 4 0 19 r = tr1_4_0_19 r := by
  revert r
  decide +kernel
lemma tr1_4_0_20_calc (r : Fin 8) : taylorRowBox 1 4 0 20 r = tr1_4_0_20 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end


