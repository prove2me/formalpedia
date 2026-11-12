-- Prove2me | Definitions.Def_OAIQ250T154
-- name    : OAIQ250T154
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T14:05:50.235356+00:00
-- url     : https://prove2.me/theorems/05312fd2-9667-465d-856e-4d9d2704999a
-- title:
--   Definitions bundle OAIQ250T154 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 22 declarations of OpenAI's Lean: 22 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Taylor_TaylorWave006`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave006.lean), [`Triangular_Taylor_TaylorWave010`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave010.lean).
--
--   **Imports.** It imports the bundles `OAIQ250T017` and `OAIQ250T077` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ250T113`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ250T017
import Definitions.Def_OAIQ250T077

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorWave006
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw0_0_6_2_calc (j : Fin 31) : taylorWaveBox 0 0 6 2 j = tw0_0_6_2 j := by
  revert j
  decide +kernel
lemma tw0_0_6_3_calc (j : Fin 31) : taylorWaveBox 0 0 6 3 j = tw0_0_6_3 j := by
  revert j
  decide +kernel
lemma tw0_0_6_4_calc (j : Fin 31) : taylorWaveBox 0 0 6 4 j = tw0_0_6_4 j := by
  revert j
  decide +kernel
lemma tw0_0_6_5_calc (j : Fin 31) : taylorWaveBox 0 0 6 5 j = tw0_0_6_5 j := by
  revert j
  decide +kernel
lemma tw0_0_6_6_calc (j : Fin 31) : taylorWaveBox 0 0 6 6 j = tw0_0_6_6 j := by
  revert j
  decide +kernel
lemma tw0_0_6_7_calc (j : Fin 31) : taylorWaveBox 0 0 6 7 j = tw0_0_6_7 j := by
  revert j
  decide +kernel
lemma tw0_0_6_8_calc (j : Fin 31) : taylorWaveBox 0 0 6 8 j = tw0_0_6_8 j := by
  revert j
  decide +kernel
lemma tw0_0_6_9_calc (j : Fin 31) : taylorWaveBox 0 0 6 9 j = tw0_0_6_9 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorWave010
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw0_1_0_0_calc (j : Fin 31) : taylorWaveBox 0 1 0 0 j = tw0_1_0_0 j := by
  revert j
  decide +kernel
lemma tw0_1_0_1_calc (j : Fin 31) : taylorWaveBox 0 1 0 1 j = tw0_1_0_1 j := by
  revert j
  decide +kernel
lemma tw0_1_0_2_calc (j : Fin 31) : taylorWaveBox 0 1 0 2 j = tw0_1_0_2 j := by
  revert j
  decide +kernel
lemma tw0_1_0_10_calc (j : Fin 31) : taylorWaveBox 0 1 0 10 j = tw0_1_0_10 j := by
  revert j
  decide +kernel
lemma tw0_1_0_11_calc (j : Fin 31) : taylorWaveBox 0 1 0 11 j = tw0_1_0_11 j := by
  revert j
  decide +kernel
lemma tw0_1_0_12_calc (j : Fin 31) : taylorWaveBox 0 1 0 12 j = tw0_1_0_12 j := by
  revert j
  decide +kernel
lemma tw0_1_0_13_calc (j : Fin 31) : taylorWaveBox 0 1 0 13 j = tw0_1_0_13 j := by
  revert j
  decide +kernel
lemma tw0_1_0_14_calc (j : Fin 31) : taylorWaveBox 0 1 0 14 j = tw0_1_0_14 j := by
  revert j
  decide +kernel
lemma tw0_1_0_15_calc (j : Fin 31) : taylorWaveBox 0 1 0 15 j = tw0_1_0_15 j := by
  revert j
  decide +kernel
lemma tw0_1_0_16_calc (j : Fin 31) : taylorWaveBox 0 1 0 16 j = tw0_1_0_16 j := by
  revert j
  decide +kernel
lemma tw0_1_0_17_calc (j : Fin 31) : taylorWaveBox 0 1 0 17 j = tw0_1_0_17 j := by
  revert j
  decide +kernel
lemma tw0_1_0_18_calc (j : Fin 31) : taylorWaveBox 0 1 0 18 j = tw0_1_0_18 j := by
  revert j
  decide +kernel
lemma tw0_1_0_19_calc (j : Fin 31) : taylorWaveBox 0 1 0 19 j = tw0_1_0_19 j := by
  revert j
  decide +kernel
lemma tw0_1_0_20_calc (j : Fin 31) : taylorWaveBox 0 1 0 20 j = tw0_1_0_20 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end


