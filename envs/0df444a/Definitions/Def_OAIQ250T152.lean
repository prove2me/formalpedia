-- Prove2me | Definitions.Def_OAIQ250T152
-- name    : OAIQ250T152
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T14:04:11.899657+00:00
-- url     : https://prove2.me/theorems/b235a3bf-a1ff-4ed3-b45c-7f72cfc8ed40
-- title:
--   Definitions bundle OAIQ250T152 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 28 declarations of OpenAI's Lean: 28 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Taylor_TaylorWave001`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave001.lean), [`Triangular_Taylor_TaylorWave002`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave002.lean).
--
--   **Imports.** It imports the bundle `OAIQ250T077` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ250T113`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ250T077

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorWave001
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw0_0_1_1_calc (j : Fin 31) : taylorWaveBox 0 0 1 1 j = tw0_0_1_1 j := by
  revert j
  decide +kernel
lemma tw0_0_1_2_calc (j : Fin 31) : taylorWaveBox 0 0 1 2 j = tw0_0_1_2 j := by
  revert j
  decide +kernel
lemma tw0_0_1_3_calc (j : Fin 31) : taylorWaveBox 0 0 1 3 j = tw0_0_1_3 j := by
  revert j
  decide +kernel
lemma tw0_0_1_4_calc (j : Fin 31) : taylorWaveBox 0 0 1 4 j = tw0_0_1_4 j := by
  revert j
  decide +kernel
lemma tw0_0_1_5_calc (j : Fin 31) : taylorWaveBox 0 0 1 5 j = tw0_0_1_5 j := by
  revert j
  decide +kernel
lemma tw0_0_1_6_calc (j : Fin 31) : taylorWaveBox 0 0 1 6 j = tw0_0_1_6 j := by
  revert j
  decide +kernel
lemma tw0_0_1_7_calc (j : Fin 31) : taylorWaveBox 0 0 1 7 j = tw0_0_1_7 j := by
  revert j
  decide +kernel
lemma tw0_0_1_8_calc (j : Fin 31) : taylorWaveBox 0 0 1 8 j = tw0_0_1_8 j := by
  revert j
  decide +kernel
lemma tw0_0_1_9_calc (j : Fin 31) : taylorWaveBox 0 0 1 9 j = tw0_0_1_9 j := by
  revert j
  decide +kernel
lemma tw0_0_1_15_calc (j : Fin 31) : taylorWaveBox 0 0 1 15 j = tw0_0_1_15 j := by
  revert j
  decide +kernel
lemma tw0_0_1_16_calc (j : Fin 31) : taylorWaveBox 0 0 1 16 j = tw0_0_1_16 j := by
  revert j
  decide +kernel
lemma tw0_0_1_17_calc (j : Fin 31) : taylorWaveBox 0 0 1 17 j = tw0_0_1_17 j := by
  revert j
  decide +kernel
lemma tw0_0_1_18_calc (j : Fin 31) : taylorWaveBox 0 0 1 18 j = tw0_0_1_18 j := by
  revert j
  decide +kernel
lemma tw0_0_1_19_calc (j : Fin 31) : taylorWaveBox 0 0 1 19 j = tw0_0_1_19 j := by
  revert j
  decide +kernel
lemma tw0_0_1_20_calc (j : Fin 31) : taylorWaveBox 0 0 1 20 j = tw0_0_1_20 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorWave002
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw0_0_2_0_calc (j : Fin 31) : taylorWaveBox 0 0 2 0 j = tw0_0_2_0 j := by
  revert j
  decide +kernel
lemma tw0_0_2_1_calc (j : Fin 31) : taylorWaveBox 0 0 2 1 j = tw0_0_2_1 j := by
  revert j
  decide +kernel
lemma tw0_0_2_10_calc (j : Fin 31) : taylorWaveBox 0 0 2 10 j = tw0_0_2_10 j := by
  revert j
  decide +kernel
lemma tw0_0_2_11_calc (j : Fin 31) : taylorWaveBox 0 0 2 11 j = tw0_0_2_11 j := by
  revert j
  decide +kernel
lemma tw0_0_2_12_calc (j : Fin 31) : taylorWaveBox 0 0 2 12 j = tw0_0_2_12 j := by
  revert j
  decide +kernel
lemma tw0_0_2_13_calc (j : Fin 31) : taylorWaveBox 0 0 2 13 j = tw0_0_2_13 j := by
  revert j
  decide +kernel
lemma tw0_0_2_14_calc (j : Fin 31) : taylorWaveBox 0 0 2 14 j = tw0_0_2_14 j := by
  revert j
  decide +kernel
lemma tw0_0_2_15_calc (j : Fin 31) : taylorWaveBox 0 0 2 15 j = tw0_0_2_15 j := by
  revert j
  decide +kernel
lemma tw0_0_2_16_calc (j : Fin 31) : taylorWaveBox 0 0 2 16 j = tw0_0_2_16 j := by
  revert j
  decide +kernel
lemma tw0_0_2_17_calc (j : Fin 31) : taylorWaveBox 0 0 2 17 j = tw0_0_2_17 j := by
  revert j
  decide +kernel
lemma tw0_0_2_18_calc (j : Fin 31) : taylorWaveBox 0 0 2 18 j = tw0_0_2_18 j := by
  revert j
  decide +kernel
lemma tw0_0_2_19_calc (j : Fin 31) : taylorWaveBox 0 0 2 19 j = tw0_0_2_19 j := by
  revert j
  decide +kernel
lemma tw0_0_2_20_calc (j : Fin 31) : taylorWaveBox 0 0 2 20 j = tw0_0_2_20 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end


