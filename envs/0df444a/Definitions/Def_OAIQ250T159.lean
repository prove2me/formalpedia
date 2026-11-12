-- Prove2me | Definitions.Def_OAIQ250T159
-- name    : OAIQ250T159
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T14:11:43.781255+00:00
-- url     : https://prove2.me/theorems/9d87d0fb-cd58-4fae-ae64-f212f538eda8
-- title:
--   Definitions bundle OAIQ250T159 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 25 declarations of OpenAI's Lean: 25 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Taylor_TaylorWave104`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave104.lean), [`Triangular_Taylor_TaylorWave105`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave105.lean).
--
--   **Imports.** It imports the bundles `OAIQ250T022` and `OAIQ250T077` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ250T113`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ250T022
import Definitions.Def_OAIQ250T077

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorWave104
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw1_0_4_6_calc (j : Fin 31) : taylorWaveBox 1 0 4 6 j = tw1_0_4_6 j := by
  revert j
  decide +kernel
lemma tw1_0_4_7_calc (j : Fin 31) : taylorWaveBox 1 0 4 7 j = tw1_0_4_7 j := by
  revert j
  decide +kernel
lemma tw1_0_4_8_calc (j : Fin 31) : taylorWaveBox 1 0 4 8 j = tw1_0_4_8 j := by
  revert j
  decide +kernel
lemma tw1_0_4_9_calc (j : Fin 31) : taylorWaveBox 1 0 4 9 j = tw1_0_4_9 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorWave105
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw1_0_5_0_calc (j : Fin 31) : taylorWaveBox 1 0 5 0 j = tw1_0_5_0 j := by
  revert j
  decide +kernel
lemma tw1_0_5_1_calc (j : Fin 31) : taylorWaveBox 1 0 5 1 j = tw1_0_5_1 j := by
  revert j
  decide +kernel
lemma tw1_0_5_2_calc (j : Fin 31) : taylorWaveBox 1 0 5 2 j = tw1_0_5_2 j := by
  revert j
  decide +kernel
lemma tw1_0_5_3_calc (j : Fin 31) : taylorWaveBox 1 0 5 3 j = tw1_0_5_3 j := by
  revert j
  decide +kernel
lemma tw1_0_5_4_calc (j : Fin 31) : taylorWaveBox 1 0 5 4 j = tw1_0_5_4 j := by
  revert j
  decide +kernel
lemma tw1_0_5_5_calc (j : Fin 31) : taylorWaveBox 1 0 5 5 j = tw1_0_5_5 j := by
  revert j
  decide +kernel
lemma tw1_0_5_6_calc (j : Fin 31) : taylorWaveBox 1 0 5 6 j = tw1_0_5_6 j := by
  revert j
  decide +kernel
lemma tw1_0_5_7_calc (j : Fin 31) : taylorWaveBox 1 0 5 7 j = tw1_0_5_7 j := by
  revert j
  decide +kernel
lemma tw1_0_5_8_calc (j : Fin 31) : taylorWaveBox 1 0 5 8 j = tw1_0_5_8 j := by
  revert j
  decide +kernel
lemma tw1_0_5_9_calc (j : Fin 31) : taylorWaveBox 1 0 5 9 j = tw1_0_5_9 j := by
  revert j
  decide +kernel
lemma tw1_0_5_10_calc (j : Fin 31) : taylorWaveBox 1 0 5 10 j = tw1_0_5_10 j := by
  revert j
  decide +kernel
lemma tw1_0_5_11_calc (j : Fin 31) : taylorWaveBox 1 0 5 11 j = tw1_0_5_11 j := by
  revert j
  decide +kernel
lemma tw1_0_5_12_calc (j : Fin 31) : taylorWaveBox 1 0 5 12 j = tw1_0_5_12 j := by
  revert j
  decide +kernel
lemma tw1_0_5_13_calc (j : Fin 31) : taylorWaveBox 1 0 5 13 j = tw1_0_5_13 j := by
  revert j
  decide +kernel
lemma tw1_0_5_14_calc (j : Fin 31) : taylorWaveBox 1 0 5 14 j = tw1_0_5_14 j := by
  revert j
  decide +kernel
lemma tw1_0_5_15_calc (j : Fin 31) : taylorWaveBox 1 0 5 15 j = tw1_0_5_15 j := by
  revert j
  decide +kernel
lemma tw1_0_5_16_calc (j : Fin 31) : taylorWaveBox 1 0 5 16 j = tw1_0_5_16 j := by
  revert j
  decide +kernel
lemma tw1_0_5_17_calc (j : Fin 31) : taylorWaveBox 1 0 5 17 j = tw1_0_5_17 j := by
  revert j
  decide +kernel
lemma tw1_0_5_18_calc (j : Fin 31) : taylorWaveBox 1 0 5 18 j = tw1_0_5_18 j := by
  revert j
  decide +kernel
lemma tw1_0_5_19_calc (j : Fin 31) : taylorWaveBox 1 0 5 19 j = tw1_0_5_19 j := by
  revert j
  decide +kernel
lemma tw1_0_5_20_calc (j : Fin 31) : taylorWaveBox 1 0 5 20 j = tw1_0_5_20 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end


