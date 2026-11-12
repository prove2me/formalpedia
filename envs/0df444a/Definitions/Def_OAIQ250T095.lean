-- Prove2me | Definitions.Def_OAIQ250T095
-- name    : OAIQ250T095
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T14:03:29.679941+00:00
-- url     : https://prove2.me/theorems/c8e01c09-c1c7-4844-8be8-51b14cd7aa71
-- title:
--   Definitions bundle OAIQ250T095 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 27 declarations of OpenAI's Lean: 27 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Taylor_TaylorWave106`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave106.lean), [`Triangular_Taylor_TaylorWave110`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave110.lean).
--
--   **Imports.** It imports the bundles `OAIQ250T022`, `OAIQ250T023` and `OAIQ250T077` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ250T113`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ250T022
import Definitions.Def_OAIQ250T023
import Definitions.Def_OAIQ250T077

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorWave106
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw1_0_6_0_calc (j : Fin 31) : taylorWaveBox 1 0 6 0 j = tw1_0_6_0 j := by
  revert j
  decide +kernel
lemma tw1_0_6_1_calc (j : Fin 31) : taylorWaveBox 1 0 6 1 j = tw1_0_6_1 j := by
  revert j
  decide +kernel
lemma tw1_0_6_2_calc (j : Fin 31) : taylorWaveBox 1 0 6 2 j = tw1_0_6_2 j := by
  revert j
  decide +kernel
lemma tw1_0_6_3_calc (j : Fin 31) : taylorWaveBox 1 0 6 3 j = tw1_0_6_3 j := by
  revert j
  decide +kernel
lemma tw1_0_6_4_calc (j : Fin 31) : taylorWaveBox 1 0 6 4 j = tw1_0_6_4 j := by
  revert j
  decide +kernel
lemma tw1_0_6_5_calc (j : Fin 31) : taylorWaveBox 1 0 6 5 j = tw1_0_6_5 j := by
  revert j
  decide +kernel
lemma tw1_0_6_6_calc (j : Fin 31) : taylorWaveBox 1 0 6 6 j = tw1_0_6_6 j := by
  revert j
  decide +kernel
lemma tw1_0_6_7_calc (j : Fin 31) : taylorWaveBox 1 0 6 7 j = tw1_0_6_7 j := by
  revert j
  decide +kernel
lemma tw1_0_6_8_calc (j : Fin 31) : taylorWaveBox 1 0 6 8 j = tw1_0_6_8 j := by
  revert j
  decide +kernel
lemma tw1_0_6_9_calc (j : Fin 31) : taylorWaveBox 1 0 6 9 j = tw1_0_6_9 j := by
  revert j
  decide +kernel
lemma tw1_0_6_10_calc (j : Fin 31) : taylorWaveBox 1 0 6 10 j = tw1_0_6_10 j := by
  revert j
  decide +kernel
lemma tw1_0_6_11_calc (j : Fin 31) : taylorWaveBox 1 0 6 11 j = tw1_0_6_11 j := by
  revert j
  decide +kernel
lemma tw1_0_6_12_calc (j : Fin 31) : taylorWaveBox 1 0 6 12 j = tw1_0_6_12 j := by
  revert j
  decide +kernel
lemma tw1_0_6_13_calc (j : Fin 31) : taylorWaveBox 1 0 6 13 j = tw1_0_6_13 j := by
  revert j
  decide +kernel
lemma tw1_0_6_14_calc (j : Fin 31) : taylorWaveBox 1 0 6 14 j = tw1_0_6_14 j := by
  revert j
  decide +kernel
lemma tw1_0_6_15_calc (j : Fin 31) : taylorWaveBox 1 0 6 15 j = tw1_0_6_15 j := by
  revert j
  decide +kernel
lemma tw1_0_6_16_calc (j : Fin 31) : taylorWaveBox 1 0 6 16 j = tw1_0_6_16 j := by
  revert j
  decide +kernel
lemma tw1_0_6_17_calc (j : Fin 31) : taylorWaveBox 1 0 6 17 j = tw1_0_6_17 j := by
  revert j
  decide +kernel
lemma tw1_0_6_18_calc (j : Fin 31) : taylorWaveBox 1 0 6 18 j = tw1_0_6_18 j := by
  revert j
  decide +kernel
lemma tw1_0_6_19_calc (j : Fin 31) : taylorWaveBox 1 0 6 19 j = tw1_0_6_19 j := by
  revert j
  decide +kernel
lemma tw1_0_6_20_calc (j : Fin 31) : taylorWaveBox 1 0 6 20 j = tw1_0_6_20 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorWave110
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw1_1_0_0_calc (j : Fin 31) : taylorWaveBox 1 1 0 0 j = tw1_1_0_0 j := by
  revert j
  decide +kernel
lemma tw1_1_0_10_calc (j : Fin 31) : taylorWaveBox 1 1 0 10 j = tw1_1_0_10 j := by
  revert j
  decide +kernel
lemma tw1_1_0_11_calc (j : Fin 31) : taylorWaveBox 1 1 0 11 j = tw1_1_0_11 j := by
  revert j
  decide +kernel
lemma tw1_1_0_12_calc (j : Fin 31) : taylorWaveBox 1 1 0 12 j = tw1_1_0_12 j := by
  revert j
  decide +kernel
lemma tw1_1_0_13_calc (j : Fin 31) : taylorWaveBox 1 1 0 13 j = tw1_1_0_13 j := by
  revert j
  decide +kernel
lemma tw1_1_0_14_calc (j : Fin 31) : taylorWaveBox 1 1 0 14 j = tw1_1_0_14 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end


