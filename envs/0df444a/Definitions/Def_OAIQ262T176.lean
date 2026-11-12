-- Prove2me | Definitions.Def_OAIQ262T176
-- name    : OAIQ262T176
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T18:16:39.850356+00:00
-- url     : https://prove2.me/theorems/69a84321-261a-436e-9385-83f75bf8d4e9
-- title:
--   Definitions bundle OAIQ262T176 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 27 declarations of OpenAI's Lean: 27 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Taylor_TaylorWave102`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave102.lean), [`Triangular_Taylor_TaylorWave103`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave103.lean), [`Triangular_Taylor_TaylorWave104`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave104.lean).
--
--   **Imports.** It imports the bundle `OAIQ262T148` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ262T261`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ262T148

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave102
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw1_0_2_1_calc (j : Fin 31) : taylorWaveBox 1 0 2 1 j = tw1_0_2_1 j := by
  revert j
  decide +kernel
lemma tw1_0_2_2_calc (j : Fin 31) : taylorWaveBox 1 0 2 2 j = tw1_0_2_2 j := by
  revert j
  decide +kernel
lemma tw1_0_2_3_calc (j : Fin 31) : taylorWaveBox 1 0 2 3 j = tw1_0_2_3 j := by
  revert j
  decide +kernel
lemma tw1_0_2_4_calc (j : Fin 31) : taylorWaveBox 1 0 2 4 j = tw1_0_2_4 j := by
  revert j
  decide +kernel
lemma tw1_0_2_5_calc (j : Fin 31) : taylorWaveBox 1 0 2 5 j = tw1_0_2_5 j := by
  revert j
  decide +kernel
lemma tw1_0_2_6_calc (j : Fin 31) : taylorWaveBox 1 0 2 6 j = tw1_0_2_6 j := by
  revert j
  decide +kernel
lemma tw1_0_2_7_calc (j : Fin 31) : taylorWaveBox 1 0 2 7 j = tw1_0_2_7 j := by
  revert j
  decide +kernel
lemma tw1_0_2_8_calc (j : Fin 31) : taylorWaveBox 1 0 2 8 j = tw1_0_2_8 j := by
  revert j
  decide +kernel
lemma tw1_0_2_9_calc (j : Fin 31) : taylorWaveBox 1 0 2 9 j = tw1_0_2_9 j := by
  revert j
  decide +kernel
lemma tw1_0_2_19_calc (j : Fin 31) : taylorWaveBox 1 0 2 19 j = tw1_0_2_19 j := by
  revert j
  decide +kernel
lemma tw1_0_2_20_calc (j : Fin 31) : taylorWaveBox 1 0 2 20 j = tw1_0_2_20 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave103
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw1_0_3_0_calc (j : Fin 31) : taylorWaveBox 1 0 3 0 j = tw1_0_3_0 j := by
  revert j
  decide +kernel
lemma tw1_0_3_1_calc (j : Fin 31) : taylorWaveBox 1 0 3 1 j = tw1_0_3_1 j := by
  revert j
  decide +kernel
lemma tw1_0_3_2_calc (j : Fin 31) : taylorWaveBox 1 0 3 2 j = tw1_0_3_2 j := by
  revert j
  decide +kernel
lemma tw1_0_3_3_calc (j : Fin 31) : taylorWaveBox 1 0 3 3 j = tw1_0_3_3 j := by
  revert j
  decide +kernel
lemma tw1_0_3_10_calc (j : Fin 31) : taylorWaveBox 1 0 3 10 j = tw1_0_3_10 j := by
  revert j
  decide +kernel
lemma tw1_0_3_11_calc (j : Fin 31) : taylorWaveBox 1 0 3 11 j = tw1_0_3_11 j := by
  revert j
  decide +kernel
lemma tw1_0_3_12_calc (j : Fin 31) : taylorWaveBox 1 0 3 12 j = tw1_0_3_12 j := by
  revert j
  decide +kernel
lemma tw1_0_3_13_calc (j : Fin 31) : taylorWaveBox 1 0 3 13 j = tw1_0_3_13 j := by
  revert j
  decide +kernel
lemma tw1_0_3_14_calc (j : Fin 31) : taylorWaveBox 1 0 3 14 j = tw1_0_3_14 j := by
  revert j
  decide +kernel
lemma tw1_0_3_15_calc (j : Fin 31) : taylorWaveBox 1 0 3 15 j = tw1_0_3_15 j := by
  revert j
  decide +kernel
lemma tw1_0_3_16_calc (j : Fin 31) : taylorWaveBox 1 0 3 16 j = tw1_0_3_16 j := by
  revert j
  decide +kernel
lemma tw1_0_3_17_calc (j : Fin 31) : taylorWaveBox 1 0 3 17 j = tw1_0_3_17 j := by
  revert j
  decide +kernel
lemma tw1_0_3_18_calc (j : Fin 31) : taylorWaveBox 1 0 3 18 j = tw1_0_3_18 j := by
  revert j
  decide +kernel
lemma tw1_0_3_19_calc (j : Fin 31) : taylorWaveBox 1 0 3 19 j = tw1_0_3_19 j := by
  revert j
  decide +kernel
lemma tw1_0_3_20_calc (j : Fin 31) : taylorWaveBox 1 0 3 20 j = tw1_0_3_20 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave104
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw1_0_4_17_calc (j : Fin 31) : taylorWaveBox 1 0 4 17 j = tw1_0_4_17 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end


