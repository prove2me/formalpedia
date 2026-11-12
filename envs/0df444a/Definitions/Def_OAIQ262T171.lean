-- Prove2me | Definitions.Def_OAIQ262T171
-- name    : OAIQ262T171
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T18:09:05.809834+00:00
-- url     : https://prove2.me/theorems/2ab1e2fc-3ab5-46a1-9424-fd3b2a8275a9
-- title:
--   Definitions bundle OAIQ262T171 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 27 declarations of OpenAI's Lean: 27 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Signs_Signs00`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/Signs00.lean), [`Triangular_Taylor_TaylorWave013`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave013.lean), [`Triangular_Taylor_TaylorWave014`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave014.lean).
--
--   **Imports.** It imports the bundles `OAIQ262T110`, `OAIQ262T147` and `OAIQ262T148` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ262T261`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ262T110
import Definitions.Def_OAIQ262T147
import Definitions.Def_OAIQ262T148

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave013
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw0_1_3_1_calc (j : Fin 31) : taylorWaveBox 0 1 3 1 j = tw0_1_3_1 j := by
  revert j
  decide +kernel
lemma tw0_1_3_2_calc (j : Fin 31) : taylorWaveBox 0 1 3 2 j = tw0_1_3_2 j := by
  revert j
  decide +kernel
lemma tw0_1_3_3_calc (j : Fin 31) : taylorWaveBox 0 1 3 3 j = tw0_1_3_3 j := by
  revert j
  decide +kernel
lemma tw0_1_3_4_calc (j : Fin 31) : taylorWaveBox 0 1 3 4 j = tw0_1_3_4 j := by
  revert j
  decide +kernel
lemma tw0_1_3_5_calc (j : Fin 31) : taylorWaveBox 0 1 3 5 j = tw0_1_3_5 j := by
  revert j
  decide +kernel
lemma tw0_1_3_6_calc (j : Fin 31) : taylorWaveBox 0 1 3 6 j = tw0_1_3_6 j := by
  revert j
  decide +kernel
lemma tw0_1_3_7_calc (j : Fin 31) : taylorWaveBox 0 1 3 7 j = tw0_1_3_7 j := by
  revert j
  decide +kernel
lemma tw0_1_3_8_calc (j : Fin 31) : taylorWaveBox 0 1 3 8 j = tw0_1_3_8 j := by
  revert j
  decide +kernel
lemma tw0_1_3_9_calc (j : Fin 31) : taylorWaveBox 0 1 3 9 j = tw0_1_3_9 j := by
  revert j
  decide +kernel
lemma tw0_1_3_16_calc (j : Fin 31) : taylorWaveBox 0 1 3 16 j = tw0_1_3_16 j := by
  revert j
  decide +kernel
lemma tw0_1_3_17_calc (j : Fin 31) : taylorWaveBox 0 1 3 17 j = tw0_1_3_17 j := by
  revert j
  decide +kernel
lemma tw0_1_3_18_calc (j : Fin 31) : taylorWaveBox 0 1 3 18 j = tw0_1_3_18 j := by
  revert j
  decide +kernel
lemma tw0_1_3_20_calc (j : Fin 31) : taylorWaveBox 0 1 3 20 j = tw0_1_3_20 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave014
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw0_1_4_0_calc (j : Fin 31) : taylorWaveBox 0 1 4 0 j = tw0_1_4_0 j := by
  revert j
  decide +kernel
lemma tw0_1_4_1_calc (j : Fin 31) : taylorWaveBox 0 1 4 1 j = tw0_1_4_1 j := by
  revert j
  decide +kernel
lemma tw0_1_4_10_calc (j : Fin 31) : taylorWaveBox 0 1 4 10 j = tw0_1_4_10 j := by
  revert j
  decide +kernel
lemma tw0_1_4_11_calc (j : Fin 31) : taylorWaveBox 0 1 4 11 j = tw0_1_4_11 j := by
  revert j
  decide +kernel
lemma tw0_1_4_12_calc (j : Fin 31) : taylorWaveBox 0 1 4 12 j = tw0_1_4_12 j := by
  revert j
  decide +kernel
lemma tw0_1_4_13_calc (j : Fin 31) : taylorWaveBox 0 1 4 13 j = tw0_1_4_13 j := by
  revert j
  decide +kernel
lemma tw0_1_4_14_calc (j : Fin 31) : taylorWaveBox 0 1 4 14 j = tw0_1_4_14 j := by
  revert j
  decide +kernel
lemma tw0_1_4_15_calc (j : Fin 31) : taylorWaveBox 0 1 4 15 j = tw0_1_4_15 j := by
  revert j
  decide +kernel
lemma tw0_1_4_16_calc (j : Fin 31) : taylorWaveBox 0 1 4 16 j = tw0_1_4_16 j := by
  revert j
  decide +kernel
lemma tw0_1_4_17_calc (j : Fin 31) : taylorWaveBox 0 1 4 17 j = tw0_1_4_17 j := by
  revert j
  decide +kernel
lemma tw0_1_4_18_calc (j : Fin 31) : taylorWaveBox 0 1 4 18 j = tw0_1_4_18 j := by
  revert j
  decide +kernel
lemma tw0_1_4_19_calc (j : Fin 31) : taylorWaveBox 0 1 4 19 j = tw0_1_4_19 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_Signs00
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma bs0_0_0_13_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 0 tr0_0_0) 13 r = bs0_0_0_13 r := by
  revert r
  decide +kernel
lemma bs0_0_0_14_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 0 tr0_0_0) 14 r = bs0_0_0_14 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end


