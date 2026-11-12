-- Prove2me | Definitions.Def_OAIQ250T094
-- name    : OAIQ250T094
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T14:02:00.396207+00:00
-- url     : https://prove2.me/theorems/b3efd873-a7c3-4171-a82a-ec94f47b9899
-- title:
--   Definitions bundle OAIQ250T094 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 30 declarations of OpenAI's Lean: 30 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Signs_ExceptionalSign1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/ExceptionalSign1.lean), [`Triangular_Taylor_TaylorWave103`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave103.lean), [`Triangular_Taylor_TaylorWave104`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave104.lean).
--
--   **Imports.** It imports the bundles `OAIQ250T019`, `OAIQ250T021`, `OAIQ250T022`, `OAIQ250T077` and `OAIQ250T079` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ250T113`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ250T019
import Definitions.Def_OAIQ250T021
import Definitions.Def_OAIQ250T022
import Definitions.Def_OAIQ250T077
import Definitions.Def_OAIQ250T079

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorWave103
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw1_0_3_1_calc (j : Fin 31) : taylorWaveBox 1 0 3 1 j = tw1_0_3_1 j := by
  revert j
  decide +kernel
lemma tw1_0_3_2_calc (j : Fin 31) : taylorWaveBox 1 0 3 2 j = tw1_0_3_2 j := by
  revert j
  decide +kernel
lemma tw1_0_3_3_calc (j : Fin 31) : taylorWaveBox 1 0 3 3 j = tw1_0_3_3 j := by
  revert j
  decide +kernel
lemma tw1_0_3_4_calc (j : Fin 31) : taylorWaveBox 1 0 3 4 j = tw1_0_3_4 j := by
  revert j
  decide +kernel
lemma tw1_0_3_5_calc (j : Fin 31) : taylorWaveBox 1 0 3 5 j = tw1_0_3_5 j := by
  revert j
  decide +kernel
lemma tw1_0_3_6_calc (j : Fin 31) : taylorWaveBox 1 0 3 6 j = tw1_0_3_6 j := by
  revert j
  decide +kernel
lemma tw1_0_3_7_calc (j : Fin 31) : taylorWaveBox 1 0 3 7 j = tw1_0_3_7 j := by
  revert j
  decide +kernel
lemma tw1_0_3_8_calc (j : Fin 31) : taylorWaveBox 1 0 3 8 j = tw1_0_3_8 j := by
  revert j
  decide +kernel
lemma tw1_0_3_9_calc (j : Fin 31) : taylorWaveBox 1 0 3 9 j = tw1_0_3_9 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

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
lemma tw1_0_4_0_calc (j : Fin 31) : taylorWaveBox 1 0 4 0 j = tw1_0_4_0 j := by
  revert j
  decide +kernel
lemma tw1_0_4_1_calc (j : Fin 31) : taylorWaveBox 1 0 4 1 j = tw1_0_4_1 j := by
  revert j
  decide +kernel
lemma tw1_0_4_2_calc (j : Fin 31) : taylorWaveBox 1 0 4 2 j = tw1_0_4_2 j := by
  revert j
  decide +kernel
lemma tw1_0_4_3_calc (j : Fin 31) : taylorWaveBox 1 0 4 3 j = tw1_0_4_3 j := by
  revert j
  decide +kernel
lemma tw1_0_4_4_calc (j : Fin 31) : taylorWaveBox 1 0 4 4 j = tw1_0_4_4 j := by
  revert j
  decide +kernel
lemma tw1_0_4_5_calc (j : Fin 31) : taylorWaveBox 1 0 4 5 j = tw1_0_4_5 j := by
  revert j
  decide +kernel
lemma tw1_0_4_10_calc (j : Fin 31) : taylorWaveBox 1 0 4 10 j = tw1_0_4_10 j := by
  revert j
  decide +kernel
lemma tw1_0_4_11_calc (j : Fin 31) : taylorWaveBox 1 0 4 11 j = tw1_0_4_11 j := by
  revert j
  decide +kernel
lemma tw1_0_4_12_calc (j : Fin 31) : taylorWaveBox 1 0 4 12 j = tw1_0_4_12 j := by
  revert j
  decide +kernel
lemma tw1_0_4_13_calc (j : Fin 31) : taylorWaveBox 1 0 4 13 j = tw1_0_4_13 j := by
  revert j
  decide +kernel
lemma tw1_0_4_14_calc (j : Fin 31) : taylorWaveBox 1 0 4 14 j = tw1_0_4_14 j := by
  revert j
  decide +kernel
lemma tw1_0_4_15_calc (j : Fin 31) : taylorWaveBox 1 0 4 15 j = tw1_0_4_15 j := by
  revert j
  decide +kernel
lemma tw1_0_4_16_calc (j : Fin 31) : taylorWaveBox 1 0 4 16 j = tw1_0_4_16 j := by
  revert j
  decide +kernel
lemma tw1_0_4_17_calc (j : Fin 31) : taylorWaveBox 1 0 4 17 j = tw1_0_4_17 j := by
  revert j
  decide +kernel
lemma tw1_0_4_18_calc (j : Fin 31) : taylorWaveBox 1 0 4 18 j = tw1_0_4_18 j := by
  revert j
  decide +kernel
lemma tw1_0_4_19_calc (j : Fin 31) : taylorWaveBox 1 0 4 19 j = tw1_0_4_19 j := by
  revert j
  decide +kernel
lemma tw1_0_4_20_calc (j : Fin 31) : taylorWaveBox 1 0 4 20 j = tw1_0_4_20 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_ExceptionalSign1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma ex1b4_calc (r : Fin 8) : bernsteinRowsBox 22 ex1r 4 r = ex1b4 r := by
  revert r
  decide +kernel
lemma ex1b5_calc (r : Fin 8) : bernsteinRowsBox 22 ex1r 5 r = ex1b5 r := by
  revert r
  decide +kernel
lemma ex1b6_calc (r : Fin 8) : bernsteinRowsBox 22 ex1r 6 r = ex1b6 r := by
  revert r
  decide +kernel
lemma ex1b7_calc (r : Fin 8) : bernsteinRowsBox 22 ex1r 7 r = ex1b7 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end


