-- Prove2me | Definitions.Def_OAIQ250T092
-- name    : OAIQ250T092
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T14:03:47.333866+00:00
-- url     : https://prove2.me/theorems/60e41c89-cc3a-439e-b9d1-2480742cc9f5
-- title:
--   Definitions bundle OAIQ250T092 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 29 declarations of OpenAI's Lean: 29 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Signs_ExceptionalSign1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/ExceptionalSign1.lean), [`Triangular_Taylor_TaylorWave015`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave015.lean), [`Triangular_Taylor_TaylorWave016`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave016.lean), [`Triangular_Taylor_TaylorWave100`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave100.lean).
--
--   **Imports.** It imports the bundles `OAIQ250T017`, `OAIQ250T019`, `OAIQ250T077` and `OAIQ250T079` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ250T113`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ250T017
import Definitions.Def_OAIQ250T019
import Definitions.Def_OAIQ250T077
import Definitions.Def_OAIQ250T079

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorWave015
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw0_1_5_5_calc (j : Fin 31) : taylorWaveBox 0 1 5 5 j = tw0_1_5_5 j := by
  revert j
  decide +kernel
lemma tw0_1_5_6_calc (j : Fin 31) : taylorWaveBox 0 1 5 6 j = tw0_1_5_6 j := by
  revert j
  decide +kernel
lemma tw0_1_5_7_calc (j : Fin 31) : taylorWaveBox 0 1 5 7 j = tw0_1_5_7 j := by
  revert j
  decide +kernel
lemma tw0_1_5_8_calc (j : Fin 31) : taylorWaveBox 0 1 5 8 j = tw0_1_5_8 j := by
  revert j
  decide +kernel
lemma tw0_1_5_9_calc (j : Fin 31) : taylorWaveBox 0 1 5 9 j = tw0_1_5_9 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorWave016
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw0_1_6_0_calc (j : Fin 31) : taylorWaveBox 0 1 6 0 j = tw0_1_6_0 j := by
  revert j
  decide +kernel
lemma tw0_1_6_1_calc (j : Fin 31) : taylorWaveBox 0 1 6 1 j = tw0_1_6_1 j := by
  revert j
  decide +kernel
lemma tw0_1_6_2_calc (j : Fin 31) : taylorWaveBox 0 1 6 2 j = tw0_1_6_2 j := by
  revert j
  decide +kernel
lemma tw0_1_6_3_calc (j : Fin 31) : taylorWaveBox 0 1 6 3 j = tw0_1_6_3 j := by
  revert j
  decide +kernel
lemma tw0_1_6_4_calc (j : Fin 31) : taylorWaveBox 0 1 6 4 j = tw0_1_6_4 j := by
  revert j
  decide +kernel
lemma tw0_1_6_5_calc (j : Fin 31) : taylorWaveBox 0 1 6 5 j = tw0_1_6_5 j := by
  revert j
  decide +kernel
lemma tw0_1_6_6_calc (j : Fin 31) : taylorWaveBox 0 1 6 6 j = tw0_1_6_6 j := by
  revert j
  decide +kernel
lemma tw0_1_6_7_calc (j : Fin 31) : taylorWaveBox 0 1 6 7 j = tw0_1_6_7 j := by
  revert j
  decide +kernel
lemma tw0_1_6_8_calc (j : Fin 31) : taylorWaveBox 0 1 6 8 j = tw0_1_6_8 j := by
  revert j
  decide +kernel
lemma tw0_1_6_9_calc (j : Fin 31) : taylorWaveBox 0 1 6 9 j = tw0_1_6_9 j := by
  revert j
  decide +kernel
lemma tw0_1_6_10_calc (j : Fin 31) : taylorWaveBox 0 1 6 10 j = tw0_1_6_10 j := by
  revert j
  decide +kernel
lemma tw0_1_6_11_calc (j : Fin 31) : taylorWaveBox 0 1 6 11 j = tw0_1_6_11 j := by
  revert j
  decide +kernel
lemma tw0_1_6_12_calc (j : Fin 31) : taylorWaveBox 0 1 6 12 j = tw0_1_6_12 j := by
  revert j
  decide +kernel
lemma tw0_1_6_13_calc (j : Fin 31) : taylorWaveBox 0 1 6 13 j = tw0_1_6_13 j := by
  revert j
  decide +kernel
lemma tw0_1_6_14_calc (j : Fin 31) : taylorWaveBox 0 1 6 14 j = tw0_1_6_14 j := by
  revert j
  decide +kernel
lemma tw0_1_6_15_calc (j : Fin 31) : taylorWaveBox 0 1 6 15 j = tw0_1_6_15 j := by
  revert j
  decide +kernel
lemma tw0_1_6_16_calc (j : Fin 31) : taylorWaveBox 0 1 6 16 j = tw0_1_6_16 j := by
  revert j
  decide +kernel
lemma tw0_1_6_17_calc (j : Fin 31) : taylorWaveBox 0 1 6 17 j = tw0_1_6_17 j := by
  revert j
  decide +kernel
lemma tw0_1_6_18_calc (j : Fin 31) : taylorWaveBox 0 1 6 18 j = tw0_1_6_18 j := by
  revert j
  decide +kernel
lemma tw0_1_6_19_calc (j : Fin 31) : taylorWaveBox 0 1 6 19 j = tw0_1_6_19 j := by
  revert j
  decide +kernel
lemma tw0_1_6_20_calc (j : Fin 31) : taylorWaveBox 0 1 6 20 j = tw0_1_6_20 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorWave100
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw1_0_0_0_calc (j : Fin 31) : taylorWaveBox 1 0 0 0 j = tw1_0_0_0 j := by
  revert j
  decide +kernel
lemma tw1_0_0_10_calc (j : Fin 31) : taylorWaveBox 1 0 0 10 j = tw1_0_0_10 j := by
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
lemma ex1b0_calc (r : Fin 8) : bernsteinRowsBox 22 ex1r 0 r = ex1b0 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end


