-- Prove2me | Definitions.Def_OAIQ250T097
-- name    : OAIQ250T097
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T14:03:50.855305+00:00
-- url     : https://prove2.me/theorems/4f69eed4-06d8-4023-8599-3659d0ae0658
-- title:
--   Definitions bundle OAIQ250T097 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 46 declarations of OpenAI's Lean: 46 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Signs_ExceptionalSign1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/ExceptionalSign1.lean), [`Triangular_Taylor_TaylorWave113`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave113.lean), [`Triangular_Taylor_TaylorWave114`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave114.lean), [`Triangular_Taylor_TaylorWave115`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave115.lean), [`Triangular_Taylor_TaylorWave116`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave116.lean).
--
--   **Imports.** It imports the bundles `OAIQ250T016`, `OAIQ250T024`, `OAIQ250T077` and `OAIQ250T079` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ250T113`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ250T016
import Definitions.Def_OAIQ250T024
import Definitions.Def_OAIQ250T077
import Definitions.Def_OAIQ250T079

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorWave113
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw1_1_3_5_calc (j : Fin 31) : taylorWaveBox 1 1 3 5 j = tw1_1_3_5 j := by
  revert j
  decide +kernel
lemma tw1_1_3_6_calc (j : Fin 31) : taylorWaveBox 1 1 3 6 j = tw1_1_3_6 j := by
  revert j
  decide +kernel
lemma tw1_1_3_7_calc (j : Fin 31) : taylorWaveBox 1 1 3 7 j = tw1_1_3_7 j := by
  revert j
  decide +kernel
lemma tw1_1_3_8_calc (j : Fin 31) : taylorWaveBox 1 1 3 8 j = tw1_1_3_8 j := by
  revert j
  decide +kernel
lemma tw1_1_3_9_calc (j : Fin 31) : taylorWaveBox 1 1 3 9 j = tw1_1_3_9 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorWave114
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw1_1_4_0_calc (j : Fin 31) : taylorWaveBox 1 1 4 0 j = tw1_1_4_0 j := by
  revert j
  decide +kernel
lemma tw1_1_4_1_calc (j : Fin 31) : taylorWaveBox 1 1 4 1 j = tw1_1_4_1 j := by
  revert j
  decide +kernel
lemma tw1_1_4_2_calc (j : Fin 31) : taylorWaveBox 1 1 4 2 j = tw1_1_4_2 j := by
  revert j
  decide +kernel
lemma tw1_1_4_3_calc (j : Fin 31) : taylorWaveBox 1 1 4 3 j = tw1_1_4_3 j := by
  revert j
  decide +kernel
lemma tw1_1_4_4_calc (j : Fin 31) : taylorWaveBox 1 1 4 4 j = tw1_1_4_4 j := by
  revert j
  decide +kernel
lemma tw1_1_4_5_calc (j : Fin 31) : taylorWaveBox 1 1 4 5 j = tw1_1_4_5 j := by
  revert j
  decide +kernel
lemma tw1_1_4_6_calc (j : Fin 31) : taylorWaveBox 1 1 4 6 j = tw1_1_4_6 j := by
  revert j
  decide +kernel
lemma tw1_1_4_7_calc (j : Fin 31) : taylorWaveBox 1 1 4 7 j = tw1_1_4_7 j := by
  revert j
  decide +kernel
lemma tw1_1_4_8_calc (j : Fin 31) : taylorWaveBox 1 1 4 8 j = tw1_1_4_8 j := by
  revert j
  decide +kernel
lemma tw1_1_4_9_calc (j : Fin 31) : taylorWaveBox 1 1 4 9 j = tw1_1_4_9 j := by
  revert j
  decide +kernel
lemma tw1_1_4_10_calc (j : Fin 31) : taylorWaveBox 1 1 4 10 j = tw1_1_4_10 j := by
  revert j
  decide +kernel
lemma tw1_1_4_11_calc (j : Fin 31) : taylorWaveBox 1 1 4 11 j = tw1_1_4_11 j := by
  revert j
  decide +kernel
lemma tw1_1_4_12_calc (j : Fin 31) : taylorWaveBox 1 1 4 12 j = tw1_1_4_12 j := by
  revert j
  decide +kernel
lemma tw1_1_4_13_calc (j : Fin 31) : taylorWaveBox 1 1 4 13 j = tw1_1_4_13 j := by
  revert j
  decide +kernel
lemma tw1_1_4_14_calc (j : Fin 31) : taylorWaveBox 1 1 4 14 j = tw1_1_4_14 j := by
  revert j
  decide +kernel
lemma tw1_1_4_15_calc (j : Fin 31) : taylorWaveBox 1 1 4 15 j = tw1_1_4_15 j := by
  revert j
  decide +kernel
lemma tw1_1_4_16_calc (j : Fin 31) : taylorWaveBox 1 1 4 16 j = tw1_1_4_16 j := by
  revert j
  decide +kernel
lemma tw1_1_4_17_calc (j : Fin 31) : taylorWaveBox 1 1 4 17 j = tw1_1_4_17 j := by
  revert j
  decide +kernel
lemma tw1_1_4_18_calc (j : Fin 31) : taylorWaveBox 1 1 4 18 j = tw1_1_4_18 j := by
  revert j
  decide +kernel
lemma tw1_1_4_19_calc (j : Fin 31) : taylorWaveBox 1 1 4 19 j = tw1_1_4_19 j := by
  revert j
  decide +kernel
lemma tw1_1_4_20_calc (j : Fin 31) : taylorWaveBox 1 1 4 20 j = tw1_1_4_20 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorWave115
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw1_1_5_0_calc (j : Fin 31) : taylorWaveBox 1 1 5 0 j = tw1_1_5_0 j := by
  revert j
  decide +kernel
lemma tw1_1_5_1_calc (j : Fin 31) : taylorWaveBox 1 1 5 1 j = tw1_1_5_1 j := by
  revert j
  decide +kernel
lemma tw1_1_5_2_calc (j : Fin 31) : taylorWaveBox 1 1 5 2 j = tw1_1_5_2 j := by
  revert j
  decide +kernel
lemma tw1_1_5_3_calc (j : Fin 31) : taylorWaveBox 1 1 5 3 j = tw1_1_5_3 j := by
  revert j
  decide +kernel
lemma tw1_1_5_4_calc (j : Fin 31) : taylorWaveBox 1 1 5 4 j = tw1_1_5_4 j := by
  revert j
  decide +kernel
lemma tw1_1_5_5_calc (j : Fin 31) : taylorWaveBox 1 1 5 5 j = tw1_1_5_5 j := by
  revert j
  decide +kernel
lemma tw1_1_5_6_calc (j : Fin 31) : taylorWaveBox 1 1 5 6 j = tw1_1_5_6 j := by
  revert j
  decide +kernel
lemma tw1_1_5_10_calc (j : Fin 31) : taylorWaveBox 1 1 5 10 j = tw1_1_5_10 j := by
  revert j
  decide +kernel
lemma tw1_1_5_11_calc (j : Fin 31) : taylorWaveBox 1 1 5 11 j = tw1_1_5_11 j := by
  revert j
  decide +kernel
lemma tw1_1_5_12_calc (j : Fin 31) : taylorWaveBox 1 1 5 12 j = tw1_1_5_12 j := by
  revert j
  decide +kernel
lemma tw1_1_5_13_calc (j : Fin 31) : taylorWaveBox 1 1 5 13 j = tw1_1_5_13 j := by
  revert j
  decide +kernel
lemma tw1_1_5_14_calc (j : Fin 31) : taylorWaveBox 1 1 5 14 j = tw1_1_5_14 j := by
  revert j
  decide +kernel
lemma tw1_1_5_15_calc (j : Fin 31) : taylorWaveBox 1 1 5 15 j = tw1_1_5_15 j := by
  revert j
  decide +kernel
lemma tw1_1_5_16_calc (j : Fin 31) : taylorWaveBox 1 1 5 16 j = tw1_1_5_16 j := by
  revert j
  decide +kernel
lemma tw1_1_5_17_calc (j : Fin 31) : taylorWaveBox 1 1 5 17 j = tw1_1_5_17 j := by
  revert j
  decide +kernel
lemma tw1_1_5_18_calc (j : Fin 31) : taylorWaveBox 1 1 5 18 j = tw1_1_5_18 j := by
  revert j
  decide +kernel
lemma tw1_1_5_19_calc (j : Fin 31) : taylorWaveBox 1 1 5 19 j = tw1_1_5_19 j := by
  revert j
  decide +kernel
lemma tw1_1_5_20_calc (j : Fin 31) : taylorWaveBox 1 1 5 20 j = tw1_1_5_20 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorWave116
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw1_1_6_0_calc (j : Fin 31) : taylorWaveBox 1 1 6 0 j = tw1_1_6_0 j := by
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
lemma ex1b10_calc (r : Fin 8) : bernsteinRowsBox 22 ex1r 10 r = ex1b10 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end


