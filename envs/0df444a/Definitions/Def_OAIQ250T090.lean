-- Prove2me | Definitions.Def_OAIQ250T090
-- name    : OAIQ250T090
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T14:03:03.558787+00:00
-- url     : https://prove2.me/theorems/47a160a6-c283-4bcb-b4c7-87b4a1f9bd58
-- title:
--   Definitions bundle OAIQ250T090 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 31 declarations of OpenAI's Lean: 31 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Signs_ExceptionalSign1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/ExceptionalSign1.lean), [`Triangular_Taylor_TaylorWave010`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave010.lean), [`Triangular_Taylor_TaylorWave011`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave011.lean).
--
--   **Imports.** It imports the bundles `OAIQ250T017`, `OAIQ250T018`, `OAIQ250T019`, `OAIQ250T024`, `OAIQ250T077` and `OAIQ250T079` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ250T113`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ250T017
import Definitions.Def_OAIQ250T018
import Definitions.Def_OAIQ250T019
import Definitions.Def_OAIQ250T024
import Definitions.Def_OAIQ250T077
import Definitions.Def_OAIQ250T079

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
lemma tw0_1_0_3_calc (j : Fin 31) : taylorWaveBox 0 1 0 3 j = tw0_1_0_3 j := by
  revert j
  decide +kernel
lemma tw0_1_0_4_calc (j : Fin 31) : taylorWaveBox 0 1 0 4 j = tw0_1_0_4 j := by
  revert j
  decide +kernel
lemma tw0_1_0_5_calc (j : Fin 31) : taylorWaveBox 0 1 0 5 j = tw0_1_0_5 j := by
  revert j
  decide +kernel
lemma tw0_1_0_6_calc (j : Fin 31) : taylorWaveBox 0 1 0 6 j = tw0_1_0_6 j := by
  revert j
  decide +kernel
lemma tw0_1_0_7_calc (j : Fin 31) : taylorWaveBox 0 1 0 7 j = tw0_1_0_7 j := by
  revert j
  decide +kernel
lemma tw0_1_0_8_calc (j : Fin 31) : taylorWaveBox 0 1 0 8 j = tw0_1_0_8 j := by
  revert j
  decide +kernel
lemma tw0_1_0_9_calc (j : Fin 31) : taylorWaveBox 0 1 0 9 j = tw0_1_0_9 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorWave011
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw0_1_1_0_calc (j : Fin 31) : taylorWaveBox 0 1 1 0 j = tw0_1_1_0 j := by
  revert j
  decide +kernel
lemma tw0_1_1_1_calc (j : Fin 31) : taylorWaveBox 0 1 1 1 j = tw0_1_1_1 j := by
  revert j
  decide +kernel
lemma tw0_1_1_2_calc (j : Fin 31) : taylorWaveBox 0 1 1 2 j = tw0_1_1_2 j := by
  revert j
  decide +kernel
lemma tw0_1_1_3_calc (j : Fin 31) : taylorWaveBox 0 1 1 3 j = tw0_1_1_3 j := by
  revert j
  decide +kernel
lemma tw0_1_1_4_calc (j : Fin 31) : taylorWaveBox 0 1 1 4 j = tw0_1_1_4 j := by
  revert j
  decide +kernel
lemma tw0_1_1_5_calc (j : Fin 31) : taylorWaveBox 0 1 1 5 j = tw0_1_1_5 j := by
  revert j
  decide +kernel
lemma tw0_1_1_6_calc (j : Fin 31) : taylorWaveBox 0 1 1 6 j = tw0_1_1_6 j := by
  revert j
  decide +kernel
lemma tw0_1_1_7_calc (j : Fin 31) : taylorWaveBox 0 1 1 7 j = tw0_1_1_7 j := by
  revert j
  decide +kernel
lemma tw0_1_1_8_calc (j : Fin 31) : taylorWaveBox 0 1 1 8 j = tw0_1_1_8 j := by
  revert j
  decide +kernel
lemma tw0_1_1_9_calc (j : Fin 31) : taylorWaveBox 0 1 1 9 j = tw0_1_1_9 j := by
  revert j
  decide +kernel
lemma tw0_1_1_10_calc (j : Fin 31) : taylorWaveBox 0 1 1 10 j = tw0_1_1_10 j := by
  revert j
  decide +kernel
lemma tw0_1_1_11_calc (j : Fin 31) : taylorWaveBox 0 1 1 11 j = tw0_1_1_11 j := by
  revert j
  decide +kernel
lemma tw0_1_1_12_calc (j : Fin 31) : taylorWaveBox 0 1 1 12 j = tw0_1_1_12 j := by
  revert j
  decide +kernel
lemma tw0_1_1_13_calc (j : Fin 31) : taylorWaveBox 0 1 1 13 j = tw0_1_1_13 j := by
  revert j
  decide +kernel
lemma tw0_1_1_14_calc (j : Fin 31) : taylorWaveBox 0 1 1 14 j = tw0_1_1_14 j := by
  revert j
  decide +kernel
lemma tw0_1_1_15_calc (j : Fin 31) : taylorWaveBox 0 1 1 15 j = tw0_1_1_15 j := by
  revert j
  decide +kernel
lemma tw0_1_1_16_calc (j : Fin 31) : taylorWaveBox 0 1 1 16 j = tw0_1_1_16 j := by
  revert j
  decide +kernel
lemma tw0_1_1_17_calc (j : Fin 31) : taylorWaveBox 0 1 1 17 j = tw0_1_1_17 j := by
  revert j
  decide +kernel
lemma tw0_1_1_18_calc (j : Fin 31) : taylorWaveBox 0 1 1 18 j = tw0_1_1_18 j := by
  revert j
  decide +kernel
lemma tw0_1_1_19_calc (j : Fin 31) : taylorWaveBox 0 1 1 19 j = tw0_1_1_19 j := by
  revert j
  decide +kernel
lemma tw0_1_1_20_calc (j : Fin 31) : taylorWaveBox 0 1 1 20 j = tw0_1_1_20 j := by
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
lemma ex1b2_calc (r : Fin 8) : bernsteinRowsBox 22 ex1r 2 r = ex1b2 r := by
  revert r
  decide +kernel
lemma ex1b3_calc (r : Fin 8) : bernsteinRowsBox 22 ex1r 3 r = ex1b3 r := by
  revert r
  decide +kernel
lemma ex1b22_calc (r : Fin 8) : bernsteinRowsBox 22 ex1r 22 r = ex1b22 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end


