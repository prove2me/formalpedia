-- Prove2me | Definitions.Def_OAIQ250T179
-- name    : OAIQ250T179
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T14:09:54.396173+00:00
-- url     : https://prove2.me/theorems/8dc9aaf2-443d-4c19-84ed-2ecb5a8a6413
-- title:
--   Definitions bundle OAIQ250T179 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 21 declarations of OpenAI's Lean: 21 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Taylor_TaylorWave110`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave110.lean), [`Triangular_Taylor_TaylorWave111`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave111.lean).
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
lemma tw1_1_0_1_calc (j : Fin 31) : taylorWaveBox 1 1 0 1 j = tw1_1_0_1 j := by
  revert j
  decide +kernel
lemma tw1_1_0_2_calc (j : Fin 31) : taylorWaveBox 1 1 0 2 j = tw1_1_0_2 j := by
  revert j
  decide +kernel
lemma tw1_1_0_3_calc (j : Fin 31) : taylorWaveBox 1 1 0 3 j = tw1_1_0_3 j := by
  revert j
  decide +kernel
lemma tw1_1_0_4_calc (j : Fin 31) : taylorWaveBox 1 1 0 4 j = tw1_1_0_4 j := by
  revert j
  decide +kernel
lemma tw1_1_0_5_calc (j : Fin 31) : taylorWaveBox 1 1 0 5 j = tw1_1_0_5 j := by
  revert j
  decide +kernel
lemma tw1_1_0_6_calc (j : Fin 31) : taylorWaveBox 1 1 0 6 j = tw1_1_0_6 j := by
  revert j
  decide +kernel
lemma tw1_1_0_7_calc (j : Fin 31) : taylorWaveBox 1 1 0 7 j = tw1_1_0_7 j := by
  revert j
  decide +kernel
lemma tw1_1_0_8_calc (j : Fin 31) : taylorWaveBox 1 1 0 8 j = tw1_1_0_8 j := by
  revert j
  decide +kernel
lemma tw1_1_0_9_calc (j : Fin 31) : taylorWaveBox 1 1 0 9 j = tw1_1_0_9 j := by
  revert j
  decide +kernel
lemma tw1_1_0_15_calc (j : Fin 31) : taylorWaveBox 1 1 0 15 j = tw1_1_0_15 j := by
  revert j
  decide +kernel
lemma tw1_1_0_16_calc (j : Fin 31) : taylorWaveBox 1 1 0 16 j = tw1_1_0_16 j := by
  revert j
  decide +kernel
lemma tw1_1_0_17_calc (j : Fin 31) : taylorWaveBox 1 1 0 17 j = tw1_1_0_17 j := by
  revert j
  decide +kernel
lemma tw1_1_0_18_calc (j : Fin 31) : taylorWaveBox 1 1 0 18 j = tw1_1_0_18 j := by
  revert j
  decide +kernel
lemma tw1_1_0_19_calc (j : Fin 31) : taylorWaveBox 1 1 0 19 j = tw1_1_0_19 j := by
  revert j
  decide +kernel
lemma tw1_1_0_20_calc (j : Fin 31) : taylorWaveBox 1 1 0 20 j = tw1_1_0_20 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorWave111
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw1_1_1_0_calc (j : Fin 31) : taylorWaveBox 1 1 1 0 j = tw1_1_1_0 j := by
  revert j
  decide +kernel
lemma tw1_1_1_10_calc (j : Fin 31) : taylorWaveBox 1 1 1 10 j = tw1_1_1_10 j := by
  revert j
  decide +kernel
lemma tw1_1_1_11_calc (j : Fin 31) : taylorWaveBox 1 1 1 11 j = tw1_1_1_11 j := by
  revert j
  decide +kernel
lemma tw1_1_1_12_calc (j : Fin 31) : taylorWaveBox 1 1 1 12 j = tw1_1_1_12 j := by
  revert j
  decide +kernel
lemma tw1_1_1_13_calc (j : Fin 31) : taylorWaveBox 1 1 1 13 j = tw1_1_1_13 j := by
  revert j
  decide +kernel
lemma tw1_1_1_14_calc (j : Fin 31) : taylorWaveBox 1 1 1 14 j = tw1_1_1_14 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end


