-- Prove2me | Definitions.Def_OAIQ250T153
-- name    : OAIQ250T153
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T14:06:07.81738+00:00
-- url     : https://prove2.me/theorems/f1531525-9bfa-43ed-bcd3-dfcc79856b9c
-- title:
--   Definitions bundle OAIQ250T153 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 25 declarations of OpenAI's Lean: 25 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Taylor_TaylorWave004`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave004.lean), [`Triangular_Taylor_TaylorWave005`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave005.lean).
--
--   **Imports.** It imports the bundles `OAIQ250T016` and `OAIQ250T077` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ250T113`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ250T016
import Definitions.Def_OAIQ250T077

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorWave004
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw0_0_4_1_calc (j : Fin 31) : taylorWaveBox 0 0 4 1 j = tw0_0_4_1 j := by
  revert j
  decide +kernel
lemma tw0_0_4_2_calc (j : Fin 31) : taylorWaveBox 0 0 4 2 j = tw0_0_4_2 j := by
  revert j
  decide +kernel
lemma tw0_0_4_3_calc (j : Fin 31) : taylorWaveBox 0 0 4 3 j = tw0_0_4_3 j := by
  revert j
  decide +kernel
lemma tw0_0_4_4_calc (j : Fin 31) : taylorWaveBox 0 0 4 4 j = tw0_0_4_4 j := by
  revert j
  decide +kernel
lemma tw0_0_4_5_calc (j : Fin 31) : taylorWaveBox 0 0 4 5 j = tw0_0_4_5 j := by
  revert j
  decide +kernel
lemma tw0_0_4_6_calc (j : Fin 31) : taylorWaveBox 0 0 4 6 j = tw0_0_4_6 j := by
  revert j
  decide +kernel
lemma tw0_0_4_7_calc (j : Fin 31) : taylorWaveBox 0 0 4 7 j = tw0_0_4_7 j := by
  revert j
  decide +kernel
lemma tw0_0_4_8_calc (j : Fin 31) : taylorWaveBox 0 0 4 8 j = tw0_0_4_8 j := by
  revert j
  decide +kernel
lemma tw0_0_4_9_calc (j : Fin 31) : taylorWaveBox 0 0 4 9 j = tw0_0_4_9 j := by
  revert j
  decide +kernel
lemma tw0_0_4_11_calc (j : Fin 31) : taylorWaveBox 0 0 4 11 j = tw0_0_4_11 j := by
  revert j
  decide +kernel
lemma tw0_0_4_12_calc (j : Fin 31) : taylorWaveBox 0 0 4 12 j = tw0_0_4_12 j := by
  revert j
  decide +kernel
lemma tw0_0_4_13_calc (j : Fin 31) : taylorWaveBox 0 0 4 13 j = tw0_0_4_13 j := by
  revert j
  decide +kernel
lemma tw0_0_4_14_calc (j : Fin 31) : taylorWaveBox 0 0 4 14 j = tw0_0_4_14 j := by
  revert j
  decide +kernel
lemma tw0_0_4_15_calc (j : Fin 31) : taylorWaveBox 0 0 4 15 j = tw0_0_4_15 j := by
  revert j
  decide +kernel
lemma tw0_0_4_16_calc (j : Fin 31) : taylorWaveBox 0 0 4 16 j = tw0_0_4_16 j := by
  revert j
  decide +kernel
lemma tw0_0_4_17_calc (j : Fin 31) : taylorWaveBox 0 0 4 17 j = tw0_0_4_17 j := by
  revert j
  decide +kernel
lemma tw0_0_4_18_calc (j : Fin 31) : taylorWaveBox 0 0 4 18 j = tw0_0_4_18 j := by
  revert j
  decide +kernel
lemma tw0_0_4_19_calc (j : Fin 31) : taylorWaveBox 0 0 4 19 j = tw0_0_4_19 j := by
  revert j
  decide +kernel
lemma tw0_0_4_20_calc (j : Fin 31) : taylorWaveBox 0 0 4 20 j = tw0_0_4_20 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorWave005
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw0_0_5_0_calc (j : Fin 31) : taylorWaveBox 0 0 5 0 j = tw0_0_5_0 j := by
  revert j
  decide +kernel
lemma tw0_0_5_10_calc (j : Fin 31) : taylorWaveBox 0 0 5 10 j = tw0_0_5_10 j := by
  revert j
  decide +kernel
lemma tw0_0_5_11_calc (j : Fin 31) : taylorWaveBox 0 0 5 11 j = tw0_0_5_11 j := by
  revert j
  decide +kernel
lemma tw0_0_5_12_calc (j : Fin 31) : taylorWaveBox 0 0 5 12 j = tw0_0_5_12 j := by
  revert j
  decide +kernel
lemma tw0_0_5_13_calc (j : Fin 31) : taylorWaveBox 0 0 5 13 j = tw0_0_5_13 j := by
  revert j
  decide +kernel
lemma tw0_0_5_14_calc (j : Fin 31) : taylorWaveBox 0 0 5 14 j = tw0_0_5_14 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end


