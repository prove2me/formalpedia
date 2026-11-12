-- Prove2me | Definitions.Def_OAIQ262T174
-- name    : OAIQ262T174
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T18:12:49.598195+00:00
-- url     : https://prove2.me/theorems/1a17850c-7be7-4c01-b52b-ffa0f36e659e
-- title:
--   Definitions bundle OAIQ262T174 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 27 declarations of OpenAI's Lean: 27 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Signs_Signs11`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/Signs11.lean), [`Triangular_Taylor_TaylorWave016`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave016.lean), [`Triangular_Taylor_TaylorWave100`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave100.lean), [`Triangular_Taylor_TaylorWave101`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave101.lean).
--
--   **Imports.** It imports the bundles `OAIQ262T050`, `OAIQ262T105`, `OAIQ262T147` and `OAIQ262T148` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ262T261`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ262T050
import Definitions.Def_OAIQ262T105
import Definitions.Def_OAIQ262T147
import Definitions.Def_OAIQ262T148

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave016
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw0_1_6_7_calc (j : Fin 31) : taylorWaveBox 0 1 6 7 j = tw0_1_6_7 j := by
  revert j
  decide +kernel
lemma tw0_1_6_8_calc (j : Fin 31) : taylorWaveBox 0 1 6 8 j = tw0_1_6_8 j := by
  revert j
  decide +kernel
lemma tw0_1_6_9_calc (j : Fin 31) : taylorWaveBox 0 1 6 9 j = tw0_1_6_9 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave100
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
lemma tw1_0_0_1_calc (j : Fin 31) : taylorWaveBox 1 0 0 1 j = tw1_0_0_1 j := by
  revert j
  decide +kernel
lemma tw1_0_0_2_calc (j : Fin 31) : taylorWaveBox 1 0 0 2 j = tw1_0_0_2 j := by
  revert j
  decide +kernel
lemma tw1_0_0_3_calc (j : Fin 31) : taylorWaveBox 1 0 0 3 j = tw1_0_0_3 j := by
  revert j
  decide +kernel
lemma tw1_0_0_4_calc (j : Fin 31) : taylorWaveBox 1 0 0 4 j = tw1_0_0_4 j := by
  revert j
  decide +kernel
lemma tw1_0_0_5_calc (j : Fin 31) : taylorWaveBox 1 0 0 5 j = tw1_0_0_5 j := by
  revert j
  decide +kernel
lemma tw1_0_0_6_calc (j : Fin 31) : taylorWaveBox 1 0 0 6 j = tw1_0_0_6 j := by
  revert j
  decide +kernel
lemma tw1_0_0_7_calc (j : Fin 31) : taylorWaveBox 1 0 0 7 j = tw1_0_0_7 j := by
  revert j
  decide +kernel
lemma tw1_0_0_8_calc (j : Fin 31) : taylorWaveBox 1 0 0 8 j = tw1_0_0_8 j := by
  revert j
  decide +kernel
lemma tw1_0_0_9_calc (j : Fin 31) : taylorWaveBox 1 0 0 9 j = tw1_0_0_9 j := by
  revert j
  decide +kernel
lemma tw1_0_0_10_calc (j : Fin 31) : taylorWaveBox 1 0 0 10 j = tw1_0_0_10 j := by
  revert j
  decide +kernel
lemma tw1_0_0_12_calc (j : Fin 31) : taylorWaveBox 1 0 0 12 j = tw1_0_0_12 j := by
  revert j
  decide +kernel
lemma tw1_0_0_13_calc (j : Fin 31) : taylorWaveBox 1 0 0 13 j = tw1_0_0_13 j := by
  revert j
  decide +kernel
lemma tw1_0_0_14_calc (j : Fin 31) : taylorWaveBox 1 0 0 14 j = tw1_0_0_14 j := by
  revert j
  decide +kernel
lemma tw1_0_0_15_calc (j : Fin 31) : taylorWaveBox 1 0 0 15 j = tw1_0_0_15 j := by
  revert j
  decide +kernel
lemma tw1_0_0_16_calc (j : Fin 31) : taylorWaveBox 1 0 0 16 j = tw1_0_0_16 j := by
  revert j
  decide +kernel
lemma tw1_0_0_17_calc (j : Fin 31) : taylorWaveBox 1 0 0 17 j = tw1_0_0_17 j := by
  revert j
  decide +kernel
lemma tw1_0_0_18_calc (j : Fin 31) : taylorWaveBox 1 0 0 18 j = tw1_0_0_18 j := by
  revert j
  decide +kernel
lemma tw1_0_0_19_calc (j : Fin 31) : taylorWaveBox 1 0 0 19 j = tw1_0_0_19 j := by
  revert j
  decide +kernel
lemma tw1_0_0_20_calc (j : Fin 31) : taylorWaveBox 1 0 0 20 j = tw1_0_0_20 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave101
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw1_0_1_0_calc (j : Fin 31) : taylorWaveBox 1 0 1 0 j = tw1_0_1_0 j := by
  revert j
  decide +kernel
lemma tw1_0_1_10_calc (j : Fin 31) : taylorWaveBox 1 0 1 10 j = tw1_0_1_10 j := by
  revert j
  decide +kernel
lemma tw1_0_1_11_calc (j : Fin 31) : taylorWaveBox 1 0 1 11 j = tw1_0_1_11 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_Signs11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma bs1_1_0_0_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 1 tr1_1_0) 0 r = bs1_1_0_0 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end


