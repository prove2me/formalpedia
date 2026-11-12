-- Prove2me | Definitions.Def_OAIQ262T180
-- name    : OAIQ262T180
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T18:18:11.423526+00:00
-- url     : https://prove2.me/theorems/fb36ddec-d85e-495a-91d5-f65ba5c07c68
-- title:
--   Definitions bundle OAIQ262T180 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 27 declarations of OpenAI's Lean: 27 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Signs_SignBase`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/SignBase.lean), [`Triangular_Taylor_TaylorWave110`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave110.lean), [`Triangular_Taylor_TaylorWave111`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave111.lean).
--
--   **Imports.** It imports the bundles `OAIQ262T144`, `OAIQ262T147`, `OAIQ262T148` and `OAIQ262T149` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ262T261`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ262T144
import Definitions.Def_OAIQ262T147
import Definitions.Def_OAIQ262T148
import Definitions.Def_OAIQ262T149

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave110
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
lemma tw1_1_0_20_calc (j : Fin 31) : taylorWaveBox 1 1 0 20 j = tw1_1_0_20 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave111
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
lemma tw1_1_1_1_calc (j : Fin 31) : taylorWaveBox 1 1 1 1 j = tw1_1_1_1 j := by
  revert j
  decide +kernel
lemma tw1_1_1_2_calc (j : Fin 31) : taylorWaveBox 1 1 1 2 j = tw1_1_1_2 j := by
  revert j
  decide +kernel
lemma tw1_1_1_3_calc (j : Fin 31) : taylorWaveBox 1 1 1 3 j = tw1_1_1_3 j := by
  revert j
  decide +kernel
lemma tw1_1_1_4_calc (j : Fin 31) : taylorWaveBox 1 1 1 4 j = tw1_1_1_4 j := by
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
lemma tw1_1_1_15_calc (j : Fin 31) : taylorWaveBox 1 1 1 15 j = tw1_1_1_15 j := by
  revert j
  decide +kernel
lemma tw1_1_1_16_calc (j : Fin 31) : taylorWaveBox 1 1 1 16 j = tw1_1_1_16 j := by
  revert j
  decide +kernel
lemma tw1_1_1_17_calc (j : Fin 31) : taylorWaveBox 1 1 1 17 j = tw1_1_1_17 j := by
  revert j
  decide +kernel
lemma tw1_1_1_18_calc (j : Fin 31) : taylorWaveBox 1 1 1 18 j = tw1_1_1_18 j := by
  revert j
  decide +kernel
lemma tw1_1_1_19_calc (j : Fin 31) : taylorWaveBox 1 1 1 19 j = tw1_1_1_19 j := by
  revert j
  decide +kernel
lemma tw1_1_1_20_calc (j : Fin 31) : taylorWaveBox 1 1 1 20 j = tw1_1_1_20 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_SignBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma ordinarySignRowBox_mem (side : Fin 2) (n : Fin 7) (y : Fin 2)
    {a : Fin 21 → Fin 8 → RI}
    (ha : ∀ l r, (a l r).Mem (taylorRow side (nearNode n) (nearDisplacement n y) l.val r))
    (l : Fin 21) (r : Fin 8) :
    (ordinarySignRowBox side n a l r).Mem (ordinarySignRow side n y l r) := by
  unfold ordinarySignRowBox ordinarySignRow
  split_ifs
  · exact RI.mem_sub (ordinaryOffsetBox_mem n r) (ha l r)
  · exact RI.mem_sub (by simpa using RI.mem_point 0) (ha l r)
  · exact ha l r
end AtomicTriangular.FiniteCertificate
end

end OAI
end


