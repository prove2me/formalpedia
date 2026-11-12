-- Prove2me | Definitions.Def_OAIQ250T093
-- name    : OAIQ250T093
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T14:16:13.55923+00:00
-- url     : https://prove2.me/theorems/f19a0c43-4db8-4c55-90c1-59cd6c2e765b
-- title:
--   Definitions bundle OAIQ250T093 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 30 declarations of OpenAI's Lean: 1 definition and 29 theorems. The definitions and types are `OAI.AtomicTriangular.Construction.ordinarySignRow`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Signs_ExceptionalSign1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/ExceptionalSign1.lean), [`Triangular_Signs_SignBase`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/SignBase.lean), [`Triangular_Taylor_TaylorWave101`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave101.lean), [`Triangular_Taylor_TaylorWave102`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave102.lean).
--
--   **Imports.** It imports the bundles `OAIQ250T021`, `OAIQ250T022`, `OAIQ250T051`, `OAIQ250T077` and `OAIQ250T079` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ250T108`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ250T021
import Definitions.Def_OAIQ250T022
import Definitions.Def_OAIQ250T051
import Definitions.Def_OAIQ250T077
import Definitions.Def_OAIQ250T079

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorWave101
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw1_0_1_1_calc (j : Fin 31) : taylorWaveBox 1 0 1 1 j = tw1_0_1_1 j := by
  revert j
  decide +kernel
lemma tw1_0_1_2_calc (j : Fin 31) : taylorWaveBox 1 0 1 2 j = tw1_0_1_2 j := by
  revert j
  decide +kernel
lemma tw1_0_1_3_calc (j : Fin 31) : taylorWaveBox 1 0 1 3 j = tw1_0_1_3 j := by
  revert j
  decide +kernel
lemma tw1_0_1_4_calc (j : Fin 31) : taylorWaveBox 1 0 1 4 j = tw1_0_1_4 j := by
  revert j
  decide +kernel
lemma tw1_0_1_5_calc (j : Fin 31) : taylorWaveBox 1 0 1 5 j = tw1_0_1_5 j := by
  revert j
  decide +kernel
lemma tw1_0_1_6_calc (j : Fin 31) : taylorWaveBox 1 0 1 6 j = tw1_0_1_6 j := by
  revert j
  decide +kernel
lemma tw1_0_1_7_calc (j : Fin 31) : taylorWaveBox 1 0 1 7 j = tw1_0_1_7 j := by
  revert j
  decide +kernel
lemma tw1_0_1_8_calc (j : Fin 31) : taylorWaveBox 1 0 1 8 j = tw1_0_1_8 j := by
  revert j
  decide +kernel
lemma tw1_0_1_9_calc (j : Fin 31) : taylorWaveBox 1 0 1 9 j = tw1_0_1_9 j := by
  revert j
  decide +kernel
lemma tw1_0_1_12_calc (j : Fin 31) : taylorWaveBox 1 0 1 12 j = tw1_0_1_12 j := by
  revert j
  decide +kernel
lemma tw1_0_1_13_calc (j : Fin 31) : taylorWaveBox 1 0 1 13 j = tw1_0_1_13 j := by
  revert j
  decide +kernel
lemma tw1_0_1_14_calc (j : Fin 31) : taylorWaveBox 1 0 1 14 j = tw1_0_1_14 j := by
  revert j
  decide +kernel
lemma tw1_0_1_15_calc (j : Fin 31) : taylorWaveBox 1 0 1 15 j = tw1_0_1_15 j := by
  revert j
  decide +kernel
lemma tw1_0_1_16_calc (j : Fin 31) : taylorWaveBox 1 0 1 16 j = tw1_0_1_16 j := by
  revert j
  decide +kernel
lemma tw1_0_1_17_calc (j : Fin 31) : taylorWaveBox 1 0 1 17 j = tw1_0_1_17 j := by
  revert j
  decide +kernel
lemma tw1_0_1_18_calc (j : Fin 31) : taylorWaveBox 1 0 1 18 j = tw1_0_1_18 j := by
  revert j
  decide +kernel
lemma tw1_0_1_19_calc (j : Fin 31) : taylorWaveBox 1 0 1 19 j = tw1_0_1_19 j := by
  revert j
  decide +kernel
lemma tw1_0_1_20_calc (j : Fin 31) : taylorWaveBox 1 0 1 20 j = tw1_0_1_20 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorWave102
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw1_0_2_0_calc (j : Fin 31) : taylorWaveBox 1 0 2 0 j = tw1_0_2_0 j := by
  revert j
  decide +kernel
lemma tw1_0_2_10_calc (j : Fin 31) : taylorWaveBox 1 0 2 10 j = tw1_0_2_10 j := by
  revert j
  decide +kernel
lemma tw1_0_2_11_calc (j : Fin 31) : taylorWaveBox 1 0 2 11 j = tw1_0_2_11 j := by
  revert j
  decide +kernel
lemma tw1_0_2_12_calc (j : Fin 31) : taylorWaveBox 1 0 2 12 j = tw1_0_2_12 j := by
  revert j
  decide +kernel
lemma tw1_0_2_13_calc (j : Fin 31) : taylorWaveBox 1 0 2 13 j = tw1_0_2_13 j := by
  revert j
  decide +kernel
lemma tw1_0_2_14_calc (j : Fin 31) : taylorWaveBox 1 0 2 14 j = tw1_0_2_14 j := by
  revert j
  decide +kernel
lemma tw1_0_2_15_calc (j : Fin 31) : taylorWaveBox 1 0 2 15 j = tw1_0_2_15 j := by
  revert j
  decide +kernel
lemma tw1_0_2_16_calc (j : Fin 31) : taylorWaveBox 1 0 2 16 j = tw1_0_2_16 j := by
  revert j
  decide +kernel
lemma tw1_0_2_17_calc (j : Fin 31) : taylorWaveBox 1 0 2 17 j = tw1_0_2_17 j := by
  revert j
  decide +kernel
lemma tw1_0_2_18_calc (j : Fin 31) : taylorWaveBox 1 0 2 18 j = tw1_0_2_18 j := by
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
lemma ex1b12_calc (r : Fin 8) : bernsteinRowsBox 22 ex1r 12 r = ex1b12 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_SignBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate

def ordinarySignRow (side : Fin 2) (n : Fin 7) (y : Fin 2) (l : Fin 21) (r : Fin 8) : ℝ :=
  if side.val=0 then (if l.val=0 then ordinaryOffset n r else 0) -
    taylorRow side (nearNode n) (nearDisplacement n y) l.val r
  else taylorRow side (nearNode n) (nearDisplacement n y) l.val r
end AtomicTriangular.Construction
end

end OAI
end


