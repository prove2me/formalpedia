-- Prove2me | Definitions.Def_OAIQ250T091
-- name    : OAIQ250T091
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T14:04:18.921809+00:00
-- url     : https://prove2.me/theorems/7b98b0d4-32c0-46a5-898c-f4cfeb1fc3e9
-- title:
--   Definitions bundle OAIQ250T091 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 33 declarations of OpenAI's Lean: 1 definition and 32 theorems. The definitions and types are `OAI.AtomicTriangular.FiniteCertificate.ordinarySignRowBox`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Signs_ExceptionalSign1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/ExceptionalSign1.lean), [`Triangular_Signs_SignBase`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/SignBase.lean), [`Triangular_Taylor_TaylorWave013`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave013.lean), [`Triangular_Taylor_TaylorWave014`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave014.lean).
--
--   **Imports.** It imports the bundles `OAIQ250T018`, `OAIQ250T019`, `OAIQ250T023`, `OAIQ250T024`, `OAIQ250T052`, `OAIQ250T077` and `OAIQ250T079` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ250T108`, `OAIQ250T109`, `OAIQ250T110` and `OAIQ250T111`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ250T018
import Definitions.Def_OAIQ250T019
import Definitions.Def_OAIQ250T023
import Definitions.Def_OAIQ250T024
import Definitions.Def_OAIQ250T052
import Definitions.Def_OAIQ250T077
import Definitions.Def_OAIQ250T079

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorWave013
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
lemma tw0_1_3_13_calc (j : Fin 31) : taylorWaveBox 0 1 3 13 j = tw0_1_3_13 j := by
  revert j
  decide +kernel
lemma tw0_1_3_14_calc (j : Fin 31) : taylorWaveBox 0 1 3 14 j = tw0_1_3_14 j := by
  revert j
  decide +kernel
lemma tw0_1_3_15_calc (j : Fin 31) : taylorWaveBox 0 1 3 15 j = tw0_1_3_15 j := by
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
lemma tw0_1_3_19_calc (j : Fin 31) : taylorWaveBox 0 1 3 19 j = tw0_1_3_19 j := by
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
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorWave014
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
lemma ex1b17_calc (r : Fin 8) : bernsteinRowsBox 22 ex1r 17 r = ex1b17 r := by
  revert r
  decide +kernel
lemma ex1b18_calc (r : Fin 8) : bernsteinRowsBox 22 ex1r 18 r = ex1b18 r := by
  revert r
  decide +kernel
lemma ex1b19_calc (r : Fin 8) : bernsteinRowsBox 22 ex1r 19 r = ex1b19 r := by
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
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

def ordinarySignRowBox (side : Fin 2) (n : Fin 7) (a : Fin 21 → Fin 8 → RI)
    (l : Fin 21) (r : Fin 8) : RI :=
  if side.val=0 then ((if l.val=0 then ordinaryOffsetBox n r else RI.point 0).sub (a l r)) else a l r
end AtomicTriangular.FiniteCertificate
end

end OAI
end


