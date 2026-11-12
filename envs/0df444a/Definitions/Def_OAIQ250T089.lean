-- Prove2me | Definitions.Def_OAIQ250T089
-- name    : OAIQ250T089
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T14:06:12.465828+00:00
-- url     : https://prove2.me/theorems/11ccf4e9-e5ff-44ea-9a17-64ca704c54a3
-- title:
--   Definitions bundle OAIQ250T089 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 31 declarations of OpenAI's Lean: 1 definition and 30 theorems. The definitions and types are `OAI.AtomicTriangular.Construction.ordinarySignValue`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Signs_ExceptionalSign1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/ExceptionalSign1.lean), [`Triangular_Signs_SignBase`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/SignBase.lean), [`Triangular_Taylor_TaylorWave005`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave005.lean), [`Triangular_Taylor_TaylorWave006`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave006.lean).
--
--   **Imports.** It imports the bundles `OAIQ250T016`, `OAIQ250T017`, `OAIQ250T023`, `OAIQ250T051`, `OAIQ250T077` and `OAIQ250T079` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ250T108`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ250T016
import Definitions.Def_OAIQ250T017
import Definitions.Def_OAIQ250T023
import Definitions.Def_OAIQ250T051
import Definitions.Def_OAIQ250T077
import Definitions.Def_OAIQ250T079

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
lemma tw0_0_5_1_calc (j : Fin 31) : taylorWaveBox 0 0 5 1 j = tw0_0_5_1 j := by
  revert j
  decide +kernel
lemma tw0_0_5_2_calc (j : Fin 31) : taylorWaveBox 0 0 5 2 j = tw0_0_5_2 j := by
  revert j
  decide +kernel
lemma tw0_0_5_3_calc (j : Fin 31) : taylorWaveBox 0 0 5 3 j = tw0_0_5_3 j := by
  revert j
  decide +kernel
lemma tw0_0_5_4_calc (j : Fin 31) : taylorWaveBox 0 0 5 4 j = tw0_0_5_4 j := by
  revert j
  decide +kernel
lemma tw0_0_5_5_calc (j : Fin 31) : taylorWaveBox 0 0 5 5 j = tw0_0_5_5 j := by
  revert j
  decide +kernel
lemma tw0_0_5_6_calc (j : Fin 31) : taylorWaveBox 0 0 5 6 j = tw0_0_5_6 j := by
  revert j
  decide +kernel
lemma tw0_0_5_7_calc (j : Fin 31) : taylorWaveBox 0 0 5 7 j = tw0_0_5_7 j := by
  revert j
  decide +kernel
lemma tw0_0_5_8_calc (j : Fin 31) : taylorWaveBox 0 0 5 8 j = tw0_0_5_8 j := by
  revert j
  decide +kernel
lemma tw0_0_5_9_calc (j : Fin 31) : taylorWaveBox 0 0 5 9 j = tw0_0_5_9 j := by
  revert j
  decide +kernel
lemma tw0_0_5_15_calc (j : Fin 31) : taylorWaveBox 0 0 5 15 j = tw0_0_5_15 j := by
  revert j
  decide +kernel
lemma tw0_0_5_16_calc (j : Fin 31) : taylorWaveBox 0 0 5 16 j = tw0_0_5_16 j := by
  revert j
  decide +kernel
lemma tw0_0_5_17_calc (j : Fin 31) : taylorWaveBox 0 0 5 17 j = tw0_0_5_17 j := by
  revert j
  decide +kernel
lemma tw0_0_5_18_calc (j : Fin 31) : taylorWaveBox 0 0 5 18 j = tw0_0_5_18 j := by
  revert j
  decide +kernel
lemma tw0_0_5_19_calc (j : Fin 31) : taylorWaveBox 0 0 5 19 j = tw0_0_5_19 j := by
  revert j
  decide +kernel
lemma tw0_0_5_20_calc (j : Fin 31) : taylorWaveBox 0 0 5 20 j = tw0_0_5_20 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorWave006
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw0_0_6_0_calc (j : Fin 31) : taylorWaveBox 0 0 6 0 j = tw0_0_6_0 j := by
  revert j
  decide +kernel
lemma tw0_0_6_1_calc (j : Fin 31) : taylorWaveBox 0 0 6 1 j = tw0_0_6_1 j := by
  revert j
  decide +kernel
lemma tw0_0_6_10_calc (j : Fin 31) : taylorWaveBox 0 0 6 10 j = tw0_0_6_10 j := by
  revert j
  decide +kernel
lemma tw0_0_6_11_calc (j : Fin 31) : taylorWaveBox 0 0 6 11 j = tw0_0_6_11 j := by
  revert j
  decide +kernel
lemma tw0_0_6_12_calc (j : Fin 31) : taylorWaveBox 0 0 6 12 j = tw0_0_6_12 j := by
  revert j
  decide +kernel
lemma tw0_0_6_13_calc (j : Fin 31) : taylorWaveBox 0 0 6 13 j = tw0_0_6_13 j := by
  revert j
  decide +kernel
lemma tw0_0_6_14_calc (j : Fin 31) : taylorWaveBox 0 0 6 14 j = tw0_0_6_14 j := by
  revert j
  decide +kernel
lemma tw0_0_6_15_calc (j : Fin 31) : taylorWaveBox 0 0 6 15 j = tw0_0_6_15 j := by
  revert j
  decide +kernel
lemma tw0_0_6_16_calc (j : Fin 31) : taylorWaveBox 0 0 6 16 j = tw0_0_6_16 j := by
  revert j
  decide +kernel
lemma tw0_0_6_17_calc (j : Fin 31) : taylorWaveBox 0 0 6 17 j = tw0_0_6_17 j := by
  revert j
  decide +kernel
lemma tw0_0_6_18_calc (j : Fin 31) : taylorWaveBox 0 0 6 18 j = tw0_0_6_18 j := by
  revert j
  decide +kernel
lemma tw0_0_6_19_calc (j : Fin 31) : taylorWaveBox 0 0 6 19 j = tw0_0_6_19 j := by
  revert j
  decide +kernel
lemma tw0_0_6_20_calc (j : Fin 31) : taylorWaveBox 0 0 6 20 j = tw0_0_6_20 j := by
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
lemma ex1b15_calc (r : Fin 8) : bernsteinRowsBox 22 ex1r 15 r = ex1b15 r := by
  revert r
  decide +kernel
lemma ex1b16_calc (r : Fin 8) : bernsteinRowsBox 22 ex1r 16 r = ex1b16 r := by
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

def ordinarySignValue (side : Fin 2) (n : Fin 7) (y : Fin 2) (e : Fin 8 → ℝ) (τ : ℝ) : ℝ :=
  if side.val=0 then (∑ r : Fin 8, ordinaryOffset n r*e r) -
    finiteTaylor side (nearNode n) (nearDisplacement n y) e τ
  else finiteTaylor side (nearNode n) (nearDisplacement n y) e τ
end AtomicTriangular.Construction
end

end OAI
end


