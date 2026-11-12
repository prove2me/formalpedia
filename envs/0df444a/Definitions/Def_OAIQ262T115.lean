-- Prove2me | Definitions.Def_OAIQ262T115
-- name    : OAIQ262T115
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T16:59:53.95956+00:00
-- url     : https://prove2.me/theorems/f193fcc7-1e50-40b5-89ea-50a067047f7c
-- title:
--   Definitions bundle OAIQ262T115 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 11 declarations of OpenAI's Lean: 1 definition and 10 theorems. The definitions and types are `OAI.AtomicTriangular.FiniteCertificate.bs0_0_0`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Signs_ExceptionalSign2`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/ExceptionalSign2.lean), [`Triangular_Signs_Signs00`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/Signs00.lean), [`Triangular_Signs_SineGrid0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/SineGrid0.lean), [`Triangular_Taylor_TaylorExp11`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorExp11.lean).
--
--   **Imports.** It imports the bundles `OAIQ262T005`, `OAIQ262T013`, `OAIQ262T015`, `OAIQ262T020`, `OAIQ262T043`, `OAIQ262T045` and `OAIQ262T046` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ262T146`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ262T005
import Definitions.Def_OAIQ262T013
import Definitions.Def_OAIQ262T015
import Definitions.Def_OAIQ262T020
import Definitions.Def_OAIQ262T043
import Definitions.Def_OAIQ262T045
import Definitions.Def_OAIQ262T046

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorExp11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma taylorExp1_1_1_calc (j : Fin 31) : ((taylorPhase1_1 j).mul (CI.point 1)).exp = taylorExp1_1_1 j := by
  revert j
  decide +kernel
lemma taylorExp1_1_3_calc (j : Fin 31) : ((taylorPhase1_1 j).mul (CI.point 3)).exp = taylorExp1_1_3 j := by
  revert j
  decide +kernel
lemma taylorExp1_1_13_calc (j : Fin 31) : ((taylorPhase1_1 j).mul (CI.point 13)).exp = taylorExp1_1_13 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_ExceptionalSign2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma ex2b0_calc (r : Fin 8) : bernsteinRowsBox 22 ex2r 0 r = ex2b0 r := by
  revert r
  decide +kernel
lemma ex2b10_calc (r : Fin 8) : bernsteinRowsBox 22 ex2r 10 r = ex2b10 r := by
  revert r
  decide +kernel
lemma ex2b11_calc (r : Fin 8) : bernsteinRowsBox 22 ex2r 11 r = ex2b11 r := by
  revert r
  decide +kernel
lemma ex2b12_calc (r : Fin 8) : bernsteinRowsBox 22 ex2r 12 r = ex2b12 r := by
  revert r
  decide +kernel
lemma ex2b13_calc (r : Fin 8) : bernsteinRowsBox 22 ex2r 13 r = ex2b13 r := by
  revert r
  decide +kernel
lemma ex2b14_calc (r : Fin 8) : bernsteinRowsBox 22 ex2r 14 r = ex2b14 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_Signs00
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
def bs0_0_0 : Fin 21 → Fin 8 → RI := ![bs0_0_0_0,bs0_0_0_1,bs0_0_0_2,bs0_0_0_3,bs0_0_0_4,bs0_0_0_5,bs0_0_0_6,bs0_0_0_7,bs0_0_0_8,bs0_0_0_9,bs0_0_0_10,bs0_0_0_11,bs0_0_0_12,bs0_0_0_13,bs0_0_0_14,bs0_0_0_15,bs0_0_0_16,bs0_0_0_17,bs0_0_0_18,bs0_0_0_19,bs0_0_0_20]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_SineGrid0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellGeometry03 (k : Fin 100) :
    0 ≤ cellMagnitude 3 k ∧ cellMagnitude 3 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 3 → 0 ≤ cellSeparation 3 k j ∧ cellSeparation 3 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0 ≤ cellMagnitude 3 k ∧ cellMagnitude 3 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 3 → 0 ≤ cellSeparation 3 k j ∧ cellSeparation 3 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end


