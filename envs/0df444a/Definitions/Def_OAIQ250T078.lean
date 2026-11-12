-- Prove2me | Definitions.Def_OAIQ250T078
-- name    : OAIQ250T078
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T11:20:26.420229+00:00
-- url     : https://prove2.me/theorems/a38f977f-dcee-4cd5-acff-12f272cf2ca9
-- title:
--   Definitions bundle OAIQ250T078 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 10 declarations of OpenAI's Lean: 1 definition and 9 theorems. The definitions and types are `OAI.AtomicTriangular.FiniteCertificate.bs0_1_0`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Signs_ExceptionalSign2`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/ExceptionalSign2.lean), [`Triangular_Signs_Signs01`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/Signs01.lean), [`Triangular_Signs_SineGrid1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/SineGrid1.lean), [`Triangular_Taylor_TaylorExp00`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorExp00.lean).
--
--   **Imports.** It imports the bundles `OAIQ250T010`, `OAIQ250T011`, `OAIQ250T012`, `OAIQ250T025`, `OAIQ250T026` and `OAIQ250T027` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ250T086`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ250T010
import Definitions.Def_OAIQ250T011
import Definitions.Def_OAIQ250T012
import Definitions.Def_OAIQ250T025
import Definitions.Def_OAIQ250T026
import Definitions.Def_OAIQ250T027

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorExp00
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma taylorExp0_0_12_calc (j : Fin 31) : ((taylorPhase0_0 j).mul (CI.point 12)).exp = taylorExp0_0_12 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_ExceptionalSign2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma ex2b2_calc (r : Fin 8) : bernsteinRowsBox 22 ex2r 2 r = ex2b2 r := by
  revert r
  decide +kernel
lemma ex2b3_calc (r : Fin 8) : bernsteinRowsBox 22 ex2r 3 r = ex2b3 r := by
  revert r
  decide +kernel
lemma ex2b4_calc (r : Fin 8) : bernsteinRowsBox 22 ex2r 4 r = ex2b4 r := by
  revert r
  decide +kernel
lemma ex2b5_calc (r : Fin 8) : bernsteinRowsBox 22 ex2r 5 r = ex2b5 r := by
  revert r
  decide +kernel
lemma ex2b22_calc (r : Fin 8) : bernsteinRowsBox 22 ex2r 22 r = ex2b22 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_Signs01
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
def bs0_1_0 : Fin 21 → Fin 8 → RI := ![bs0_1_0_0,bs0_1_0_1,bs0_1_0_2,bs0_1_0_3,bs0_1_0_4,bs0_1_0_5,bs0_1_0_6,bs0_1_0_7,bs0_1_0_8,bs0_1_0_9,bs0_1_0_10,bs0_1_0_11,bs0_1_0_12,bs0_1_0_13,bs0_1_0_14,bs0_1_0_15,bs0_1_0_16,bs0_1_0_17,bs0_1_0_18,bs0_1_0_19,bs0_1_0_20]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_SineGrid1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellGeometry16 (k : Fin 100) :
    0 ≤ cellMagnitude 16 k ∧ cellMagnitude 16 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 16 → 0 ≤ cellSeparation 16 k j ∧ cellSeparation 16 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0 ≤ cellMagnitude 16 k ∧ cellMagnitude 16 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 16 → 0 ≤ cellSeparation 16 k j ∧ cellSeparation 16 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellGeometry17 (k : Fin 100) :
    0 ≤ cellMagnitude 17 k ∧ cellMagnitude 17 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 17 → 0 ≤ cellSeparation 17 k j ∧ cellSeparation 17 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0 ≤ cellMagnitude 17 k ∧ cellMagnitude 17 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 17 → 0 ≤ cellSeparation 17 k j ∧ cellSeparation 17 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellGeometry18 (k : Fin 100) :
    0 ≤ cellMagnitude 18 k ∧ cellMagnitude 18 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 18 → 0 ≤ cellSeparation 18 k j ∧ cellSeparation 18 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0 ≤ cellMagnitude 18 k ∧ cellMagnitude 18 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 18 → 0 ≤ cellSeparation 18 k j ∧ cellSeparation 18 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end


