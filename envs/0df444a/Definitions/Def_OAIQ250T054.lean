-- Prove2me | Definitions.Def_OAIQ250T054
-- name    : OAIQ250T054
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T11:16:55.77981+00:00
-- url     : https://prove2.me/theorems/e2c041a3-7d34-4ce9-8cc4-4450432c6123
-- title:
--   Definitions bundle OAIQ250T054 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 11 declarations of OpenAI's Lean: 2 definitions and 9 theorems. The definitions and types are `OAI.AtomicTriangular.FiniteCertificate.bs0_2_1`, `OAI.AtomicTriangular.FiniteCertificate.bs0_3_1`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Signs_ExceptionalSign2`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/ExceptionalSign2.lean), [`Triangular_Signs_ExceptionalSign3`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/ExceptionalSign3.lean), [`Triangular_Signs_Signs02`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/Signs02.lean), [`Triangular_Signs_Signs03`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/Signs03.lean), [`Triangular_Signs_SineGrid0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/SineGrid0.lean), [`Triangular_Taylor_TaylorExp01`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorExp01.lean).
--
--   **Imports.** It imports the bundles `OAIQ250T010`, `OAIQ250T011`, `OAIQ250T012`, `OAIQ250T026`, `OAIQ250T029`, `OAIQ250T030` and `OAIQ250T031` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ250T086` and `OAIQ250T107`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ250T010
import Definitions.Def_OAIQ250T011
import Definitions.Def_OAIQ250T012
import Definitions.Def_OAIQ250T026
import Definitions.Def_OAIQ250T029
import Definitions.Def_OAIQ250T030
import Definitions.Def_OAIQ250T031

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorExp01
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma taylorExp0_1_1_calc (j : Fin 31) : ((taylorPhase0_1 j).mul (CI.point 1)).exp = taylorExp0_1_1 j := by
  revert j
  decide +kernel
lemma taylorExp0_1_12_calc (j : Fin 31) : ((taylorPhase0_1 j).mul (CI.point 12)).exp = taylorExp0_1_12 j := by
  revert j
  decide +kernel
lemma taylorExp0_1_13_calc (j : Fin 31) : ((taylorPhase0_1 j).mul (CI.point 13)).exp = taylorExp0_1_13 j := by
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
lemma ex2b6_calc (r : Fin 8) : bernsteinRowsBox 22 ex2r 6 r = ex2b6 r := by
  revert r
  decide +kernel
lemma ex2b7_calc (r : Fin 8) : bernsteinRowsBox 22 ex2r 7 r = ex2b7 r := by
  revert r
  decide +kernel
lemma ex2b8_calc (r : Fin 8) : bernsteinRowsBox 22 ex2r 8 r = ex2b8 r := by
  revert r
  decide +kernel
lemma ex2b9_calc (r : Fin 8) : bernsteinRowsBox 22 ex2r 9 r = ex2b9 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_ExceptionalSign3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma ex3b10_calc (r : Fin 8) : bernsteinRowsBox 22 ex3r 10 r = ex3b10 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_Signs02
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
def bs0_2_1 : Fin 21 → Fin 8 → RI := ![bs0_2_1_0,bs0_2_1_1,bs0_2_1_2,bs0_2_1_3,bs0_2_1_4,bs0_2_1_5,bs0_2_1_6,bs0_2_1_7,bs0_2_1_8,bs0_2_1_9,bs0_2_1_10,bs0_2_1_11,bs0_2_1_12,bs0_2_1_13,bs0_2_1_14,bs0_2_1_15,bs0_2_1_16,bs0_2_1_17,bs0_2_1_18,bs0_2_1_19,bs0_2_1_20]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_Signs03
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
def bs0_3_1 : Fin 21 → Fin 8 → RI := ![bs0_3_1_0,bs0_3_1_1,bs0_3_1_2,bs0_3_1_3,bs0_3_1_4,bs0_3_1_5,bs0_3_1_6,bs0_3_1_7,bs0_3_1_8,bs0_3_1_9,bs0_3_1_10,bs0_3_1_11,bs0_3_1_12,bs0_3_1_13,bs0_3_1_14,bs0_3_1_15,bs0_3_1_16,bs0_3_1_17,bs0_3_1_18,bs0_3_1_19,bs0_3_1_20]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_SineGrid0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors02 (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 2 k j) ∧ cellBarrier 2 < ∏ j : Fin 15,(cellFactor 2 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 2 k j) ∧ cellBarrier 2 < ∏ j : Fin 15,(cellFactor 2 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end


