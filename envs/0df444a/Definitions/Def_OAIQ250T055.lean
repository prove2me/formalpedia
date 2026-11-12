-- Prove2me | Definitions.Def_OAIQ250T055
-- name    : OAIQ250T055
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T11:16:25.012977+00:00
-- url     : https://prove2.me/theorems/223ce0e0-207a-49c9-a605-aa96128da7a2
-- title:
--   Definitions bundle OAIQ250T055 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 9 declarations of OpenAI's Lean: 3 definitions and 6 theorems. The definitions and types are `OAI.AtomicTriangular.FiniteCertificate.bs0_6_0`, `OAI.AtomicTriangular.FiniteCertificate.bs1_0_0`, `OAI.AtomicTriangular.FiniteCertificate.bs1_0_1`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Signs_ExceptionalSign2`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/ExceptionalSign2.lean), [`Triangular_Signs_Signs06`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/Signs06.lean), [`Triangular_Signs_Signs10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/Signs10.lean), [`Triangular_Signs_SineGrid0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/SineGrid0.lean), [`Triangular_Taylor_TaylorExp01`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorExp01.lean).
--
--   **Imports.** It imports the bundles `OAIQ250T010`, `OAIQ250T011`, `OAIQ250T012`, `OAIQ250T026`, `OAIQ250T034`, `OAIQ250T035`, `OAIQ250T036` and `OAIQ250T037` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ250T086` and `OAIQ250T107`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ250T010
import Definitions.Def_OAIQ250T011
import Definitions.Def_OAIQ250T012
import Definitions.Def_OAIQ250T026
import Definitions.Def_OAIQ250T034
import Definitions.Def_OAIQ250T035
import Definitions.Def_OAIQ250T036
import Definitions.Def_OAIQ250T037

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
lemma taylorExp0_1_3_calc (j : Fin 31) : ((taylorPhase0_1 j).mul (CI.point 3)).exp = taylorExp0_1_3 j := by
  revert j
  decide +kernel
lemma taylorExp0_1_4_calc (j : Fin 31) : ((taylorPhase0_1 j).mul (CI.point 4)).exp = taylorExp0_1_4 j := by
  revert j
  decide +kernel
lemma taylorExp0_1_7_calc (j : Fin 31) : ((taylorPhase0_1 j).mul (CI.point 7)).exp = taylorExp0_1_7 j := by
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
lemma ex2b10_calc (r : Fin 8) : bernsteinRowsBox 22 ex2r 10 r = ex2b10 r := by
  revert r
  decide +kernel
lemma ex2b11_calc (r : Fin 8) : bernsteinRowsBox 22 ex2r 11 r = ex2b11 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_Signs06
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
def bs0_6_0 : Fin 21 → Fin 8 → RI := ![bs0_6_0_0,bs0_6_0_1,bs0_6_0_2,bs0_6_0_3,bs0_6_0_4,bs0_6_0_5,bs0_6_0_6,bs0_6_0_7,bs0_6_0_8,bs0_6_0_9,bs0_6_0_10,bs0_6_0_11,bs0_6_0_12,bs0_6_0_13,bs0_6_0_14,bs0_6_0_15,bs0_6_0_16,bs0_6_0_17,bs0_6_0_18,bs0_6_0_19,bs0_6_0_20]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_Signs10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
def bs1_0_0 : Fin 21 → Fin 8 → RI := ![bs1_0_0_0,bs1_0_0_1,bs1_0_0_2,bs1_0_0_3,bs1_0_0_4,bs1_0_0_5,bs1_0_0_6,bs1_0_0_7,bs1_0_0_8,bs1_0_0_9,bs1_0_0_10,bs1_0_0_11,bs1_0_0_12,bs1_0_0_13,bs1_0_0_14,bs1_0_0_15,bs1_0_0_16,bs1_0_0_17,bs1_0_0_18,bs1_0_0_19,bs1_0_0_20]
def bs1_0_1 : Fin 21 → Fin 8 → RI := ![bs1_0_1_0,bs1_0_1_1,bs1_0_1_2,bs1_0_1_3,bs1_0_1_4,bs1_0_1_5,bs1_0_1_6,bs1_0_1_7,bs1_0_1_8,bs1_0_1_9,bs1_0_1_10,bs1_0_1_11,bs1_0_1_12,bs1_0_1_13,bs1_0_1_14,bs1_0_1_15,bs1_0_1_16,bs1_0_1_17,bs1_0_1_18,bs1_0_1_19,bs1_0_1_20]
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
lemma cellFactors03 (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 3 k j) ∧ cellBarrier 3 < ∏ j : Fin 15,(cellFactor 3 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 3 k j) ∧ cellBarrier 3 < ∏ j : Fin 15,(cellFactor 3 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end


