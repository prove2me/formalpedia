-- Prove2me | Definitions.Def_OAIQ262T108
-- name    : OAIQ262T108
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T16:56:31.680743+00:00
-- url     : https://prove2.me/theorems/f44b8de2-cd96-49c1-bc1c-7318a2c50f34
-- title:
--   Definitions bundle OAIQ262T108 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 7 declarations of OpenAI's Lean: 3 definitions and 4 theorems. The definitions and types are `OAI.AtomicTriangular.FiniteCertificate.ex1b`, `OAI.AtomicTriangular.FiniteCertificate.ex1r`, `OAI.AtomicTriangular.FiniteCertificate.ex2b`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Signs_ExceptionalSign1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/ExceptionalSign1.lean), [`Triangular_Signs_ExceptionalSign2`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/ExceptionalSign2.lean), [`Triangular_Signs_SineGrid2`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/SineGrid2.lean), [`Triangular_Taylor_TaylorExp00`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorExp00.lean), [`Triangular_Taylor_TaylorExp01`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorExp01.lean).
--
--   **Imports.** It imports the bundles `OAIQ262T005`, `OAIQ262T013`, `OAIQ262T015`, `OAIQ262T018`, `OAIQ262T022`, `OAIQ262T023`, `OAIQ262T025`, `OAIQ262T026`, `OAIQ262T027`, `OAIQ262T030`, `OAIQ262T031`, `OAIQ262T032`, `OAIQ262T033`, `OAIQ262T034`, `OAIQ262T035`, `OAIQ262T038`, `OAIQ262T039`, `OAIQ262T040`, `OAIQ262T042`, `OAIQ262T043`, `OAIQ262T044` and `OAIQ262T045` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ262T146`, `OAIQ262T148` and `OAIQ262T149`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ262T005
import Definitions.Def_OAIQ262T013
import Definitions.Def_OAIQ262T015
import Definitions.Def_OAIQ262T018
import Definitions.Def_OAIQ262T022
import Definitions.Def_OAIQ262T023
import Definitions.Def_OAIQ262T025
import Definitions.Def_OAIQ262T026
import Definitions.Def_OAIQ262T027
import Definitions.Def_OAIQ262T030
import Definitions.Def_OAIQ262T031
import Definitions.Def_OAIQ262T032
import Definitions.Def_OAIQ262T033
import Definitions.Def_OAIQ262T034
import Definitions.Def_OAIQ262T035
import Definitions.Def_OAIQ262T038
import Definitions.Def_OAIQ262T039
import Definitions.Def_OAIQ262T040
import Definitions.Def_OAIQ262T042
import Definitions.Def_OAIQ262T043
import Definitions.Def_OAIQ262T044
import Definitions.Def_OAIQ262T045

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorExp00
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma taylorExp0_0_9_calc (j : Fin 31) : ((taylorPhase0_0 j).mul (CI.point 9)).exp = taylorExp0_0_9 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorExp01
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma taylorExp0_1_12_calc (j : Fin 31) : ((taylorPhase0_1 j).mul (CI.point 12)).exp = taylorExp0_1_12 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_ExceptionalSign1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
def ex1r : Fin 23 → Fin 8 → RI := ![ex1r0,ex1r1,ex1r2,ex1r3,ex1r4,ex1r5,ex1r6,ex1r7,ex1r8,ex1r9,ex1r10,ex1r11,ex1r12,ex1r13,ex1r14,ex1r15,ex1r16,ex1r17,ex1r18,ex1r19,ex1r20,ex1r21,ex1r22]
def ex1b : Fin 23 → Fin 8 → RI := ![ex1b0,ex1b1,ex1b2,ex1b3,ex1b4,ex1b5,ex1b6,ex1b7,ex1b8,ex1b9,ex1b10,ex1b11,ex1b12,ex1b13,ex1b14,ex1b15,ex1b16,ex1b17,ex1b18,ex1b19,ex1b20,ex1b21,ex1b22]
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
def ex2b : Fin 23 → Fin 8 → RI := ![ex2b0,ex2b1,ex2b2,ex2b3,ex2b4,ex2b5,ex2b6,ex2b7,ex2b8,ex2b9,ex2b10,ex2b11,ex2b12,ex2b13,ex2b14,ex2b15,ex2b16,ex2b17,ex2b18,ex2b19,ex2b20,ex2b21,ex2b22]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_SineGrid2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors22 (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 22 k j) ∧ cellBarrier 22 < ∏ j : Fin 15,(cellFactor 22 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 22 k j) ∧ cellBarrier 22 < ∏ j : Fin 15,(cellFactor 22 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors23 (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 23 k j) ∧ cellBarrier 23 < ∏ j : Fin 15,(cellFactor 23 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 23 k j) ∧ cellBarrier 23 < ∏ j : Fin 15,(cellFactor 23 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end


