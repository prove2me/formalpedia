-- Prove2me | Definitions.Def_OAIQ262T133
-- name    : OAIQ262T133
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T17:19:20.638147+00:00
-- url     : https://prove2.me/theorems/b6849cfc-3607-4771-b42b-8aac10502edc
-- title:
--   Definitions bundle OAIQ262T133 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 6 declarations of OpenAI's Lean: 4 definitions and 2 theorems. The definitions and types are `OAI.AtomicTriangular.FiniteCertificate.ex0b`, `OAI.AtomicTriangular.FiniteCertificate.ex0r`, `OAI.AtomicTriangular.FiniteCertificate.tw0_0_3`, `OAI.AtomicTriangular.FiniteCertificate.tw0_0_6`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Signs_ExceptionalSign0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/ExceptionalSign0.lean), [`Triangular_Signs_SineGrid2`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/SineGrid2.lean), [`Triangular_Taylor_TaylorWave003`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave003.lean), [`Triangular_Taylor_TaylorWave006`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave006.lean).
--
--   **Imports.** It imports the bundles `OAIQ262T015`, `OAIQ262T017`, `OAIQ262T018`, `OAIQ262T019`, `OAIQ262T020`, `OAIQ262T024`, `OAIQ262T025`, `OAIQ262T026` and `OAIQ262T027` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ262T146`, `OAIQ262T147` and `OAIQ262T148`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ262T015
import Definitions.Def_OAIQ262T017
import Definitions.Def_OAIQ262T018
import Definitions.Def_OAIQ262T019
import Definitions.Def_OAIQ262T020
import Definitions.Def_OAIQ262T024
import Definitions.Def_OAIQ262T025
import Definitions.Def_OAIQ262T026
import Definitions.Def_OAIQ262T027

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave003
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def tw0_0_3 : Fin 21 → Fin 31 → CI := ![tw0_0_3_0,tw0_0_3_1,tw0_0_3_2,tw0_0_3_3,tw0_0_3_4,tw0_0_3_5,tw0_0_3_6,tw0_0_3_7,tw0_0_3_8,tw0_0_3_9,tw0_0_3_10,tw0_0_3_11,tw0_0_3_12,tw0_0_3_13,tw0_0_3_14,tw0_0_3_15,tw0_0_3_16,tw0_0_3_17,tw0_0_3_18,tw0_0_3_19,tw0_0_3_20]

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave006
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def tw0_0_6 : Fin 21 → Fin 31 → CI := ![tw0_0_6_0,tw0_0_6_1,tw0_0_6_2,tw0_0_6_3,tw0_0_6_4,tw0_0_6_5,tw0_0_6_6,tw0_0_6_7,tw0_0_6_8,tw0_0_6_9,tw0_0_6_10,tw0_0_6_11,tw0_0_6_12,tw0_0_6_13,tw0_0_6_14,tw0_0_6_15,tw0_0_6_16,tw0_0_6_17,tw0_0_6_18,tw0_0_6_19,tw0_0_6_20]

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_ExceptionalSign0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
def ex0r : Fin 23 → Fin 8 → RI := ![ex0r0,ex0r1,ex0r2,ex0r3,ex0r4,ex0r5,ex0r6,ex0r7,ex0r8,ex0r9,ex0r10,ex0r11,ex0r12,ex0r13,ex0r14,ex0r15,ex0r16,ex0r17,ex0r18,ex0r19,ex0r20,ex0r21,ex0r22]
def ex0b : Fin 23 → Fin 8 → RI := ![ex0b0,ex0b1,ex0b2,ex0b3,ex0b4,ex0b5,ex0b6,ex0b7,ex0b8,ex0b9,ex0b10,ex0b11,ex0b12,ex0b13,ex0b14,ex0b15,ex0b16,ex0b17,ex0b18,ex0b19,ex0b20,ex0b21,ex0b22]
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
lemma cellGeometry22 (k : Fin 100) :
    0 ≤ cellMagnitude 22 k ∧ cellMagnitude 22 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 22 → 0 ≤ cellSeparation 22 k j ∧ cellSeparation 22 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0 ≤ cellMagnitude 22 k ∧ cellMagnitude 22 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 22 → 0 ≤ cellSeparation 22 k j ∧ cellSeparation 22 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellGeometry23 (k : Fin 100) :
    0 ≤ cellMagnitude 23 k ∧ cellMagnitude 23 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 23 → 0 ≤ cellSeparation 23 k j ∧ cellSeparation 23 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0 ≤ cellMagnitude 23 k ∧ cellMagnitude 23 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 23 → 0 ≤ cellSeparation 23 k j ∧ cellSeparation 23 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end


