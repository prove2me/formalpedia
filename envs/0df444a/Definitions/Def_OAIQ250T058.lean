-- Prove2me | Definitions.Def_OAIQ250T058
-- name    : OAIQ250T058
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T11:18:30.14782+00:00
-- url     : https://prove2.me/theorems/3e59f1a4-33d1-437b-9fcd-09923846dc81
-- title:
--   Definitions bundle OAIQ250T058 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 12 declarations of OpenAI's Lean: 4 definitions and 8 theorems. The definitions and types are `OAI.AtomicTriangular.FiniteCertificate.bs1_1_0`, `OAI.AtomicTriangular.FiniteCertificate.bs1_3_0`, `OAI.AtomicTriangular.FiniteCertificate.bs1_3_1`, `OAI.AtomicTriangular.FiniteCertificate.bs1_4_1`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Signs_ExceptionalSign2`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/ExceptionalSign2.lean), [`Triangular_Signs_Signs11`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/Signs11.lean), [`Triangular_Signs_Signs13`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/Signs13.lean), [`Triangular_Signs_Signs14`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/Signs14.lean), [`Triangular_Signs_SineGrid0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/SineGrid0.lean), [`Triangular_Taylor_TaylorExp10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorExp10.lean), [`Triangular_Taylor_TaylorExp11`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorExp11.lean).
--
--   **Imports.** It imports the bundles `OAIQ250T010`, `OAIQ250T011`, `OAIQ250T012`, `OAIQ250T025`, `OAIQ250T026`, `OAIQ250T027`, `OAIQ250T037`, `OAIQ250T039`, `OAIQ250T040`, `OAIQ250T041` and `OAIQ250T042` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ250T086` and `OAIQ250T107`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ250T010
import Definitions.Def_OAIQ250T011
import Definitions.Def_OAIQ250T012
import Definitions.Def_OAIQ250T025
import Definitions.Def_OAIQ250T026
import Definitions.Def_OAIQ250T027
import Definitions.Def_OAIQ250T037
import Definitions.Def_OAIQ250T039
import Definitions.Def_OAIQ250T040
import Definitions.Def_OAIQ250T041
import Definitions.Def_OAIQ250T042

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorExp10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma taylorExp1_0_7_calc (j : Fin 31) : ((taylorPhase1_0 j).mul (CI.point 7)).exp = taylorExp1_0_7 j := by
  revert j
  decide +kernel
lemma taylorExp1_0_9_calc (j : Fin 31) : ((taylorPhase1_0 j).mul (CI.point 9)).exp = taylorExp1_0_9 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorExp11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma taylorExp1_1_12_calc (j : Fin 31) : ((taylorPhase1_1 j).mul (CI.point 12)).exp = taylorExp1_1_12 j := by
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
lemma ex2b15_calc (r : Fin 8) : bernsteinRowsBox 22 ex2r 15 r = ex2b15 r := by
  revert r
  decide +kernel
lemma ex2b16_calc (r : Fin 8) : bernsteinRowsBox 22 ex2r 16 r = ex2b16 r := by
  revert r
  decide +kernel
lemma ex2b17_calc (r : Fin 8) : bernsteinRowsBox 22 ex2r 17 r = ex2b17 r := by
  revert r
  decide +kernel
lemma ex2b18_calc (r : Fin 8) : bernsteinRowsBox 22 ex2r 18 r = ex2b18 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_Signs11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
def bs1_1_0 : Fin 21 → Fin 8 → RI := ![bs1_1_0_0,bs1_1_0_1,bs1_1_0_2,bs1_1_0_3,bs1_1_0_4,bs1_1_0_5,bs1_1_0_6,bs1_1_0_7,bs1_1_0_8,bs1_1_0_9,bs1_1_0_10,bs1_1_0_11,bs1_1_0_12,bs1_1_0_13,bs1_1_0_14,bs1_1_0_15,bs1_1_0_16,bs1_1_0_17,bs1_1_0_18,bs1_1_0_19,bs1_1_0_20]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_Signs13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
def bs1_3_0 : Fin 21 → Fin 8 → RI := ![bs1_3_0_0,bs1_3_0_1,bs1_3_0_2,bs1_3_0_3,bs1_3_0_4,bs1_3_0_5,bs1_3_0_6,bs1_3_0_7,bs1_3_0_8,bs1_3_0_9,bs1_3_0_10,bs1_3_0_11,bs1_3_0_12,bs1_3_0_13,bs1_3_0_14,bs1_3_0_15,bs1_3_0_16,bs1_3_0_17,bs1_3_0_18,bs1_3_0_19,bs1_3_0_20]
def bs1_3_1 : Fin 21 → Fin 8 → RI := ![bs1_3_1_0,bs1_3_1_1,bs1_3_1_2,bs1_3_1_3,bs1_3_1_4,bs1_3_1_5,bs1_3_1_6,bs1_3_1_7,bs1_3_1_8,bs1_3_1_9,bs1_3_1_10,bs1_3_1_11,bs1_3_1_12,bs1_3_1_13,bs1_3_1_14,bs1_3_1_15,bs1_3_1_16,bs1_3_1_17,bs1_3_1_18,bs1_3_1_19,bs1_3_1_20]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_Signs14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
def bs1_4_1 : Fin 21 → Fin 8 → RI := ![bs1_4_1_0,bs1_4_1_1,bs1_4_1_2,bs1_4_1_3,bs1_4_1_4,bs1_4_1_5,bs1_4_1_6,bs1_4_1_7,bs1_4_1_8,bs1_4_1_9,bs1_4_1_10,bs1_4_1_11,bs1_4_1_12,bs1_4_1_13,bs1_4_1_14,bs1_4_1_15,bs1_4_1_16,bs1_4_1_17,bs1_4_1_18,bs1_4_1_19,bs1_4_1_20]
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
lemma cellFactors06 (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 6 k j) ∧ cellBarrier 6 < ∏ j : Fin 15,(cellFactor 6 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 6 k j) ∧ cellBarrier 6 < ∏ j : Fin 15,(cellFactor 6 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end


