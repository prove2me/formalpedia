-- Prove2me | Definitions.Def_OAIQ250T057
-- name    : OAIQ250T057
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T11:16:08.37461+00:00
-- url     : https://prove2.me/theorems/b6cbe5bc-a293-46d9-86af-082f934cbab9
-- title:
--   Definitions bundle OAIQ250T057 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 10 declarations of OpenAI's Lean: 3 definitions and 7 theorems. The definitions and types are `OAI.AtomicTriangular.FiniteCertificate.bs0_4_0`, `OAI.AtomicTriangular.FiniteCertificate.bs0_5_1`, `OAI.AtomicTriangular.FiniteCertificate.bs1_2_0`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Signs_ExceptionalSign2`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/ExceptionalSign2.lean), [`Triangular_Signs_Signs04`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/Signs04.lean), [`Triangular_Signs_Signs05`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/Signs05.lean), [`Triangular_Signs_Signs12`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/Signs12.lean), [`Triangular_Signs_SineGrid0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/SineGrid0.lean), [`Triangular_Taylor_TaylorExp10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorExp10.lean).
--
--   **Imports.** It imports the bundles `OAIQ250T010`, `OAIQ250T011`, `OAIQ250T012`, `OAIQ250T026`, `OAIQ250T031`, `OAIQ250T032`, `OAIQ250T033`, `OAIQ250T034`, `OAIQ250T038` and `OAIQ250T039` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ250T086` and `OAIQ250T107`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ250T010
import Definitions.Def_OAIQ250T011
import Definitions.Def_OAIQ250T012
import Definitions.Def_OAIQ250T026
import Definitions.Def_OAIQ250T031
import Definitions.Def_OAIQ250T032
import Definitions.Def_OAIQ250T033
import Definitions.Def_OAIQ250T034
import Definitions.Def_OAIQ250T038
import Definitions.Def_OAIQ250T039

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
lemma taylorExp1_0_1_calc (j : Fin 31) : ((taylorPhase1_0 j).mul (CI.point 1)).exp = taylorExp1_0_1 j := by
  revert j
  decide +kernel
lemma taylorExp1_0_3_calc (j : Fin 31) : ((taylorPhase1_0 j).mul (CI.point 3)).exp = taylorExp1_0_3 j := by
  revert j
  decide +kernel
lemma taylorExp1_0_4_calc (j : Fin 31) : ((taylorPhase1_0 j).mul (CI.point 4)).exp = taylorExp1_0_4 j := by
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
-- module Solutions.OAIQ250_TR.Triangular_Signs_Signs04
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
def bs0_4_0 : Fin 21 → Fin 8 → RI := ![bs0_4_0_0,bs0_4_0_1,bs0_4_0_2,bs0_4_0_3,bs0_4_0_4,bs0_4_0_5,bs0_4_0_6,bs0_4_0_7,bs0_4_0_8,bs0_4_0_9,bs0_4_0_10,bs0_4_0_11,bs0_4_0_12,bs0_4_0_13,bs0_4_0_14,bs0_4_0_15,bs0_4_0_16,bs0_4_0_17,bs0_4_0_18,bs0_4_0_19,bs0_4_0_20]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_Signs05
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
def bs0_5_1 : Fin 21 → Fin 8 → RI := ![bs0_5_1_0,bs0_5_1_1,bs0_5_1_2,bs0_5_1_3,bs0_5_1_4,bs0_5_1_5,bs0_5_1_6,bs0_5_1_7,bs0_5_1_8,bs0_5_1_9,bs0_5_1_10,bs0_5_1_11,bs0_5_1_12,bs0_5_1_13,bs0_5_1_14,bs0_5_1_15,bs0_5_1_16,bs0_5_1_17,bs0_5_1_18,bs0_5_1_19,bs0_5_1_20]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_Signs12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
def bs1_2_0 : Fin 21 → Fin 8 → RI := ![bs1_2_0_0,bs1_2_0_1,bs1_2_0_2,bs1_2_0_3,bs1_2_0_4,bs1_2_0_5,bs1_2_0_6,bs1_2_0_7,bs1_2_0_8,bs1_2_0_9,bs1_2_0_10,bs1_2_0_11,bs1_2_0_12,bs1_2_0_13,bs1_2_0_14,bs1_2_0_15,bs1_2_0_16,bs1_2_0_17,bs1_2_0_18,bs1_2_0_19,bs1_2_0_20]
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
lemma cellFactors05 (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 5 k j) ∧ cellBarrier 5 < ∏ j : Fin 15,(cellFactor 5 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 5 k j) ∧ cellBarrier 5 < ∏ j : Fin 15,(cellFactor 5 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end


