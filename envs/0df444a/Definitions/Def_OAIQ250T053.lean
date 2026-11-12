-- Prove2me | Definitions.Def_OAIQ250T053
-- name    : OAIQ250T053
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T11:16:26.813519+00:00
-- url     : https://prove2.me/theorems/66918516-7382-4f57-9eae-d6cfa6406921
-- title:
--   Definitions bundle OAIQ250T053 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 18 declarations of OpenAI's Lean: 3 definitions and 15 theorems. The definitions and types are `OAI.AtomicTriangular.FiniteCertificate.bs1_5_0`, `OAI.AtomicTriangular.FiniteCertificate.bs1_5_1`, `OAI.AtomicTriangular.FiniteCertificate.bs1_6_0`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Signs_ExceptionalSign3`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/ExceptionalSign3.lean), [`Triangular_Signs_Signs15`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/Signs15.lean), [`Triangular_Signs_Signs16`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/Signs16.lean), [`Triangular_Signs_SineGrid0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/SineGrid0.lean), [`Triangular_Taylor_TaylorExp00`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorExp00.lean).
--
--   **Imports.** It imports the bundles `OAIQ250T010`, `OAIQ250T011`, `OAIQ250T012`, `OAIQ250T026`, `OAIQ250T042`, `OAIQ250T043`, `OAIQ250T044` and `OAIQ250T045` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ250T086`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ250T010
import Definitions.Def_OAIQ250T011
import Definitions.Def_OAIQ250T012
import Definitions.Def_OAIQ250T026
import Definitions.Def_OAIQ250T042
import Definitions.Def_OAIQ250T043
import Definitions.Def_OAIQ250T044
import Definitions.Def_OAIQ250T045

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
lemma taylorExp0_0_4_calc (j : Fin 31) : ((taylorPhase0_0 j).mul (CI.point 4)).exp = taylorExp0_0_4 j := by
  revert j
  decide +kernel
lemma taylorExp0_0_7_calc (j : Fin 31) : ((taylorPhase0_0 j).mul (CI.point 7)).exp = taylorExp0_0_7 j := by
  revert j
  decide +kernel
lemma taylorExp0_0_9_calc (j : Fin 31) : ((taylorPhase0_0 j).mul (CI.point 9)).exp = taylorExp0_0_9 j := by
  revert j
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
lemma ex3b1_calc (r : Fin 8) : bernsteinRowsBox 22 ex3r 1 r = ex3b1 r := by
  revert r
  decide +kernel
lemma ex3b2_calc (r : Fin 8) : bernsteinRowsBox 22 ex3r 2 r = ex3b2 r := by
  revert r
  decide +kernel
lemma ex3b3_calc (r : Fin 8) : bernsteinRowsBox 22 ex3r 3 r = ex3b3 r := by
  revert r
  decide +kernel
lemma ex3b4_calc (r : Fin 8) : bernsteinRowsBox 22 ex3r 4 r = ex3b4 r := by
  revert r
  decide +kernel
lemma ex3b5_calc (r : Fin 8) : bernsteinRowsBox 22 ex3r 5 r = ex3b5 r := by
  revert r
  decide +kernel
lemma ex3b6_calc (r : Fin 8) : bernsteinRowsBox 22 ex3r 6 r = ex3b6 r := by
  revert r
  decide +kernel
lemma ex3b7_calc (r : Fin 8) : bernsteinRowsBox 22 ex3r 7 r = ex3b7 r := by
  revert r
  decide +kernel
lemma ex3b8_calc (r : Fin 8) : bernsteinRowsBox 22 ex3r 8 r = ex3b8 r := by
  revert r
  decide +kernel
lemma ex3b20_calc (r : Fin 8) : bernsteinRowsBox 22 ex3r 20 r = ex3b20 r := by
  revert r
  decide +kernel
lemma ex3b21_calc (r : Fin 8) : bernsteinRowsBox 22 ex3r 21 r = ex3b21 r := by
  revert r
  decide +kernel
lemma ex3b22_calc (r : Fin 8) : bernsteinRowsBox 22 ex3r 22 r = ex3b22 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_Signs15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
def bs1_5_0 : Fin 21 → Fin 8 → RI := ![bs1_5_0_0,bs1_5_0_1,bs1_5_0_2,bs1_5_0_3,bs1_5_0_4,bs1_5_0_5,bs1_5_0_6,bs1_5_0_7,bs1_5_0_8,bs1_5_0_9,bs1_5_0_10,bs1_5_0_11,bs1_5_0_12,bs1_5_0_13,bs1_5_0_14,bs1_5_0_15,bs1_5_0_16,bs1_5_0_17,bs1_5_0_18,bs1_5_0_19,bs1_5_0_20]
def bs1_5_1 : Fin 21 → Fin 8 → RI := ![bs1_5_1_0,bs1_5_1_1,bs1_5_1_2,bs1_5_1_3,bs1_5_1_4,bs1_5_1_5,bs1_5_1_6,bs1_5_1_7,bs1_5_1_8,bs1_5_1_9,bs1_5_1_10,bs1_5_1_11,bs1_5_1_12,bs1_5_1_13,bs1_5_1_14,bs1_5_1_15,bs1_5_1_16,bs1_5_1_17,bs1_5_1_18,bs1_5_1_19,bs1_5_1_20]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_Signs16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
def bs1_6_0 : Fin 21 → Fin 8 → RI := ![bs1_6_0_0,bs1_6_0_1,bs1_6_0_2,bs1_6_0_3,bs1_6_0_4,bs1_6_0_5,bs1_6_0_6,bs1_6_0_7,bs1_6_0_8,bs1_6_0_9,bs1_6_0_10,bs1_6_0_11,bs1_6_0_12,bs1_6_0_13,bs1_6_0_14,bs1_6_0_15,bs1_6_0_16,bs1_6_0_17,bs1_6_0_18,bs1_6_0_19,bs1_6_0_20]
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
lemma cellFactors01 (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 1 k j) ∧ cellBarrier 1 < ∏ j : Fin 15,(cellFactor 1 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 1 k j) ∧ cellBarrier 1 < ∏ j : Fin 15,(cellFactor 1 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end


