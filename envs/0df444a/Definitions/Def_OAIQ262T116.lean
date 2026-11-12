-- Prove2me | Definitions.Def_OAIQ262T116
-- name    : OAIQ262T116
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T16:57:32.413241+00:00
-- url     : https://prove2.me/theorems/7045e18a-3ae1-4a8e-a5da-76c63f5ee793
-- title:
--   Definitions bundle OAIQ262T116 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 13 declarations of OpenAI's Lean: 3 definitions and 10 theorems. The definitions and types are `OAI.AtomicTriangular.FiniteCertificate.bs0_3_1`, `OAI.AtomicTriangular.FiniteCertificate.bs0_5_0`, `OAI.AtomicTriangular.FiniteCertificate.bs1_0_0`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Signs_ExceptionalSign2`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/ExceptionalSign2.lean), [`Triangular_Signs_Signs03`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/Signs03.lean), [`Triangular_Signs_Signs05`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/Signs05.lean), [`Triangular_Signs_Signs10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/Signs10.lean), [`Triangular_Signs_SineGrid0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/SineGrid0.lean), [`Triangular_Taylor_TaylorExp11`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorExp11.lean).
--
--   **Imports.** It imports the bundles `OAIQ262T005`, `OAIQ262T013`, `OAIQ262T015`, `OAIQ262T020`, `OAIQ262T045`, `OAIQ262T053`, `OAIQ262T054`, `OAIQ262T057`, `OAIQ262T058`, `OAIQ262T059`, `OAIQ262T060`, `OAIQ262T061`, `OAIQ262T063` and `OAIQ262T064` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ262T146`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ262T005
import Definitions.Def_OAIQ262T013
import Definitions.Def_OAIQ262T015
import Definitions.Def_OAIQ262T020
import Definitions.Def_OAIQ262T045
import Definitions.Def_OAIQ262T053
import Definitions.Def_OAIQ262T054
import Definitions.Def_OAIQ262T057
import Definitions.Def_OAIQ262T058
import Definitions.Def_OAIQ262T059
import Definitions.Def_OAIQ262T060
import Definitions.Def_OAIQ262T061
import Definitions.Def_OAIQ262T063
import Definitions.Def_OAIQ262T064

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
lemma taylorExp1_1_4_calc (j : Fin 31) : ((taylorPhase1_1 j).mul (CI.point 4)).exp = taylorExp1_1_4 j := by
  revert j
  decide +kernel
lemma taylorExp1_1_7_calc (j : Fin 31) : ((taylorPhase1_1 j).mul (CI.point 7)).exp = taylorExp1_1_7 j := by
  revert j
  decide +kernel
lemma taylorExp1_1_9_calc (j : Fin 31) : ((taylorPhase1_1 j).mul (CI.point 9)).exp = taylorExp1_1_9 j := by
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
lemma ex2b2_calc (r : Fin 8) : bernsteinRowsBox 22 ex2r 2 r = ex2b2 r := by
  revert r
  decide +kernel
lemma ex2b3_calc (r : Fin 8) : bernsteinRowsBox 22 ex2r 3 r = ex2b3 r := by
  revert r
  decide +kernel
lemma ex2b4_calc (r : Fin 8) : bernsteinRowsBox 22 ex2r 4 r = ex2b4 r := by
  revert r
  decide +kernel
lemma ex2b20_calc (r : Fin 8) : bernsteinRowsBox 22 ex2r 20 r = ex2b20 r := by
  revert r
  decide +kernel
lemma ex2b21_calc (r : Fin 8) : bernsteinRowsBox 22 ex2r 21 r = ex2b21 r := by
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
-- module Solutions.OAIQ262_TG.Triangular_Signs_Signs03
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
-- module Solutions.OAIQ262_TG.Triangular_Signs_Signs05
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
def bs0_5_0 : Fin 21 → Fin 8 → RI := ![bs0_5_0_0,bs0_5_0_1,bs0_5_0_2,bs0_5_0_3,bs0_5_0_4,bs0_5_0_5,bs0_5_0_6,bs0_5_0_7,bs0_5_0_8,bs0_5_0_9,bs0_5_0_10,bs0_5_0_11,bs0_5_0_12,bs0_5_0_13,bs0_5_0_14,bs0_5_0_15,bs0_5_0_16,bs0_5_0_17,bs0_5_0_18,bs0_5_0_19,bs0_5_0_20]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_Signs10
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
lemma cellGeometry04 (k : Fin 100) :
    0 ≤ cellMagnitude 4 k ∧ cellMagnitude 4 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 4 → 0 ≤ cellSeparation 4 k j ∧ cellSeparation 4 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0 ≤ cellMagnitude 4 k ∧ cellMagnitude 4 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 4 → 0 ≤ cellSeparation 4 k j ∧ cellSeparation 4 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end


