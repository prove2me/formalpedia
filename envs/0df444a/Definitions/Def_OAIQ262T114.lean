-- Prove2me | Definitions.Def_OAIQ262T114
-- name    : OAIQ262T114
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T16:58:17.804687+00:00
-- url     : https://prove2.me/theorems/32c8f05c-b6ea-4086-b41a-9d6a6b0c7e00
-- title:
--   Definitions bundle OAIQ262T114 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 12 declarations of OpenAI's Lean: 8 definitions and 4 theorems. The definitions and types are `OAI.AtomicTriangular.FiniteCertificate.bs0_5_1`, `OAI.AtomicTriangular.FiniteCertificate.bs0_6_0`, `OAI.AtomicTriangular.FiniteCertificate.bs0_6_1`, `OAI.AtomicTriangular.FiniteCertificate.tr0_3_0`, `OAI.AtomicTriangular.FiniteCertificate.tr0_3_1`, `OAI.AtomicTriangular.FiniteCertificate.tr0_4_0`, `OAI.AtomicTriangular.FiniteCertificate.tr0_4_1`, `OAI.AtomicTriangular.FiniteCertificate.tr0_5_0`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Signs_Signs05`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/Signs05.lean), [`Triangular_Signs_Signs06`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/Signs06.lean), [`Triangular_Signs_SineGrid0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/SineGrid0.lean), [`Triangular_Taylor_TaylorExp10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorExp10.lean), [`Triangular_Taylor_TaylorExp11`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorExp11.lean), [`Triangular_Taylor_TaylorRows03`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorRows03.lean), [`Triangular_Taylor_TaylorRows04`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorRows04.lean), [`Triangular_Taylor_TaylorRows05`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorRows05.lean).
--
--   **Imports.** It imports the bundles `OAIQ262T005`, `OAIQ262T013`, `OAIQ262T015`, `OAIQ262T044`, `OAIQ262T045`, `OAIQ262T053`, `OAIQ262T054`, `OAIQ262T055`, `OAIQ262T056`, `OAIQ262T057`, `OAIQ262T058`, `OAIQ262T059`, `OAIQ262T060`, `OAIQ262T061`, `OAIQ262T062` and `OAIQ262T063` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ262T146`, `OAIQ262T186`, `OAIQ262T187` and `OAIQ262T188`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ262T005
import Definitions.Def_OAIQ262T013
import Definitions.Def_OAIQ262T015
import Definitions.Def_OAIQ262T044
import Definitions.Def_OAIQ262T045
import Definitions.Def_OAIQ262T053
import Definitions.Def_OAIQ262T054
import Definitions.Def_OAIQ262T055
import Definitions.Def_OAIQ262T056
import Definitions.Def_OAIQ262T057
import Definitions.Def_OAIQ262T058
import Definitions.Def_OAIQ262T059
import Definitions.Def_OAIQ262T060
import Definitions.Def_OAIQ262T061
import Definitions.Def_OAIQ262T062
import Definitions.Def_OAIQ262T063

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorExp10
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
lemma taylorExp1_1_12_calc (j : Fin 31) : ((taylorPhase1_1 j).mul (CI.point 12)).exp = taylorExp1_1_12 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorRows05
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

def tr0_5_0 : Fin 21 → Fin 8 → RI := ![tr0_5_0_0,tr0_5_0_1,tr0_5_0_2,tr0_5_0_3,tr0_5_0_4,tr0_5_0_5,tr0_5_0_6,tr0_5_0_7,tr0_5_0_8,tr0_5_0_9,tr0_5_0_10,tr0_5_0_11,tr0_5_0_12,tr0_5_0_13,tr0_5_0_14,tr0_5_0_15,tr0_5_0_16,tr0_5_0_17,tr0_5_0_18,tr0_5_0_19,tr0_5_0_20]
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
def bs0_5_1 : Fin 21 → Fin 8 → RI := ![bs0_5_1_0,bs0_5_1_1,bs0_5_1_2,bs0_5_1_3,bs0_5_1_4,bs0_5_1_5,bs0_5_1_6,bs0_5_1_7,bs0_5_1_8,bs0_5_1_9,bs0_5_1_10,bs0_5_1_11,bs0_5_1_12,bs0_5_1_13,bs0_5_1_14,bs0_5_1_15,bs0_5_1_16,bs0_5_1_17,bs0_5_1_18,bs0_5_1_19,bs0_5_1_20]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_Signs06
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
def bs0_6_1 : Fin 21 → Fin 8 → RI := ![bs0_6_1_0,bs0_6_1_1,bs0_6_1_2,bs0_6_1_3,bs0_6_1_4,bs0_6_1_5,bs0_6_1_6,bs0_6_1_7,bs0_6_1_8,bs0_6_1_9,bs0_6_1_10,bs0_6_1_11,bs0_6_1_12,bs0_6_1_13,bs0_6_1_14,bs0_6_1_15,bs0_6_1_16,bs0_6_1_17,bs0_6_1_18,bs0_6_1_19,bs0_6_1_20]
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
lemma cellGeometry02 (k : Fin 100) :
    0 ≤ cellMagnitude 2 k ∧ cellMagnitude 2 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 2 → 0 ≤ cellSeparation 2 k j ∧ cellSeparation 2 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0 ≤ cellMagnitude 2 k ∧ cellMagnitude 2 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 2 → 0 ≤ cellSeparation 2 k j ∧ cellSeparation 2 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorRows03
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

def tr0_3_0 : Fin 21 → Fin 8 → RI := ![tr0_3_0_0,tr0_3_0_1,tr0_3_0_2,tr0_3_0_3,tr0_3_0_4,tr0_3_0_5,tr0_3_0_6,tr0_3_0_7,tr0_3_0_8,tr0_3_0_9,tr0_3_0_10,tr0_3_0_11,tr0_3_0_12,tr0_3_0_13,tr0_3_0_14,tr0_3_0_15,tr0_3_0_16,tr0_3_0_17,tr0_3_0_18,tr0_3_0_19,tr0_3_0_20]
def tr0_3_1 : Fin 21 → Fin 8 → RI := ![tr0_3_1_0,tr0_3_1_1,tr0_3_1_2,tr0_3_1_3,tr0_3_1_4,tr0_3_1_5,tr0_3_1_6,tr0_3_1_7,tr0_3_1_8,tr0_3_1_9,tr0_3_1_10,tr0_3_1_11,tr0_3_1_12,tr0_3_1_13,tr0_3_1_14,tr0_3_1_15,tr0_3_1_16,tr0_3_1_17,tr0_3_1_18,tr0_3_1_19,tr0_3_1_20]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorRows04
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

def tr0_4_0 : Fin 21 → Fin 8 → RI := ![tr0_4_0_0,tr0_4_0_1,tr0_4_0_2,tr0_4_0_3,tr0_4_0_4,tr0_4_0_5,tr0_4_0_6,tr0_4_0_7,tr0_4_0_8,tr0_4_0_9,tr0_4_0_10,tr0_4_0_11,tr0_4_0_12,tr0_4_0_13,tr0_4_0_14,tr0_4_0_15,tr0_4_0_16,tr0_4_0_17,tr0_4_0_18,tr0_4_0_19,tr0_4_0_20]
def tr0_4_1 : Fin 21 → Fin 8 → RI := ![tr0_4_1_0,tr0_4_1_1,tr0_4_1_2,tr0_4_1_3,tr0_4_1_4,tr0_4_1_5,tr0_4_1_6,tr0_4_1_7,tr0_4_1_8,tr0_4_1_9,tr0_4_1_10,tr0_4_1_11,tr0_4_1_12,tr0_4_1_13,tr0_4_1_14,tr0_4_1_15,tr0_4_1_16,tr0_4_1_17,tr0_4_1_18,tr0_4_1_19,tr0_4_1_20]
end AtomicTriangular.FiniteCertificate
end

end OAI
end


