-- Prove2me | Definitions.Def_OAIQ262T110
-- name    : OAIQ262T110
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T16:57:14.93992+00:00
-- url     : https://prove2.me/theorems/0c1c242c-b657-4bbe-93f0-f8ffe41625a2
-- title:
--   Definitions bundle OAIQ262T110 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 10 declarations of OpenAI's Lean: 7 definitions and 3 theorems. The definitions and types are `OAI.AtomicTriangular.FiniteCertificate.bs0_3_0`, `OAI.AtomicTriangular.FiniteCertificate.bs0_4_1`, `OAI.AtomicTriangular.FiniteCertificate.tr0_0_0`, `OAI.AtomicTriangular.FiniteCertificate.tr0_1_0`, `OAI.AtomicTriangular.FiniteCertificate.tr0_1_1`, `OAI.AtomicTriangular.FiniteCertificate.tr0_2_0`, `OAI.AtomicTriangular.FiniteCertificate.tr0_2_1`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Signs_Signs03`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/Signs03.lean), [`Triangular_Signs_Signs04`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/Signs04.lean), [`Triangular_Signs_SineGrid2`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/SineGrid2.lean), [`Triangular_Taylor_TaylorExp01`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorExp01.lean), [`Triangular_Taylor_TaylorRows00`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorRows00.lean), [`Triangular_Taylor_TaylorRows01`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorRows01.lean), [`Triangular_Taylor_TaylorRows02`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorRows02.lean).
--
--   **Imports.** It imports the bundles `OAIQ262T005`, `OAIQ262T013`, `OAIQ262T015`, `OAIQ262T044`, `OAIQ262T046`, `OAIQ262T047`, `OAIQ262T048`, `OAIQ262T049`, `OAIQ262T050`, `OAIQ262T051`, `OAIQ262T052`, `OAIQ262T053`, `OAIQ262T056` and `OAIQ262T057` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ262T146`, `OAIQ262T171`, `OAIQ262T175`, `OAIQ262T177`, `OAIQ262T181`, `OAIQ262T183`, `OAIQ262T184`, `OAIQ262T185` and `OAIQ262T186`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ262T005
import Definitions.Def_OAIQ262T013
import Definitions.Def_OAIQ262T015
import Definitions.Def_OAIQ262T044
import Definitions.Def_OAIQ262T046
import Definitions.Def_OAIQ262T047
import Definitions.Def_OAIQ262T048
import Definitions.Def_OAIQ262T049
import Definitions.Def_OAIQ262T050
import Definitions.Def_OAIQ262T051
import Definitions.Def_OAIQ262T052
import Definitions.Def_OAIQ262T053
import Definitions.Def_OAIQ262T056
import Definitions.Def_OAIQ262T057

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
lemma taylorExp0_1_1_calc (j : Fin 31) : ((taylorPhase0_1 j).mul (CI.point 1)).exp = taylorExp0_1_1 j := by
  revert j
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
def bs0_3_0 : Fin 21 → Fin 8 → RI := ![bs0_3_0_0,bs0_3_0_1,bs0_3_0_2,bs0_3_0_3,bs0_3_0_4,bs0_3_0_5,bs0_3_0_6,bs0_3_0_7,bs0_3_0_8,bs0_3_0_9,bs0_3_0_10,bs0_3_0_11,bs0_3_0_12,bs0_3_0_13,bs0_3_0_14,bs0_3_0_15,bs0_3_0_16,bs0_3_0_17,bs0_3_0_18,bs0_3_0_19,bs0_3_0_20]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_Signs04
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
def bs0_4_1 : Fin 21 → Fin 8 → RI := ![bs0_4_1_0,bs0_4_1_1,bs0_4_1_2,bs0_4_1_3,bs0_4_1_4,bs0_4_1_5,bs0_4_1_6,bs0_4_1_7,bs0_4_1_8,bs0_4_1_9,bs0_4_1_10,bs0_4_1_11,bs0_4_1_12,bs0_4_1_13,bs0_4_1_14,bs0_4_1_15,bs0_4_1_16,bs0_4_1_17,bs0_4_1_18,bs0_4_1_19,bs0_4_1_20]
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
lemma cellFactors26 (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 26 k j) ∧ cellBarrier 26 < ∏ j : Fin 15,(cellFactor 26 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 26 k j) ∧ cellBarrier 26 < ∏ j : Fin 15,(cellFactor 26 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors27 (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 27 k j) ∧ cellBarrier 27 < ∏ j : Fin 15,(cellFactor 27 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 27 k j) ∧ cellBarrier 27 < ∏ j : Fin 15,(cellFactor 27 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorRows00
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

def tr0_0_0 : Fin 21 → Fin 8 → RI := ![tr0_0_0_0,tr0_0_0_1,tr0_0_0_2,tr0_0_0_3,tr0_0_0_4,tr0_0_0_5,tr0_0_0_6,tr0_0_0_7,tr0_0_0_8,tr0_0_0_9,tr0_0_0_10,tr0_0_0_11,tr0_0_0_12,tr0_0_0_13,tr0_0_0_14,tr0_0_0_15,tr0_0_0_16,tr0_0_0_17,tr0_0_0_18,tr0_0_0_19,tr0_0_0_20]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorRows01
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

def tr0_1_0 : Fin 21 → Fin 8 → RI := ![tr0_1_0_0,tr0_1_0_1,tr0_1_0_2,tr0_1_0_3,tr0_1_0_4,tr0_1_0_5,tr0_1_0_6,tr0_1_0_7,tr0_1_0_8,tr0_1_0_9,tr0_1_0_10,tr0_1_0_11,tr0_1_0_12,tr0_1_0_13,tr0_1_0_14,tr0_1_0_15,tr0_1_0_16,tr0_1_0_17,tr0_1_0_18,tr0_1_0_19,tr0_1_0_20]
def tr0_1_1 : Fin 21 → Fin 8 → RI := ![tr0_1_1_0,tr0_1_1_1,tr0_1_1_2,tr0_1_1_3,tr0_1_1_4,tr0_1_1_5,tr0_1_1_6,tr0_1_1_7,tr0_1_1_8,tr0_1_1_9,tr0_1_1_10,tr0_1_1_11,tr0_1_1_12,tr0_1_1_13,tr0_1_1_14,tr0_1_1_15,tr0_1_1_16,tr0_1_1_17,tr0_1_1_18,tr0_1_1_19,tr0_1_1_20]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorRows02
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

def tr0_2_0 : Fin 21 → Fin 8 → RI := ![tr0_2_0_0,tr0_2_0_1,tr0_2_0_2,tr0_2_0_3,tr0_2_0_4,tr0_2_0_5,tr0_2_0_6,tr0_2_0_7,tr0_2_0_8,tr0_2_0_9,tr0_2_0_10,tr0_2_0_11,tr0_2_0_12,tr0_2_0_13,tr0_2_0_14,tr0_2_0_15,tr0_2_0_16,tr0_2_0_17,tr0_2_0_18,tr0_2_0_19,tr0_2_0_20]
def tr0_2_1 : Fin 21 → Fin 8 → RI := ![tr0_2_1_0,tr0_2_1_1,tr0_2_1_2,tr0_2_1_3,tr0_2_1_4,tr0_2_1_5,tr0_2_1_6,tr0_2_1_7,tr0_2_1_8,tr0_2_1_9,tr0_2_1_10,tr0_2_1_11,tr0_2_1_12,tr0_2_1_13,tr0_2_1_14,tr0_2_1_15,tr0_2_1_16,tr0_2_1_17,tr0_2_1_18,tr0_2_1_19,tr0_2_1_20]
end AtomicTriangular.FiniteCertificate
end

end OAI
end


