-- Prove2me | Definitions.Def_OAIQ262T102
-- name    : OAIQ262T102
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T16:56:46.890305+00:00
-- url     : https://prove2.me/theorems/7befecf4-11d7-4fe4-aa9c-9f3b53afd3ce
-- title:
--   Definitions bundle OAIQ262T102 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 11 declarations of OpenAI's Lean: 8 definitions and 3 theorems. The definitions and types are `OAI.AtomicTriangular.FiniteCertificate.bs1_3_1`, `OAI.AtomicTriangular.FiniteCertificate.bs1_4_0`, `OAI.AtomicTriangular.FiniteCertificate.bs1_4_1`, `OAI.AtomicTriangular.FiniteCertificate.tr0_5_1`, `OAI.AtomicTriangular.FiniteCertificate.tr0_6_0`, `OAI.AtomicTriangular.FiniteCertificate.tr0_6_1`, `OAI.AtomicTriangular.FiniteCertificate.tr1_0_0`, `OAI.AtomicTriangular.FiniteCertificate.tr1_0_1`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Signs_Signs13`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/Signs13.lean), [`Triangular_Signs_Signs14`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/Signs14.lean), [`Triangular_Signs_SineGrid1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/SineGrid1.lean), [`Triangular_Taylor_TaylorExp00`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorExp00.lean), [`Triangular_Taylor_TaylorRows05`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorRows05.lean), [`Triangular_Taylor_TaylorRows06`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorRows06.lean), [`Triangular_Taylor_TaylorRows10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorRows10.lean).
--
--   **Imports.** It imports the bundles `OAIQ262T005`, `OAIQ262T013`, `OAIQ262T015`, `OAIQ262T043`, `OAIQ262T060`, `OAIQ262T061`, `OAIQ262T062`, `OAIQ262T063`, `OAIQ262T064`, `OAIQ262T065`, `OAIQ262T066`, `OAIQ262T067`, `OAIQ262T073`, `OAIQ262T074`, `OAIQ262T075`, `OAIQ262T076` and `OAIQ262T077` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ262T146`, `OAIQ262T188` and `OAIQ262T189`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ262T005
import Definitions.Def_OAIQ262T013
import Definitions.Def_OAIQ262T015
import Definitions.Def_OAIQ262T043
import Definitions.Def_OAIQ262T060
import Definitions.Def_OAIQ262T061
import Definitions.Def_OAIQ262T062
import Definitions.Def_OAIQ262T063
import Definitions.Def_OAIQ262T064
import Definitions.Def_OAIQ262T065
import Definitions.Def_OAIQ262T066
import Definitions.Def_OAIQ262T067
import Definitions.Def_OAIQ262T073
import Definitions.Def_OAIQ262T074
import Definitions.Def_OAIQ262T075
import Definitions.Def_OAIQ262T076
import Definitions.Def_OAIQ262T077

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
lemma taylorExp0_0_12_calc (j : Fin 31) : ((taylorPhase0_0 j).mul (CI.point 12)).exp = taylorExp0_0_12 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_Signs13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
def bs1_3_1 : Fin 21 → Fin 8 → RI := ![bs1_3_1_0,bs1_3_1_1,bs1_3_1_2,bs1_3_1_3,bs1_3_1_4,bs1_3_1_5,bs1_3_1_6,bs1_3_1_7,bs1_3_1_8,bs1_3_1_9,bs1_3_1_10,bs1_3_1_11,bs1_3_1_12,bs1_3_1_13,bs1_3_1_14,bs1_3_1_15,bs1_3_1_16,bs1_3_1_17,bs1_3_1_18,bs1_3_1_19,bs1_3_1_20]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_Signs14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
def bs1_4_0 : Fin 21 → Fin 8 → RI := ![bs1_4_0_0,bs1_4_0_1,bs1_4_0_2,bs1_4_0_3,bs1_4_0_4,bs1_4_0_5,bs1_4_0_6,bs1_4_0_7,bs1_4_0_8,bs1_4_0_9,bs1_4_0_10,bs1_4_0_11,bs1_4_0_12,bs1_4_0_13,bs1_4_0_14,bs1_4_0_15,bs1_4_0_16,bs1_4_0_17,bs1_4_0_18,bs1_4_0_19,bs1_4_0_20]
def bs1_4_1 : Fin 21 → Fin 8 → RI := ![bs1_4_1_0,bs1_4_1_1,bs1_4_1_2,bs1_4_1_3,bs1_4_1_4,bs1_4_1_5,bs1_4_1_6,bs1_4_1_7,bs1_4_1_8,bs1_4_1_9,bs1_4_1_10,bs1_4_1_11,bs1_4_1_12,bs1_4_1_13,bs1_4_1_14,bs1_4_1_15,bs1_4_1_16,bs1_4_1_17,bs1_4_1_18,bs1_4_1_19,bs1_4_1_20]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_SineGrid1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors10 (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 10 k j) ∧ cellBarrier 10 < ∏ j : Fin 15,(cellFactor 10 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 10 k j) ∧ cellBarrier 10 < ∏ j : Fin 15,(cellFactor 10 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors11 (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 11 k j) ∧ cellBarrier 11 < ∏ j : Fin 15,(cellFactor 11 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 11 k j) ∧ cellBarrier 11 < ∏ j : Fin 15,(cellFactor 11 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
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

def tr0_5_1 : Fin 21 → Fin 8 → RI := ![tr0_5_1_0,tr0_5_1_1,tr0_5_1_2,tr0_5_1_3,tr0_5_1_4,tr0_5_1_5,tr0_5_1_6,tr0_5_1_7,tr0_5_1_8,tr0_5_1_9,tr0_5_1_10,tr0_5_1_11,tr0_5_1_12,tr0_5_1_13,tr0_5_1_14,tr0_5_1_15,tr0_5_1_16,tr0_5_1_17,tr0_5_1_18,tr0_5_1_19,tr0_5_1_20]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorRows06
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

def tr0_6_0 : Fin 21 → Fin 8 → RI := ![tr0_6_0_0,tr0_6_0_1,tr0_6_0_2,tr0_6_0_3,tr0_6_0_4,tr0_6_0_5,tr0_6_0_6,tr0_6_0_7,tr0_6_0_8,tr0_6_0_9,tr0_6_0_10,tr0_6_0_11,tr0_6_0_12,tr0_6_0_13,tr0_6_0_14,tr0_6_0_15,tr0_6_0_16,tr0_6_0_17,tr0_6_0_18,tr0_6_0_19,tr0_6_0_20]
def tr0_6_1 : Fin 21 → Fin 8 → RI := ![tr0_6_1_0,tr0_6_1_1,tr0_6_1_2,tr0_6_1_3,tr0_6_1_4,tr0_6_1_5,tr0_6_1_6,tr0_6_1_7,tr0_6_1_8,tr0_6_1_9,tr0_6_1_10,tr0_6_1_11,tr0_6_1_12,tr0_6_1_13,tr0_6_1_14,tr0_6_1_15,tr0_6_1_16,tr0_6_1_17,tr0_6_1_18,tr0_6_1_19,tr0_6_1_20]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorRows10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

def tr1_0_0 : Fin 21 → Fin 8 → RI := ![tr1_0_0_0,tr1_0_0_1,tr1_0_0_2,tr1_0_0_3,tr1_0_0_4,tr1_0_0_5,tr1_0_0_6,tr1_0_0_7,tr1_0_0_8,tr1_0_0_9,tr1_0_0_10,tr1_0_0_11,tr1_0_0_12,tr1_0_0_13,tr1_0_0_14,tr1_0_0_15,tr1_0_0_16,tr1_0_0_17,tr1_0_0_18,tr1_0_0_19,tr1_0_0_20]
def tr1_0_1 : Fin 21 → Fin 8 → RI := ![tr1_0_1_0,tr1_0_1_1,tr1_0_1_2,tr1_0_1_3,tr1_0_1_4,tr1_0_1_5,tr1_0_1_6,tr1_0_1_7,tr1_0_1_8,tr1_0_1_9,tr1_0_1_10,tr1_0_1_11,tr1_0_1_12,tr1_0_1_13,tr1_0_1_14,tr1_0_1_15,tr1_0_1_16,tr1_0_1_17,tr1_0_1_18,tr1_0_1_19,tr1_0_1_20]
end AtomicTriangular.FiniteCertificate
end

end OAI
end


