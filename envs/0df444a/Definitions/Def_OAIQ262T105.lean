-- Prove2me | Definitions.Def_OAIQ262T105
-- name    : OAIQ262T105
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T16:55:23.400804+00:00
-- url     : https://prove2.me/theorems/6b72824f-279a-49ae-bfad-5b23897aba5d
-- title:
--   Definitions bundle OAIQ262T105 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 12 declarations of OpenAI's Lean: 9 definitions and 3 theorems. The definitions and types are `OAI.AtomicTriangular.FiniteCertificate.bs1_5_0`, `OAI.AtomicTriangular.FiniteCertificate.bs1_5_1`, `OAI.AtomicTriangular.FiniteCertificate.bs1_6_0`, `OAI.AtomicTriangular.FiniteCertificate.bs1_6_1`, `OAI.AtomicTriangular.FiniteCertificate.tr1_1_0`, `OAI.AtomicTriangular.FiniteCertificate.tr1_1_1`, `OAI.AtomicTriangular.FiniteCertificate.tr1_2_0`, `OAI.AtomicTriangular.FiniteCertificate.tr1_2_1`, `OAI.AtomicTriangular.FiniteCertificate.tr1_3_0`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Signs_Signs15`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/Signs15.lean), [`Triangular_Signs_Signs16`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/Signs16.lean), [`Triangular_Signs_SineGrid1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/SineGrid1.lean), [`Triangular_Taylor_TaylorExp00`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorExp00.lean), [`Triangular_Taylor_TaylorRows11`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorRows11.lean), [`Triangular_Taylor_TaylorRows12`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorRows12.lean), [`Triangular_Taylor_TaylorRows13`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorRows13.lean).
--
--   **Imports.** It imports the bundles `OAIQ262T005`, `OAIQ262T013`, `OAIQ262T015`, `OAIQ262T043`, `OAIQ262T067`, `OAIQ262T068`, `OAIQ262T069`, `OAIQ262T070`, `OAIQ262T071`, `OAIQ262T072`, `OAIQ262T073`, `OAIQ262T074`, `OAIQ262T077`, `OAIQ262T078`, `OAIQ262T079`, `OAIQ262T080`, `OAIQ262T081`, `OAIQ262T082` and `OAIQ262T083` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ262T146`, `OAIQ262T174`, `OAIQ262T175`, `OAIQ262T183`, `OAIQ262T189` and `OAIQ262T190`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ262T005
import Definitions.Def_OAIQ262T013
import Definitions.Def_OAIQ262T015
import Definitions.Def_OAIQ262T043
import Definitions.Def_OAIQ262T067
import Definitions.Def_OAIQ262T068
import Definitions.Def_OAIQ262T069
import Definitions.Def_OAIQ262T070
import Definitions.Def_OAIQ262T071
import Definitions.Def_OAIQ262T072
import Definitions.Def_OAIQ262T073
import Definitions.Def_OAIQ262T074
import Definitions.Def_OAIQ262T077
import Definitions.Def_OAIQ262T078
import Definitions.Def_OAIQ262T079
import Definitions.Def_OAIQ262T080
import Definitions.Def_OAIQ262T081
import Definitions.Def_OAIQ262T082
import Definitions.Def_OAIQ262T083

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
lemma taylorExp0_0_3_calc (j : Fin 31) : ((taylorPhase0_0 j).mul (CI.point 3)).exp = taylorExp0_0_3 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_Signs15
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
-- module Solutions.OAIQ262_TG.Triangular_Signs_Signs16
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
def bs1_6_1 : Fin 21 → Fin 8 → RI := ![bs1_6_1_0,bs1_6_1_1,bs1_6_1_2,bs1_6_1_3,bs1_6_1_4,bs1_6_1_5,bs1_6_1_6,bs1_6_1_7,bs1_6_1_8,bs1_6_1_9,bs1_6_1_10,bs1_6_1_11,bs1_6_1_12,bs1_6_1_13,bs1_6_1_14,bs1_6_1_15,bs1_6_1_16,bs1_6_1_17,bs1_6_1_18,bs1_6_1_19,bs1_6_1_20]
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
lemma cellFactors16 (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 16 k j) ∧ cellBarrier 16 < ∏ j : Fin 15,(cellFactor 16 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 16 k j) ∧ cellBarrier 16 < ∏ j : Fin 15,(cellFactor 16 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors17 (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 17 k j) ∧ cellBarrier 17 < ∏ j : Fin 15,(cellFactor 17 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 17 k j) ∧ cellBarrier 17 < ∏ j : Fin 15,(cellFactor 17 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorRows11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

def tr1_1_0 : Fin 21 → Fin 8 → RI := ![tr1_1_0_0,tr1_1_0_1,tr1_1_0_2,tr1_1_0_3,tr1_1_0_4,tr1_1_0_5,tr1_1_0_6,tr1_1_0_7,tr1_1_0_8,tr1_1_0_9,tr1_1_0_10,tr1_1_0_11,tr1_1_0_12,tr1_1_0_13,tr1_1_0_14,tr1_1_0_15,tr1_1_0_16,tr1_1_0_17,tr1_1_0_18,tr1_1_0_19,tr1_1_0_20]
def tr1_1_1 : Fin 21 → Fin 8 → RI := ![tr1_1_1_0,tr1_1_1_1,tr1_1_1_2,tr1_1_1_3,tr1_1_1_4,tr1_1_1_5,tr1_1_1_6,tr1_1_1_7,tr1_1_1_8,tr1_1_1_9,tr1_1_1_10,tr1_1_1_11,tr1_1_1_12,tr1_1_1_13,tr1_1_1_14,tr1_1_1_15,tr1_1_1_16,tr1_1_1_17,tr1_1_1_18,tr1_1_1_19,tr1_1_1_20]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorRows12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

def tr1_2_0 : Fin 21 → Fin 8 → RI := ![tr1_2_0_0,tr1_2_0_1,tr1_2_0_2,tr1_2_0_3,tr1_2_0_4,tr1_2_0_5,tr1_2_0_6,tr1_2_0_7,tr1_2_0_8,tr1_2_0_9,tr1_2_0_10,tr1_2_0_11,tr1_2_0_12,tr1_2_0_13,tr1_2_0_14,tr1_2_0_15,tr1_2_0_16,tr1_2_0_17,tr1_2_0_18,tr1_2_0_19,tr1_2_0_20]
def tr1_2_1 : Fin 21 → Fin 8 → RI := ![tr1_2_1_0,tr1_2_1_1,tr1_2_1_2,tr1_2_1_3,tr1_2_1_4,tr1_2_1_5,tr1_2_1_6,tr1_2_1_7,tr1_2_1_8,tr1_2_1_9,tr1_2_1_10,tr1_2_1_11,tr1_2_1_12,tr1_2_1_13,tr1_2_1_14,tr1_2_1_15,tr1_2_1_16,tr1_2_1_17,tr1_2_1_18,tr1_2_1_19,tr1_2_1_20]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorRows13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

def tr1_3_0 : Fin 21 → Fin 8 → RI := ![tr1_3_0_0,tr1_3_0_1,tr1_3_0_2,tr1_3_0_3,tr1_3_0_4,tr1_3_0_5,tr1_3_0_6,tr1_3_0_7,tr1_3_0_8,tr1_3_0_9,tr1_3_0_10,tr1_3_0_11,tr1_3_0_12,tr1_3_0_13,tr1_3_0_14,tr1_3_0_15,tr1_3_0_16,tr1_3_0_17,tr1_3_0_18,tr1_3_0_19,tr1_3_0_20]
end AtomicTriangular.FiniteCertificate
end

end OAI
end


