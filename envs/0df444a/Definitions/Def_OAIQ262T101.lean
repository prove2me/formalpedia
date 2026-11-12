-- Prove2me | Definitions.Def_OAIQ262T101
-- name    : OAIQ262T101
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T16:56:13.635087+00:00
-- url     : https://prove2.me/theorems/c6cc1d3e-366d-44a7-bdef-d3288684bccc
-- title:
--   Definitions bundle OAIQ262T101 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 28 declarations of OpenAI's Lean: 25 definitions and 3 theorems. The definitions and types are `OAI.AtomicTriangular.FiniteCertificate.spectrum1_0`, `OAI.AtomicTriangular.FiniteCertificate.taylorExpTable`, `OAI.AtomicTriangular.FiniteCertificate.tr1_6_0`, `OAI.AtomicTriangular.FiniteCertificate.tr1_6_1`, `OAI.AtomicTriangular.FiniteCertificate.tw0_0_4`, `OAI.AtomicTriangular.FiniteCertificate.tw0_1`, `OAI.AtomicTriangular.FiniteCertificate.tw0_1_0`, `OAI.AtomicTriangular.FiniteCertificate.tw0_1_1`, `OAI.AtomicTriangular.FiniteCertificate.tw0_1_3`, `OAI.AtomicTriangular.FiniteCertificate.tw0_1_4`, `OAI.AtomicTriangular.FiniteCertificate.tw0_1_5`, `OAI.AtomicTriangular.FiniteCertificate.tw0_1_6`, `OAI.AtomicTriangular.FiniteCertificate.tw1_0`, `OAI.AtomicTriangular.FiniteCertificate.tw1_0_1`, `OAI.AtomicTriangular.FiniteCertificate.tw1_0_2`, `OAI.AtomicTriangular.FiniteCertificate.tw1_0_3`, `OAI.AtomicTriangular.FiniteCertificate.tw1_0_5`, `OAI.AtomicTriangular.FiniteCertificate.tw1_0_6`, `OAI.AtomicTriangular.FiniteCertificate.tw1_1`, `OAI.AtomicTriangular.FiniteCertificate.tw1_1_0`, `OAI.AtomicTriangular.FiniteCertificate.tw1_1_2`, `OAI.AtomicTriangular.FiniteCertificate.tw1_1_3`, `OAI.AtomicTriangular.FiniteCertificate.tw1_1_4`, `OAI.AtomicTriangular.FiniteCertificate.tw1_1_5`, `OAI.AtomicTriangular.FiniteCertificate.tw1_1_6`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `Triangular_Signs_SineGrid0`, `Triangular_Taylor_TaylorExp`, `Triangular_Taylor_TaylorRows16`, `Triangular_Taylor_TaylorRowsBase`, `Triangular_Taylor_TaylorSpectrum`, `Triangular_Taylor_TaylorWave004`, `Triangular_Taylor_TaylorWave01`, `Triangular_Taylor_TaylorWave010`, `Triangular_Taylor_TaylorWave011`, `Triangular_Taylor_TaylorWave013`, `Triangular_Taylor_TaylorWave014`, `Triangular_Taylor_TaylorWave015`, `Triangular_Taylor_TaylorWave016`, `Triangular_Taylor_TaylorWave10`, `Triangular_Taylor_TaylorWave101`, `Triangular_Taylor_TaylorWave102`, `Triangular_Taylor_TaylorWave103`, `Triangular_Taylor_TaylorWave105`, `Triangular_Taylor_TaylorWave106`, `Triangular_Taylor_TaylorWave11`, `Triangular_Taylor_TaylorWave110`, `Triangular_Taylor_TaylorWave112`, `Triangular_Taylor_TaylorWave113`, `Triangular_Taylor_TaylorWave114`, `Triangular_Taylor_TaylorWave115`, `Triangular_Taylor_TaylorWave116`.
--
--   **Imports.** It imports the bundles `OAIQ262T005`, `OAIQ262T015`, `OAIQ262T019`, `OAIQ262T021`, `OAIQ262T022`, `OAIQ262T025`, `OAIQ262T026`, `OAIQ262T027`, `OAIQ262T028`, `OAIQ262T029`, `OAIQ262T030`, `OAIQ262T031`, `OAIQ262T032`, `OAIQ262T033`, `OAIQ262T034`, `OAIQ262T035`, `OAIQ262T036`, `OAIQ262T037`, `OAIQ262T038`, `OAIQ262T039`, `OAIQ262T040`, `OAIQ262T041`, `OAIQ262T042`, `OAIQ262T043`, `OAIQ262T044`, `OAIQ262T045`, `OAIQ262T081`, `OAIQ262T082`, `OAIQ262T083` and `OAIQ262T084` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ262T143`, `OAIQ262T146`, `OAIQ262T148`, `OAIQ262T191` and `OAIQ262T192`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ262T005
import Definitions.Def_OAIQ262T015
import Definitions.Def_OAIQ262T019
import Definitions.Def_OAIQ262T021
import Definitions.Def_OAIQ262T022
import Definitions.Def_OAIQ262T025
import Definitions.Def_OAIQ262T026
import Definitions.Def_OAIQ262T027
import Definitions.Def_OAIQ262T028
import Definitions.Def_OAIQ262T029
import Definitions.Def_OAIQ262T030
import Definitions.Def_OAIQ262T031
import Definitions.Def_OAIQ262T032
import Definitions.Def_OAIQ262T033
import Definitions.Def_OAIQ262T034
import Definitions.Def_OAIQ262T035
import Definitions.Def_OAIQ262T036
import Definitions.Def_OAIQ262T037
import Definitions.Def_OAIQ262T038
import Definitions.Def_OAIQ262T039
import Definitions.Def_OAIQ262T040
import Definitions.Def_OAIQ262T041
import Definitions.Def_OAIQ262T042
import Definitions.Def_OAIQ262T043
import Definitions.Def_OAIQ262T044
import Definitions.Def_OAIQ262T045
import Definitions.Def_OAIQ262T081
import Definitions.Def_OAIQ262T082
import Definitions.Def_OAIQ262T083
import Definitions.Def_OAIQ262T084

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
lemma cellFactors08 (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 8 k j) ∧ cellBarrier 8 < ∏ j : Fin 15,(cellFactor 8 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 8 k j) ∧ cellBarrier 8 < ∏ j : Fin 15,(cellFactor 8 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors09 (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 9 k j) ∧ cellBarrier 9 < ∏ j : Fin 15,(cellFactor 9 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 9 k j) ∧ cellBarrier 9 < ∏ j : Fin 15,(cellFactor 9 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorExp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def taylorExpTable : Fin 2 → Fin 2 → Fin 7 → Fin 31 → CI := ![![![taylorExp0_0_1,taylorExp0_0_3,taylorExp0_0_4,taylorExp0_0_7,taylorExp0_0_9,taylorExp0_0_12,taylorExp0_0_13],![taylorExp0_1_1,taylorExp0_1_3,taylorExp0_1_4,taylorExp0_1_7,taylorExp0_1_9,taylorExp0_1_12,taylorExp0_1_13]],![![taylorExp1_0_1,taylorExp1_0_3,taylorExp1_0_4,taylorExp1_0_7,taylorExp1_0_9,taylorExp1_0_12,taylorExp1_0_13],![taylorExp1_1_1,taylorExp1_1_3,taylorExp1_1_4,taylorExp1_1_7,taylorExp1_1_9,taylorExp1_1_12,taylorExp1_1_13]]]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def spectrum1_0 : Fin 31 → Fin 8 → CI := ![spectrum1_0_0,spectrum1_0_1,spectrum1_0_2,spectrum1_0_3,spectrum1_0_4,spectrum1_0_5,spectrum1_0_6,spectrum1_0_7,spectrum1_0_8,spectrum1_0_9,spectrum1_0_10,spectrum1_0_11,spectrum1_0_12,spectrum1_0_13,spectrum1_0_14,spectrum1_0_15,spectrum1_0_16,spectrum1_0_17,spectrum1_0_18,spectrum1_0_19,spectrum1_0_20,spectrum1_0_21,spectrum1_0_22,spectrum1_0_23,spectrum1_0_24,spectrum1_0_25,spectrum1_0_26,spectrum1_0_27,spectrum1_0_28,spectrum1_0_29,spectrum1_0_30]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave004
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def tw0_0_4 : Fin 21 → Fin 31 → CI := ![tw0_0_4_0,tw0_0_4_1,tw0_0_4_2,tw0_0_4_3,tw0_0_4_4,tw0_0_4_5,tw0_0_4_6,tw0_0_4_7,tw0_0_4_8,tw0_0_4_9,tw0_0_4_10,tw0_0_4_11,tw0_0_4_12,tw0_0_4_13,tw0_0_4_14,tw0_0_4_15,tw0_0_4_16,tw0_0_4_17,tw0_0_4_18,tw0_0_4_19,tw0_0_4_20]

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave010
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def tw0_1_0 : Fin 21 → Fin 31 → CI := ![tw0_1_0_0,tw0_1_0_1,tw0_1_0_2,tw0_1_0_3,tw0_1_0_4,tw0_1_0_5,tw0_1_0_6,tw0_1_0_7,tw0_1_0_8,tw0_1_0_9,tw0_1_0_10,tw0_1_0_11,tw0_1_0_12,tw0_1_0_13,tw0_1_0_14,tw0_1_0_15,tw0_1_0_16,tw0_1_0_17,tw0_1_0_18,tw0_1_0_19,tw0_1_0_20]

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave011
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def tw0_1_1 : Fin 21 → Fin 31 → CI := ![tw0_1_1_0,tw0_1_1_1,tw0_1_1_2,tw0_1_1_3,tw0_1_1_4,tw0_1_1_5,tw0_1_1_6,tw0_1_1_7,tw0_1_1_8,tw0_1_1_9,tw0_1_1_10,tw0_1_1_11,tw0_1_1_12,tw0_1_1_13,tw0_1_1_14,tw0_1_1_15,tw0_1_1_16,tw0_1_1_17,tw0_1_1_18,tw0_1_1_19,tw0_1_1_20]

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave013
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def tw0_1_3 : Fin 21 → Fin 31 → CI := ![tw0_1_3_0,tw0_1_3_1,tw0_1_3_2,tw0_1_3_3,tw0_1_3_4,tw0_1_3_5,tw0_1_3_6,tw0_1_3_7,tw0_1_3_8,tw0_1_3_9,tw0_1_3_10,tw0_1_3_11,tw0_1_3_12,tw0_1_3_13,tw0_1_3_14,tw0_1_3_15,tw0_1_3_16,tw0_1_3_17,tw0_1_3_18,tw0_1_3_19,tw0_1_3_20]

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave014
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def tw0_1_4 : Fin 21 → Fin 31 → CI := ![tw0_1_4_0,tw0_1_4_1,tw0_1_4_2,tw0_1_4_3,tw0_1_4_4,tw0_1_4_5,tw0_1_4_6,tw0_1_4_7,tw0_1_4_8,tw0_1_4_9,tw0_1_4_10,tw0_1_4_11,tw0_1_4_12,tw0_1_4_13,tw0_1_4_14,tw0_1_4_15,tw0_1_4_16,tw0_1_4_17,tw0_1_4_18,tw0_1_4_19,tw0_1_4_20]

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave015
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def tw0_1_5 : Fin 21 → Fin 31 → CI := ![tw0_1_5_0,tw0_1_5_1,tw0_1_5_2,tw0_1_5_3,tw0_1_5_4,tw0_1_5_5,tw0_1_5_6,tw0_1_5_7,tw0_1_5_8,tw0_1_5_9,tw0_1_5_10,tw0_1_5_11,tw0_1_5_12,tw0_1_5_13,tw0_1_5_14,tw0_1_5_15,tw0_1_5_16,tw0_1_5_17,tw0_1_5_18,tw0_1_5_19,tw0_1_5_20]

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave016
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def tw0_1_6 : Fin 21 → Fin 31 → CI := ![tw0_1_6_0,tw0_1_6_1,tw0_1_6_2,tw0_1_6_3,tw0_1_6_4,tw0_1_6_5,tw0_1_6_6,tw0_1_6_7,tw0_1_6_8,tw0_1_6_9,tw0_1_6_10,tw0_1_6_11,tw0_1_6_12,tw0_1_6_13,tw0_1_6_14,tw0_1_6_15,tw0_1_6_16,tw0_1_6_17,tw0_1_6_18,tw0_1_6_19,tw0_1_6_20]

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave01
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def tw0_1 : Fin 7 → Fin 21 → Fin 31 → CI := ![tw0_1_0,tw0_1_1,tw0_1_2,tw0_1_3,tw0_1_4,tw0_1_5,tw0_1_6]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave101
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def tw1_0_1 : Fin 21 → Fin 31 → CI := ![tw1_0_1_0,tw1_0_1_1,tw1_0_1_2,tw1_0_1_3,tw1_0_1_4,tw1_0_1_5,tw1_0_1_6,tw1_0_1_7,tw1_0_1_8,tw1_0_1_9,tw1_0_1_10,tw1_0_1_11,tw1_0_1_12,tw1_0_1_13,tw1_0_1_14,tw1_0_1_15,tw1_0_1_16,tw1_0_1_17,tw1_0_1_18,tw1_0_1_19,tw1_0_1_20]

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave102
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def tw1_0_2 : Fin 21 → Fin 31 → CI := ![tw1_0_2_0,tw1_0_2_1,tw1_0_2_2,tw1_0_2_3,tw1_0_2_4,tw1_0_2_5,tw1_0_2_6,tw1_0_2_7,tw1_0_2_8,tw1_0_2_9,tw1_0_2_10,tw1_0_2_11,tw1_0_2_12,tw1_0_2_13,tw1_0_2_14,tw1_0_2_15,tw1_0_2_16,tw1_0_2_17,tw1_0_2_18,tw1_0_2_19,tw1_0_2_20]

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave103
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def tw1_0_3 : Fin 21 → Fin 31 → CI := ![tw1_0_3_0,tw1_0_3_1,tw1_0_3_2,tw1_0_3_3,tw1_0_3_4,tw1_0_3_5,tw1_0_3_6,tw1_0_3_7,tw1_0_3_8,tw1_0_3_9,tw1_0_3_10,tw1_0_3_11,tw1_0_3_12,tw1_0_3_13,tw1_0_3_14,tw1_0_3_15,tw1_0_3_16,tw1_0_3_17,tw1_0_3_18,tw1_0_3_19,tw1_0_3_20]

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave105
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def tw1_0_5 : Fin 21 → Fin 31 → CI := ![tw1_0_5_0,tw1_0_5_1,tw1_0_5_2,tw1_0_5_3,tw1_0_5_4,tw1_0_5_5,tw1_0_5_6,tw1_0_5_7,tw1_0_5_8,tw1_0_5_9,tw1_0_5_10,tw1_0_5_11,tw1_0_5_12,tw1_0_5_13,tw1_0_5_14,tw1_0_5_15,tw1_0_5_16,tw1_0_5_17,tw1_0_5_18,tw1_0_5_19,tw1_0_5_20]

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave106
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def tw1_0_6 : Fin 21 → Fin 31 → CI := ![tw1_0_6_0,tw1_0_6_1,tw1_0_6_2,tw1_0_6_3,tw1_0_6_4,tw1_0_6_5,tw1_0_6_6,tw1_0_6_7,tw1_0_6_8,tw1_0_6_9,tw1_0_6_10,tw1_0_6_11,tw1_0_6_12,tw1_0_6_13,tw1_0_6_14,tw1_0_6_15,tw1_0_6_16,tw1_0_6_17,tw1_0_6_18,tw1_0_6_19,tw1_0_6_20]

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def tw1_0 : Fin 7 → Fin 21 → Fin 31 → CI := ![tw1_0_0,tw1_0_1,tw1_0_2,tw1_0_3,tw1_0_4,tw1_0_5,tw1_0_6]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave110
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def tw1_1_0 : Fin 21 → Fin 31 → CI := ![tw1_1_0_0,tw1_1_0_1,tw1_1_0_2,tw1_1_0_3,tw1_1_0_4,tw1_1_0_5,tw1_1_0_6,tw1_1_0_7,tw1_1_0_8,tw1_1_0_9,tw1_1_0_10,tw1_1_0_11,tw1_1_0_12,tw1_1_0_13,tw1_1_0_14,tw1_1_0_15,tw1_1_0_16,tw1_1_0_17,tw1_1_0_18,tw1_1_0_19,tw1_1_0_20]

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave112
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def tw1_1_2 : Fin 21 → Fin 31 → CI := ![tw1_1_2_0,tw1_1_2_1,tw1_1_2_2,tw1_1_2_3,tw1_1_2_4,tw1_1_2_5,tw1_1_2_6,tw1_1_2_7,tw1_1_2_8,tw1_1_2_9,tw1_1_2_10,tw1_1_2_11,tw1_1_2_12,tw1_1_2_13,tw1_1_2_14,tw1_1_2_15,tw1_1_2_16,tw1_1_2_17,tw1_1_2_18,tw1_1_2_19,tw1_1_2_20]

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave113
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def tw1_1_3 : Fin 21 → Fin 31 → CI := ![tw1_1_3_0,tw1_1_3_1,tw1_1_3_2,tw1_1_3_3,tw1_1_3_4,tw1_1_3_5,tw1_1_3_6,tw1_1_3_7,tw1_1_3_8,tw1_1_3_9,tw1_1_3_10,tw1_1_3_11,tw1_1_3_12,tw1_1_3_13,tw1_1_3_14,tw1_1_3_15,tw1_1_3_16,tw1_1_3_17,tw1_1_3_18,tw1_1_3_19,tw1_1_3_20]

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave114
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def tw1_1_4 : Fin 21 → Fin 31 → CI := ![tw1_1_4_0,tw1_1_4_1,tw1_1_4_2,tw1_1_4_3,tw1_1_4_4,tw1_1_4_5,tw1_1_4_6,tw1_1_4_7,tw1_1_4_8,tw1_1_4_9,tw1_1_4_10,tw1_1_4_11,tw1_1_4_12,tw1_1_4_13,tw1_1_4_14,tw1_1_4_15,tw1_1_4_16,tw1_1_4_17,tw1_1_4_18,tw1_1_4_19,tw1_1_4_20]

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave115
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def tw1_1_5 : Fin 21 → Fin 31 → CI := ![tw1_1_5_0,tw1_1_5_1,tw1_1_5_2,tw1_1_5_3,tw1_1_5_4,tw1_1_5_5,tw1_1_5_6,tw1_1_5_7,tw1_1_5_8,tw1_1_5_9,tw1_1_5_10,tw1_1_5_11,tw1_1_5_12,tw1_1_5_13,tw1_1_5_14,tw1_1_5_15,tw1_1_5_16,tw1_1_5_17,tw1_1_5_18,tw1_1_5_19,tw1_1_5_20]

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave116
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def tw1_1_6 : Fin 21 → Fin 31 → CI := ![tw1_1_6_0,tw1_1_6_1,tw1_1_6_2,tw1_1_6_3,tw1_1_6_4,tw1_1_6_5,tw1_1_6_6,tw1_1_6_7,tw1_1_6_8,tw1_1_6_9,tw1_1_6_10,tw1_1_6_11,tw1_1_6_12,tw1_1_6_13,tw1_1_6_14,tw1_1_6_15,tw1_1_6_16,tw1_1_6_17,tw1_1_6_18,tw1_1_6_19,tw1_1_6_20]

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def tw1_1 : Fin 7 → Fin 21 → Fin 31 → CI := ![tw1_1_0,tw1_1_1,tw1_1_2,tw1_1_3,tw1_1_4,tw1_1_5,tw1_1_6]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorRowsBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma nearDisplacementBox_mem (n : Fin 7) (y : Fin 2) :
    (nearDisplacementBox n y).Mem (nearDisplacement n y) := by
  exact RI.mem_divNat (RI.mem_point _) (by norm_num)
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorRows16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

def tr1_6_0 : Fin 21 → Fin 8 → RI := ![tr1_6_0_0,tr1_6_0_1,tr1_6_0_2,tr1_6_0_3,tr1_6_0_4,tr1_6_0_5,tr1_6_0_6,tr1_6_0_7,tr1_6_0_8,tr1_6_0_9,tr1_6_0_10,tr1_6_0_11,tr1_6_0_12,tr1_6_0_13,tr1_6_0_14,tr1_6_0_15,tr1_6_0_16,tr1_6_0_17,tr1_6_0_18,tr1_6_0_19,tr1_6_0_20]
def tr1_6_1 : Fin 21 → Fin 8 → RI := ![tr1_6_1_0,tr1_6_1_1,tr1_6_1_2,tr1_6_1_3,tr1_6_1_4,tr1_6_1_5,tr1_6_1_6,tr1_6_1_7,tr1_6_1_8,tr1_6_1_9,tr1_6_1_10,tr1_6_1_11,tr1_6_1_12,tr1_6_1_13,tr1_6_1_14,tr1_6_1_15,tr1_6_1_16,tr1_6_1_17,tr1_6_1_18,tr1_6_1_19,tr1_6_1_20]
end AtomicTriangular.FiniteCertificate
end

end OAI
end


