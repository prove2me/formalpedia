-- Prove2me | Definitions.Def_OAIQ262T103
-- name    : OAIQ262T103
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T16:54:12.785471+00:00
-- url     : https://prove2.me/theorems/88646596-a521-4260-a7d0-de7e196008a3
-- title:
--   Definitions bundle OAIQ262T103 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 15 declarations of OpenAI's Lean: 4 definitions and 11 theorems. The definitions and types are `OAI.AtomicTriangular.FiniteCertificate.bs0_1_1`, `OAI.AtomicTriangular.FiniteCertificate.bs0_2_0`, `OAI.AtomicTriangular.FiniteCertificate.bs0_2_1`, `OAI.AtomicTriangular.FiniteCertificate.bs0_4_0`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Signs_ExceptionalSign3`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/ExceptionalSign3.lean), [`Triangular_Signs_Signs01`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/Signs01.lean), [`Triangular_Signs_Signs02`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/Signs02.lean), [`Triangular_Signs_Signs04`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/Signs04.lean), [`Triangular_Signs_SineGrid1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/SineGrid1.lean), [`Triangular_Taylor_TaylorExp00`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorExp00.lean).
--
--   **Imports.** It imports the bundles `OAIQ262T005`, `OAIQ262T013`, `OAIQ262T015`, `OAIQ262T020`, `OAIQ262T043`, `OAIQ262T045`, `OAIQ262T047`, `OAIQ262T048`, `OAIQ262T049`, `OAIQ262T050`, `OAIQ262T051`, `OAIQ262T053`, `OAIQ262T054`, `OAIQ262T055` and `OAIQ262T056` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ262T146`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ262T005
import Definitions.Def_OAIQ262T013
import Definitions.Def_OAIQ262T015
import Definitions.Def_OAIQ262T020
import Definitions.Def_OAIQ262T043
import Definitions.Def_OAIQ262T045
import Definitions.Def_OAIQ262T047
import Definitions.Def_OAIQ262T048
import Definitions.Def_OAIQ262T049
import Definitions.Def_OAIQ262T050
import Definitions.Def_OAIQ262T051
import Definitions.Def_OAIQ262T053
import Definitions.Def_OAIQ262T054
import Definitions.Def_OAIQ262T055
import Definitions.Def_OAIQ262T056

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
lemma taylorExp0_0_13_calc (j : Fin 31) : ((taylorPhase0_0 j).mul (CI.point 13)).exp = taylorExp0_0_13 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_ExceptionalSign3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma ex3b11_calc (r : Fin 8) : bernsteinRowsBox 22 ex3r 11 r = ex3b11 r := by
  revert r
  decide +kernel
lemma ex3b12_calc (r : Fin 8) : bernsteinRowsBox 22 ex3r 12 r = ex3b12 r := by
  revert r
  decide +kernel
lemma ex3b13_calc (r : Fin 8) : bernsteinRowsBox 22 ex3r 13 r = ex3b13 r := by
  revert r
  decide +kernel
lemma ex3b14_calc (r : Fin 8) : bernsteinRowsBox 22 ex3r 14 r = ex3b14 r := by
  revert r
  decide +kernel
lemma ex3b15_calc (r : Fin 8) : bernsteinRowsBox 22 ex3r 15 r = ex3b15 r := by
  revert r
  decide +kernel
lemma ex3b16_calc (r : Fin 8) : bernsteinRowsBox 22 ex3r 16 r = ex3b16 r := by
  revert r
  decide +kernel
lemma ex3b17_calc (r : Fin 8) : bernsteinRowsBox 22 ex3r 17 r = ex3b17 r := by
  revert r
  decide +kernel
lemma ex3b18_calc (r : Fin 8) : bernsteinRowsBox 22 ex3r 18 r = ex3b18 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_Signs01
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
def bs0_1_1 : Fin 21 → Fin 8 → RI := ![bs0_1_1_0,bs0_1_1_1,bs0_1_1_2,bs0_1_1_3,bs0_1_1_4,bs0_1_1_5,bs0_1_1_6,bs0_1_1_7,bs0_1_1_8,bs0_1_1_9,bs0_1_1_10,bs0_1_1_11,bs0_1_1_12,bs0_1_1_13,bs0_1_1_14,bs0_1_1_15,bs0_1_1_16,bs0_1_1_17,bs0_1_1_18,bs0_1_1_19,bs0_1_1_20]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_Signs02
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
def bs0_2_0 : Fin 21 → Fin 8 → RI := ![bs0_2_0_0,bs0_2_0_1,bs0_2_0_2,bs0_2_0_3,bs0_2_0_4,bs0_2_0_5,bs0_2_0_6,bs0_2_0_7,bs0_2_0_8,bs0_2_0_9,bs0_2_0_10,bs0_2_0_11,bs0_2_0_12,bs0_2_0_13,bs0_2_0_14,bs0_2_0_15,bs0_2_0_16,bs0_2_0_17,bs0_2_0_18,bs0_2_0_19,bs0_2_0_20]
def bs0_2_1 : Fin 21 → Fin 8 → RI := ![bs0_2_1_0,bs0_2_1_1,bs0_2_1_2,bs0_2_1_3,bs0_2_1_4,bs0_2_1_5,bs0_2_1_6,bs0_2_1_7,bs0_2_1_8,bs0_2_1_9,bs0_2_1_10,bs0_2_1_11,bs0_2_1_12,bs0_2_1_13,bs0_2_1_14,bs0_2_1_15,bs0_2_1_16,bs0_2_1_17,bs0_2_1_18,bs0_2_1_19,bs0_2_1_20]
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
def bs0_4_0 : Fin 21 → Fin 8 → RI := ![bs0_4_0_0,bs0_4_0_1,bs0_4_0_2,bs0_4_0_3,bs0_4_0_4,bs0_4_0_5,bs0_4_0_6,bs0_4_0_7,bs0_4_0_8,bs0_4_0_9,bs0_4_0_10,bs0_4_0_11,bs0_4_0_12,bs0_4_0_13,bs0_4_0_14,bs0_4_0_15,bs0_4_0_16,bs0_4_0_17,bs0_4_0_18,bs0_4_0_19,bs0_4_0_20]
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
lemma cellFactors12 (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 12 k j) ∧ cellBarrier 12 < ∏ j : Fin 15,(cellFactor 12 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 12 k j) ∧ cellBarrier 12 < ∏ j : Fin 15,(cellFactor 12 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors13 (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 13 k j) ∧ cellBarrier 13 < ∏ j : Fin 15,(cellFactor 13 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 13 k j) ∧ cellBarrier 13 < ∏ j : Fin 15,(cellFactor 13 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end


