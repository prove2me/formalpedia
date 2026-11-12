-- Prove2me | Definitions.Def_OAIQ262T106
-- name    : OAIQ262T106
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T16:55:12.153811+00:00
-- url     : https://prove2.me/theorems/05039302-2784-4aa9-bf04-51004972337f
-- title:
--   Definitions bundle OAIQ262T106 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 16 declarations of OpenAI's Lean: 5 definitions and 11 theorems. The definitions and types are `OAI.AtomicTriangular.FiniteCertificate.bs1_0_1`, `OAI.AtomicTriangular.FiniteCertificate.bs1_1_0`, `OAI.AtomicTriangular.FiniteCertificate.bs1_1_1`, `OAI.AtomicTriangular.FiniteCertificate.bs1_2_0`, `OAI.AtomicTriangular.FiniteCertificate.bs1_3_0`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Signs_ExceptionalSign3`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/ExceptionalSign3.lean), [`Triangular_Signs_Signs10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/Signs10.lean), [`Triangular_Signs_Signs11`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/Signs11.lean), [`Triangular_Signs_Signs12`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/Signs12.lean), [`Triangular_Signs_Signs13`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/Signs13.lean), [`Triangular_Signs_SineGrid1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/SineGrid1.lean), [`Triangular_Taylor_TaylorExp00`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorExp00.lean).
--
--   **Imports.** It imports the bundles `OAIQ262T005`, `OAIQ262T013`, `OAIQ262T015`, `OAIQ262T020`, `OAIQ262T044`, `OAIQ262T045`, `OAIQ262T050`, `OAIQ262T064`, `OAIQ262T065`, `OAIQ262T066`, `OAIQ262T067`, `OAIQ262T068`, `OAIQ262T069`, `OAIQ262T070`, `OAIQ262T071`, `OAIQ262T072` and `OAIQ262T073` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ262T146`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ262T005
import Definitions.Def_OAIQ262T013
import Definitions.Def_OAIQ262T015
import Definitions.Def_OAIQ262T020
import Definitions.Def_OAIQ262T044
import Definitions.Def_OAIQ262T045
import Definitions.Def_OAIQ262T050
import Definitions.Def_OAIQ262T064
import Definitions.Def_OAIQ262T065
import Definitions.Def_OAIQ262T066
import Definitions.Def_OAIQ262T067
import Definitions.Def_OAIQ262T068
import Definitions.Def_OAIQ262T069
import Definitions.Def_OAIQ262T070
import Definitions.Def_OAIQ262T071
import Definitions.Def_OAIQ262T072
import Definitions.Def_OAIQ262T073

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
lemma taylorExp0_0_4_calc (j : Fin 31) : ((taylorPhase0_0 j).mul (CI.point 4)).exp = taylorExp0_0_4 j := by
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
lemma ex3b19_calc (r : Fin 8) : bernsteinRowsBox 22 ex3r 19 r = ex3b19 r := by
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
def bs1_0_1 : Fin 21 → Fin 8 → RI := ![bs1_0_1_0,bs1_0_1_1,bs1_0_1_2,bs1_0_1_3,bs1_0_1_4,bs1_0_1_5,bs1_0_1_6,bs1_0_1_7,bs1_0_1_8,bs1_0_1_9,bs1_0_1_10,bs1_0_1_11,bs1_0_1_12,bs1_0_1_13,bs1_0_1_14,bs1_0_1_15,bs1_0_1_16,bs1_0_1_17,bs1_0_1_18,bs1_0_1_19,bs1_0_1_20]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_Signs11
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
def bs1_1_1 : Fin 21 → Fin 8 → RI := ![bs1_1_1_0,bs1_1_1_1,bs1_1_1_2,bs1_1_1_3,bs1_1_1_4,bs1_1_1_5,bs1_1_1_6,bs1_1_1_7,bs1_1_1_8,bs1_1_1_9,bs1_1_1_10,bs1_1_1_11,bs1_1_1_12,bs1_1_1_13,bs1_1_1_14,bs1_1_1_15,bs1_1_1_16,bs1_1_1_17,bs1_1_1_18,bs1_1_1_19,bs1_1_1_20]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_Signs12
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
def bs1_3_0 : Fin 21 → Fin 8 → RI := ![bs1_3_0_0,bs1_3_0_1,bs1_3_0_2,bs1_3_0_3,bs1_3_0_4,bs1_3_0_5,bs1_3_0_6,bs1_3_0_7,bs1_3_0_8,bs1_3_0_9,bs1_3_0_10,bs1_3_0_11,bs1_3_0_12,bs1_3_0_13,bs1_3_0_14,bs1_3_0_15,bs1_3_0_16,bs1_3_0_17,bs1_3_0_18,bs1_3_0_19,bs1_3_0_20]
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
lemma cellFactors18 (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 18 k j) ∧ cellBarrier 18 < ∏ j : Fin 15,(cellFactor 18 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 18 k j) ∧ cellBarrier 18 < ∏ j : Fin 15,(cellFactor 18 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors19 (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 19 k j) ∧ cellBarrier 19 < ∏ j : Fin 15,(cellFactor 19 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 19 k j) ∧ cellBarrier 19 < ∏ j : Fin 15,(cellFactor 19 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end


