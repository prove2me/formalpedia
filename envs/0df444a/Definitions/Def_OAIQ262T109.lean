-- Prove2me | Definitions.Def_OAIQ262T109
-- name    : OAIQ262T109
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T16:55:22.151171+00:00
-- url     : https://prove2.me/theorems/07adf23c-63dd-431f-a5f8-d572c4690470
-- title:
--   Definitions bundle OAIQ262T109 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 3 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Signs_SineGrid2`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/SineGrid2.lean), [`Triangular_Taylor_TaylorExp01`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorExp01.lean).
--
--   **Imports.** It imports the bundles `OAIQ262T005`, `OAIQ262T013`, `OAIQ262T015` and `OAIQ262T044` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ262T146`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ262T005
import Definitions.Def_OAIQ262T013
import Definitions.Def_OAIQ262T015
import Definitions.Def_OAIQ262T044

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
lemma cellFactors24 (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 24 k j) ∧ cellBarrier 24 < ∏ j : Fin 15,(cellFactor 24 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 24 k j) ∧ cellBarrier 24 < ∏ j : Fin 15,(cellFactor 24 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors25 (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 25 k j) ∧ cellBarrier 25 < ∏ j : Fin 15,(cellFactor 25 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 25 k j) ∧ cellBarrier 25 < ∏ j : Fin 15,(cellFactor 25 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end

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
lemma taylorExp0_1_13_calc (j : Fin 31) : ((taylorPhase0_1 j).mul (CI.point 13)).exp = taylorExp0_1_13 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end


