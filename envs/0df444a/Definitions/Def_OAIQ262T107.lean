-- Prove2me | Definitions.Def_OAIQ262T107
-- name    : OAIQ262T107
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T16:54:46.821195+00:00
-- url     : https://prove2.me/theorems/3aad5a62-666d-4e55-bdc3-20aa90ee5e35
-- title:
--   Definitions bundle OAIQ262T107 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 3 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Signs_SineGrid2`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/SineGrid2.lean), [`Triangular_Taylor_TaylorExp00`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorExp00.lean).
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
lemma cellFactors20 (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 20 k j) ∧ cellBarrier 20 < ∏ j : Fin 15,(cellFactor 20 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 20 k j) ∧ cellBarrier 20 < ∏ j : Fin 15,(cellFactor 20 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors21 (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 21 k j) ∧ cellBarrier 21 < ∏ j : Fin 15,(cellFactor 21 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 21 k j) ∧ cellBarrier 21 < ∏ j : Fin 15,(cellFactor 21 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end

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
lemma taylorExp0_0_7_calc (j : Fin 31) : ((taylorPhase0_0 j).mul (CI.point 7)).exp = taylorExp0_0_7 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end


