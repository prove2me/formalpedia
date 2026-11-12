-- Prove2me | Definitions.Def_OAIQ250T063
-- name    : OAIQ250T063
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T13:44:50.375413+00:00
-- url     : https://prove2.me/theorems/e4dfe3a2-c37f-4d07-9b18-364cce41592e
-- title:
--   Definitions bundle OAIQ250T063 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2 declarations of OpenAI's Lean: 2 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Signs_SineGrid1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/SineGrid1.lean).
--
--   **Imports.** It imports the bundle `OAIQ250T011` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ250T086`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ250T011

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_SineGrid1
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


