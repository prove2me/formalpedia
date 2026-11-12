-- Prove2me | Definitions.Def_OAIQ262T121
-- name    : OAIQ262T121
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T16:57:23.608348+00:00
-- url     : https://prove2.me/theorems/b95576c4-7d4a-44d6-88d1-afdfab19b473
-- title:
--   Definitions bundle OAIQ262T121 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 theorem.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Signs_SineGrid0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/SineGrid0.lean).
--
--   **Imports.** It imports the bundle `OAIQ262T015` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ262T146`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ262T015

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
lemma cellGeometry09 (k : Fin 100) :
    0 ≤ cellMagnitude 9 k ∧ cellMagnitude 9 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 9 → 0 ≤ cellSeparation 9 k j ∧ cellSeparation 9 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0 ≤ cellMagnitude 9 k ∧ cellMagnitude 9 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 9 → 0 ≤ cellSeparation 9 k j ∧ cellSeparation 9 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end


