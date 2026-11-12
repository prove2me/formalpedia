-- Prove2me | Definitions.Def_OAIQ262T136
-- name    : OAIQ262T136
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T17:19:01.466203+00:00
-- url     : https://prove2.me/theorems/d3a91dbd-23a9-4c82-ab28-dfeb05e12e3a
-- title:
--   Definitions bundle OAIQ262T136 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 3 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Signs_ExceptionalInterval`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/ExceptionalInterval.lean), [`Triangular_Signs_SineGrid2`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/SineGrid2.lean).
--
--   **Imports.** It imports the bundles `OAIQ262T005` and `OAIQ262T015` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ262T146` and `OAIQ262T148`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ262T005
import Definitions.Def_OAIQ262T015

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_ExceptionalInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma ep2 : (RI.point 2).Mem (2 : ℝ) := by simpa using RI.mem_point 2
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
lemma cellGeometry28 (k : Fin 100) :
    0 ≤ cellMagnitude 28 k ∧ cellMagnitude 28 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 28 → 0 ≤ cellSeparation 28 k j ∧ cellSeparation 28 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0 ≤ cellMagnitude 28 k ∧ cellMagnitude 28 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 28 → 0 ≤ cellSeparation 28 k j ∧ cellSeparation 28 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellGeometry29 (k : Fin 100) :
    0 ≤ cellMagnitude 29 k ∧ cellMagnitude 29 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 29 → 0 ≤ cellSeparation 29 k j ∧ cellSeparation 29 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0 ≤ cellMagnitude 29 k ∧ cellMagnitude 29 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 29 → 0 ≤ cellSeparation 29 k j ∧ cellSeparation 29 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end


