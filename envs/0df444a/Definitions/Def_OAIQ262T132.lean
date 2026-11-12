-- Prove2me | Definitions.Def_OAIQ262T132
-- name    : OAIQ262T132
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T17:19:00.84261+00:00
-- url     : https://prove2.me/theorems/83e8642e-9a33-4e92-a542-6fbd5f98886d
-- title:
--   Definitions bundle OAIQ262T132 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 5 declarations of OpenAI's Lean: 3 definitions and 2 theorems. The definitions and types are `OAI.AtomicTriangular.Construction.rawRemainderColumn`, `OAI.AtomicTriangular.Construction.remainderWave`, `OAI.AtomicTriangular.FiniteCertificate.remainderExpInput`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Signs_RemainderBoxes`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/RemainderBoxes.lean), [`Triangular_Signs_SineGrid2`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/SineGrid2.lean).
--
--   **Imports.** It imports the published bundle `Def_TriangularGaussian`; the bundles `OAIQ262T012`, `OAIQ262T013` and `OAIQ262T015` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ262T144`, `OAIQ262T146` and `OAIQ262T147`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_TriangularGaussian
import Definitions.Def_OAIQ262T012
import Definitions.Def_OAIQ262T013
import Definitions.Def_OAIQ262T015

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_RemainderBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open AtomicTriangular.FiniteCertificate
namespace AtomicTriangular.Construction

def remainderWave (q br : Fin 2) (m Y t : ℝ) : ℝ :=
  curvatureWave q br m t * (Y*‖taylorPhase q br t‖)^21 / (23).factorial /
    (1-Y*‖taylorPhase q br t‖/24)
def rawRemainderColumn (br : Fin 2) (n : Fin 7) (c : Fin 22) : ℝ :=
  ∑ j : Fin 31, remainderWave 1 br (nearNode n) (nearRadius n) (frequency j)*
    ‖finiteColumn ⟨c.val,by omega⟩ j‖
end AtomicTriangular.Construction
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def remainderExpInput (q br : Fin 2) (n : Fin 7) (j : Fin 31) : CI :=
  CI.ofReal ((taylorPhaseTable q br j).re.mul (RI.point (nearNode n)))
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
lemma cellGeometry20 (k : Fin 100) :
    0 ≤ cellMagnitude 20 k ∧ cellMagnitude 20 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 20 → 0 ≤ cellSeparation 20 k j ∧ cellSeparation 20 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0 ≤ cellMagnitude 20 k ∧ cellMagnitude 20 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 20 → 0 ≤ cellSeparation 20 k j ∧ cellSeparation 20 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellGeometry21 (k : Fin 100) :
    0 ≤ cellMagnitude 21 k ∧ cellMagnitude 21 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 21 → 0 ≤ cellSeparation 21 k j ∧ cellSeparation 21 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0 ≤ cellMagnitude 21 k ∧ cellMagnitude 21 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 21 → 0 ≤ cellSeparation 21 k j ∧ cellSeparation 21 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end


