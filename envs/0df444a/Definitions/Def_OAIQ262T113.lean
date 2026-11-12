-- Prove2me | Definitions.Def_OAIQ262T113
-- name    : OAIQ262T113
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T16:56:26.529668+00:00
-- url     : https://prove2.me/theorems/e2753524-30a2-4dcc-b216-f5a2c4279ba0
-- title:
--   Definitions bundle OAIQ262T113 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 11 declarations of OpenAI's Lean: 1 definition and 10 theorems. The definitions and types are `OAI.AtomicTriangular.FiniteCertificate.ordinaryOffsetBox`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Signs_ExceptionalSign2`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/ExceptionalSign2.lean), [`Triangular_Signs_SignBase`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/SignBase.lean), [`Triangular_Signs_SineGrid0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/SineGrid0.lean), [`Triangular_Taylor_TaylorExp10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorExp10.lean).
--
--   **Imports.** It imports the bundles `OAIQ262T005`, `OAIQ262T012`, `OAIQ262T013`, `OAIQ262T015`, `OAIQ262T020`, `OAIQ262T043`, `OAIQ262T044` and `OAIQ262T045` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ262T146`, `OAIQ262T147` and `OAIQ262T149`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ262T005
import Definitions.Def_OAIQ262T012
import Definitions.Def_OAIQ262T013
import Definitions.Def_OAIQ262T015
import Definitions.Def_OAIQ262T020
import Definitions.Def_OAIQ262T043
import Definitions.Def_OAIQ262T044
import Definitions.Def_OAIQ262T045

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorExp10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma taylorExp1_0_1_calc (j : Fin 31) : ((taylorPhase1_0 j).mul (CI.point 1)).exp = taylorExp1_0_1 j := by
  revert j
  decide +kernel
lemma taylorExp1_0_3_calc (j : Fin 31) : ((taylorPhase1_0 j).mul (CI.point 3)).exp = taylorExp1_0_3 j := by
  revert j
  decide +kernel
lemma taylorExp1_0_4_calc (j : Fin 31) : ((taylorPhase1_0 j).mul (CI.point 4)).exp = taylorExp1_0_4 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_ExceptionalSign2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma ex2b1_calc (r : Fin 8) : bernsteinRowsBox 22 ex2r 1 r = ex2b1 r := by
  revert r
  decide +kernel
lemma ex2b15_calc (r : Fin 8) : bernsteinRowsBox 22 ex2r 15 r = ex2b15 r := by
  revert r
  decide +kernel
lemma ex2b16_calc (r : Fin 8) : bernsteinRowsBox 22 ex2r 16 r = ex2b16 r := by
  revert r
  decide +kernel
lemma ex2b17_calc (r : Fin 8) : bernsteinRowsBox 22 ex2r 17 r = ex2b17 r := by
  revert r
  decide +kernel
lemma ex2b18_calc (r : Fin 8) : bernsteinRowsBox 22 ex2r 18 r = ex2b18 r := by
  revert r
  decide +kernel
lemma ex2b19_calc (r : Fin 8) : bernsteinRowsBox 22 ex2r 19 r = ex2b19 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_SignBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

def ordinaryOffsetBox (n : Fin 7) (r : Fin 8) : RI :=
  if n.val=0 ∧ r.val=1 then QBox1.mul ((RI.point 2).mul ZBox).invPos
  else if n.val=1 ∧ r.val=3 then ((RI.point 4).divNat 5).mul QBox1 else RI.point 0
end AtomicTriangular.FiniteCertificate
end

end OAI
end

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
lemma cellGeometry01 (k : Fin 100) :
    0 ≤ cellMagnitude 1 k ∧ cellMagnitude 1 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 1 → 0 ≤ cellSeparation 1 k j ∧ cellSeparation 1 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0 ≤ cellMagnitude 1 k ∧ cellMagnitude 1 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 1 → 0 ≤ cellSeparation 1 k j ∧ cellSeparation 1 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end


