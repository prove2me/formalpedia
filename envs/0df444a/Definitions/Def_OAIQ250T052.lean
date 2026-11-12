-- Prove2me | Definitions.Def_OAIQ250T052
-- name    : OAIQ250T052
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T11:16:59.371714+00:00
-- url     : https://prove2.me/theorems/5e98471b-7b70-4d6a-9f8a-ffbb061f8867
-- title:
--   Definitions bundle OAIQ250T052 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 14 declarations of OpenAI's Lean: 1 definition and 13 theorems. The definitions and types are `OAI.AtomicTriangular.FiniteCertificate.ordinaryOffsetBox`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Signs_ExceptionalSign3`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/ExceptionalSign3.lean), [`Triangular_Signs_SignBase`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/SignBase.lean), [`Triangular_Signs_SineGrid0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/SineGrid0.lean), [`Triangular_Taylor_TaylorExp00`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorExp00.lean).
--
--   **Imports.** It imports the bundles `OAIQ250T003`, `OAIQ250T007`, `OAIQ250T010`, `OAIQ250T011`, `OAIQ250T012`, `OAIQ250T025` and `OAIQ250T026` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ250T086`, `OAIQ250T091` and `OAIQ250T098`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ250T003
import Definitions.Def_OAIQ250T007
import Definitions.Def_OAIQ250T010
import Definitions.Def_OAIQ250T011
import Definitions.Def_OAIQ250T012
import Definitions.Def_OAIQ250T025
import Definitions.Def_OAIQ250T026

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorExp00
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma taylorExp0_0_1_calc (j : Fin 31) : ((taylorPhase0_0 j).mul (CI.point 1)).exp = taylorExp0_0_1 j := by
  revert j
  decide +kernel
lemma taylorExp0_0_3_calc (j : Fin 31) : ((taylorPhase0_0 j).mul (CI.point 3)).exp = taylorExp0_0_3 j := by
  revert j
  decide +kernel
lemma taylorExp0_0_13_calc (j : Fin 31) : ((taylorPhase0_0 j).mul (CI.point 13)).exp = taylorExp0_0_13 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_ExceptionalSign3
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
lemma ex3b19_calc (r : Fin 8) : bernsteinRowsBox 22 ex3r 19 r = ex3b19 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_SignBase
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
-- module Solutions.OAIQ250_TR.Triangular_Signs_SineGrid0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors00 (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 0 k j) ∧ cellBarrier 0 < ∏ j : Fin 15,(cellFactor 0 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 0 k j) ∧ cellBarrier 0 < ∏ j : Fin 15,(cellFactor 0 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end


