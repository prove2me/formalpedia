-- Prove2me | Definitions.Def_OAIQ262T112
-- name    : OAIQ262T112
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T16:56:31.810376+00:00
-- url     : https://prove2.me/theorems/deb5de1d-19e9-4410-9d14-fa0db8961af0
-- title:
--   Definitions bundle OAIQ262T112 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 13 declarations of OpenAI's Lean: 13 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Schwartz_GaussianPair`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Schwartz/GaussianPair.lean), [`Triangular_Signs_ExceptionalSign2`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/ExceptionalSign2.lean), [`Triangular_Signs_ExceptionalSign3`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/ExceptionalSign3.lean), [`Triangular_Signs_SineGrid0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/SineGrid0.lean), [`Triangular_Taylor_TaylorExp01`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorExp01.lean), [`Triangular_Taylor_TaylorExp10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorExp10.lean).
--
--   **Imports.** It imports the published bundle `Def_TriangularGaussian`; the bundles `OAIQ262T005`, `OAIQ262T013`, `OAIQ262T015`, `OAIQ262T020`, `OAIQ262T043`, `OAIQ262T044` and `OAIQ262T045` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ262T146` and `OAIQ262T150`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_TriangularGaussian
import Definitions.Def_OAIQ262T005
import Definitions.Def_OAIQ262T013
import Definitions.Def_OAIQ262T015
import Definitions.Def_OAIQ262T020
import Definitions.Def_OAIQ262T043
import Definitions.Def_OAIQ262T044
import Definitions.Def_OAIQ262T045

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
lemma taylorExp0_1_9_calc (j : Fin 31) : ((taylorPhase0_1 j).mul (CI.point 9)).exp = taylorExp0_1_9 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

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
lemma taylorExp1_0_12_calc (j : Fin 31) : ((taylorPhase1_0 j).mul (CI.point 12)).exp = taylorExp1_0_12 j := by
  revert j
  decide +kernel
lemma taylorExp1_0_13_calc (j : Fin 31) : ((taylorPhase1_0 j).mul (CI.point 13)).exp = taylorExp1_0_13 j := by
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
lemma ex2b5_calc (r : Fin 8) : bernsteinRowsBox 22 ex2r 5 r = ex2b5 r := by
  revert r
  decide +kernel
lemma ex2b6_calc (r : Fin 8) : bernsteinRowsBox 22 ex2r 6 r = ex2b6 r := by
  revert r
  decide +kernel
lemma ex2b7_calc (r : Fin 8) : bernsteinRowsBox 22 ex2r 7 r = ex2b7 r := by
  revert r
  decide +kernel
lemma ex2b8_calc (r : Fin 8) : bernsteinRowsBox 22 ex2r 8 r = ex2b8 r := by
  revert r
  decide +kernel
lemma ex2b9_calc (r : Fin 8) : bernsteinRowsBox 22 ex2r 9 r = ex2b9 r := by
  revert r
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
lemma ex3b0_calc (r : Fin 8) : bernsteinRowsBox 22 ex3r 0 r = ex3b0 r := by
  revert r
  decide +kernel
lemma ex3b10_calc (r : Fin 8) : bernsteinRowsBox 22 ex3r 10 r = ex3b10 r := by
  revert r
  decide +kernel
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
lemma cellGeometry00 (k : Fin 100) :
    0 ≤ cellMagnitude 0 k ∧ cellMagnitude 0 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 0 → 0 ≤ cellSeparation 0 k j ∧ cellSeparation 0 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0 ≤ cellMagnitude 0 k ∧ cellMagnitude 0 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 0 → 0 ≤ cellSeparation 0 k j ∧ cellSeparation 0 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Schwartz_GaussianPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped FourierTransform SchwartzMap
open Complex MeasureTheory
namespace AtomicTriangular
open Construction

lemma gaussianSchwartz_apply (α : ℝ) (hα : 0<α) (x : Plane) :
    gaussianSchwartz α hα x=gaussian α x := by
  simp only [gaussianSchwartz,Analysis.gaussianSchwartz_apply,gaussian,neg_mul]
lemma gaussianSchwartz_coe (α : ℝ) (hα : 0<α) :
    (gaussianSchwartz α hα : Plane → ℝ)=gaussian α := funext (gaussianSchwartz_apply α hα)
end AtomicTriangular
end

end OAI
end


