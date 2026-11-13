-- Prove2me | Definitions.Def_OAIQ334E027
-- name    : OAIQ334E027
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-12T12:55:56.302706+00:00
-- url     : https://prove2.me/theorems/ac96d25b-a9f4-4161-92c7-9a7595c0c2d2
-- title:
--   Definitions bundle OAIQ334E027 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.universal_energy_minimum`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2 declarations of OpenAI's Lean: 1 definition and 1 theorem. The definitions and types are `OAI.AtomicTriangular.Construction.dualAtomFunction`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Energy_LatticePoisson`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Energy/LatticePoisson.lean), [`Triangular_Schwartz_GaussianPair`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Schwartz/GaussianPair.lean).
--
--   **Imports.** It imports the published bundle `Def_TriangularEnergy`; the bundle `OAIQ334E007` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ334E032`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_TriangularEnergy
import Definitions.Def_OAIQ334E007

section
-- module Solutions.OAIQ334_EU.Triangular_Energy_LatticePoisson
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators FourierTransform SchwartzMap
open Complex
namespace AtomicTriangular.Construction
def dualAtomFunction (q : Fin 2) (x : Plane) : C(Spectrum,ℂ) :=
  exp (-(Real.pi:ℂ)*h*(radial x:ℂ)) • transformedFunction (damping q) h (damping_pos q) (radial x:ℂ)
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Schwartz_GaussianPair
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

lemma realFourier_smul (c : ℝ) (f : Plane → ℝ) (w : Plane) :
    realFourier (c • f) w=(c:ℂ)*realFourier f w := by
  unfold realFourier
  simp only [Pi.smul_apply,smul_eq_mul,ofReal_mul]
  change 𝓕 ((c:ℂ) • (fun x => (f x:ℂ))) w=_
  rw [complex_fourier_smul]
  rfl
end AtomicTriangular
end

end OAI
end


