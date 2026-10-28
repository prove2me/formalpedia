-- Prove2me | Definitions.Def_OAIW2HM002
-- name    : OAIW2HM002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-25T08:29:13.004129+00:00
-- url     : https://prove2.me/theorems/6afdbdd6-ca5e-4ff2-9f00-34fa5f0aaa07
-- title:
--   Definitions bundle OAIW2HM002 of the split of OpenAI, Spontaneous magnetization in the quantum Heisenberg ferromagnet
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Heisenberg.spontaneous_magnetization`, carved from OpenAI's openai/math development (OpenAI, *Spontaneous magnetization in the quantum Heisenberg ferromagnet*, OpenAI Math Release, September 24, 2026, result family 271, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 12 declarations of OpenAI's Lean: 8 definitions, 3 instances and 1 theorem. The definitions and types are `OAI.Heisenberg.gibbsDensity`, `OAI.Heisenberg.gibbsHalf`, `OAI.Heisenberg.gibbsState`, `OAI.Heisenberg.incidentEdges`, `OAI.Heisenberg.localCore`, `OAI.Heisenberg.neighborhood`, `OAI.Heisenberg.realFunctional`, `OAI.Heisenberg.sandwichState`.
--
--   **Sources.** They come from these modules of lean/OAI/MathematicalPhysics, in whole or in part: [`Heisenberg_ExponentialEvolution`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Heisenberg/ExponentialEvolution.lean), [`Heisenberg_LocalAlgebra`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Heisenberg/LocalAlgebra.lean), [`Heisenberg_LocalDynamics`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Heisenberg/LocalDynamics.lean), [`Heisenberg_SpinMatrixTrace`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Heisenberg/SpinMatrixTrace.lean), [`Heisenberg_StateCompactness`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Heisenberg/StateCompactness.lean), [`Heisenberg_ThermodynamicDynamics`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Heisenberg/ThermodynamicDynamics.lean).
--
--   **Imports.** It imports the published bundle `Def_Heisenberg`; the bundles `OAIW2HM000` and `OAIW2HM001` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.Heisenberg.Selection.field_ordered_cubes`, `OAI.Heisenberg.Selection.physical_field_mean`, `OAI.Heisenberg.cubeAverage_limit_KMS` and `OAI.Heisenberg.finite_cube_gibbs_strip`; the proofs of `OAI.Heisenberg.Selection.field_ordered_cubes`, `OAI.Heisenberg.Selection.physical_field_mean`, `OAI.Heisenberg.cubeAverage_limit_KMS`, `OAI.Heisenberg.cubeBoundary_error`, `OAI.Heisenberg.cubeBoundary_lower`, `OAI.Heisenberg.cubeBoundary_upper`, `OAI.Heisenberg.dynamics_converges`, `OAI.Heisenberg.field_local_small`, `OAI.Heisenberg.finiteDynamics_deep_uniform`, `OAI.Heisenberg.finite_cube_gibbs_strip`, `OAI.Heisenberg.spontaneous_magnetization` and `OAI.Heisenberg.state_limit_locallyUniform`.
-- source:
--   OpenAI, Spontaneous magnetization in the quantum Heisenberg ferromagnet, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 271; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Spontaneous-magnetization-in-the-quantum-Heisenberg-ferromagnet-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/MathematicalPhysics at commit adc7f12

import Mathlib
import Definitions.Def_Heisenberg
import Definitions.Def_OAIW2HM000
import Definitions.Def_OAIW2HM001

section
-- module Solutions.OAIW2_Heis.Heisenberg_LocalAlgebra
attribute [-instance] _root_.OAI.Heisenberg.quasiLocalClosed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate ENNReal Classical

open scoped ComplexConjugate BigOperators
namespace Heisenberg

instance quasiLocalStarMul (d ℓ : ℕ) : StarMul (QuasiLocal d ℓ) :=
  (quasiLocalAlgebra d ℓ).starRing.toStarMul

instance quasiLocalComplete (d ℓ : ℕ) : CompleteSpace (QuasiLocal d ℓ) :=
  (StarSubalgebra.isClosed_topologicalClosure _).completeSpace_coe

instance quasiLocalRationalAlgebra (d ℓ : ℕ) : NormedAlgebra ℚ (QuasiLocal d ℓ) :=
  NormedAlgebra.restrictScalars ℚ ℂ _

end Heisenberg
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_ExponentialEvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate ENNReal Classical
open scoped ComplexConjugate BigOperators

namespace Heisenberg

def incidentEdges {d : ℕ} (F : Finset (Site d)) : Finset (Site d × Site d) :=
  F.biUnion fun x => ((neighbors x).image (fun y => (x,y))) ∪
    ((neighbors x).image (fun y => (y,x)))

def neighborhood {d : ℕ} (F : Finset (Site d)) : Finset (Site d) :=
  F ∪ F.biUnion neighbors

end Heisenberg
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_LocalDynamics
attribute [-instance] _root_.OAI.Heisenberg.quasiLocalClosed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate ENNReal Classical
open scoped ComplexConjugate BigOperators

namespace Heisenberg

def localCore (d ℓ : ℕ) : StarSubalgebra ℂ (QuasiLocal d ℓ) :=
  StarAlgebra.adjoin ℂ {A | ∃ x a b, A = localUnit d ℓ x a b}

end Heisenberg

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_ThermodynamicDynamics
attribute [-instance] _root_.OAI.Heisenberg.quasiLocalClosed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate ENNReal Classical
open scoped ComplexConjugate BigOperators

namespace Heisenberg

local instance instIsTopologicalRingContinuousLinearMapComplexIdSubtypeSpinOperatorMemStarSubalgebraQuasiLocal (d ℓ : ℕ) : IsTopologicalRing (QuasiLocal d ℓ →L[ℂ] QuasiLocal d ℓ) :=
  clm_topologicalRing

end Heisenberg

open Filter Topology Metric
open scoped NNReal

open scoped NNReal
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_StateCompactness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate ENNReal Classical
open scoped ComplexConjugate BigOperators
open Filter Topology Metric
open scoped NNReal
open scoped NNReal

namespace Heisenberg

open scoped ComplexOrder

open scoped InnerProductSpace

def sandwichState {d ℓ : ℕ} (ω : State d ℓ) (B : QuasiLocal d ℓ) (hB : IsUnit B) :
    State d ℓ := by
  let : PartialOrder (QuasiLocal d ℓ) := CStarAlgebra.spectralOrder _
  let : StarOrderedRing (QuasiLocal d ℓ) := CStarAlgebra.spectralOrderedRing _
  have hp : ∀ C, 0 ≤ ω.functional (star C * C) :=
    fun C => ⟨(ω.positive C).2, by simpa using (ω.positive C).1.symm⟩
  have hZ := sandwich_one_pos ω.functional ω.normalized hp hB
  let Z := (sandwichFunctional ω.functional B 1).re
  refine ⟨((Z : ℂ)⁻¹) • sandwichFunctional ω.functional B, ?_, ?_⟩
  · change (Z : ℂ)⁻¹ * sandwichFunctional ω.functional B 1 = 1
    have hz : sandwichFunctional ω.functional B 1 = (Z : ℂ) := by
      apply Complex.ext
      · rfl
      · simpa only [sandwichFunctional_apply, mul_one, Complex.ofReal_im] using (ω.positive B).1
    rw [hz]
    exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (ne_of_gt hZ))
  · intro A
    change (((Z : ℂ)⁻¹) * sandwichFunctional ω.functional B (star A*A)).im = 0 ∧ _
    have hA := sandwichFunctional_positive ω.functional hp B A
    have hi : 0 ≤ ((Z : ℂ)⁻¹) := by
      rw [← Complex.ofReal_inv]
      exact ⟨le_of_lt (inv_pos.mpr hZ), by simp⟩
    have hh := mul_nonneg hi hA
    exact ⟨hh.2.symm, hh.1⟩

def gibbsDensity {d ℓ : ℕ} (K : QuasiLocal d ℓ) (β : ℝ) : QuasiLocal d ℓ :=
  NormedSpace.exp (((-β : ℝ) : ℂ) • K)

def gibbsHalf {d ℓ : ℕ} (K : QuasiLocal d ℓ) (β : ℝ) : QuasiLocal d ℓ :=
  NormedSpace.exp (((-β/2 : ℝ) : ℂ) • K)

def gibbsState {d ℓ : ℕ} (τ : State d ℓ) (K : QuasiLocal d ℓ) (β : ℝ) : State d ℓ :=
  sandwichState τ (gibbsHalf K β) (NormedSpace.isUnit_exp _)

end Heisenberg
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_SpinMatrixTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical BigOperators Matrix Matrix.Norms.Operator
namespace Heisenberg
open TensorUnits
variable {d ℓ : ℕ} {X : Type} [Fintype X] [DecidableEq X]

def realFunctional (τ : State d ℓ) : QuasiLocal d ℓ →ₗ[ℝ] ℝ :=
  (Complex.reCLM.comp (τ.functional.restrictScalars ℝ)).toLinearMap

end Heisenberg
end
end

end OAI
end


