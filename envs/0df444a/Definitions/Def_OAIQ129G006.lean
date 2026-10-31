-- Prove2me | Definitions.Def_OAIQ129G006
-- name    : OAIQ129G006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T20:15:31.401174+00:00
-- url     : https://prove2.me/theorems/632e6717-2c4e-4d0a-846a-9d9a604f97cc
-- title:
--   Definitions bundle OAIQ129G006 of the split of OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.RelativeGeneration.main_theorem` and `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 5 declarations of OpenAI's Lean: 2 definitions, 2 instances and 1 theorem. The definitions and types are `OAI.Generator.predualFunctionalIsometry`, `OAI.Generator.predualFunctionals`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`FactorGeneration_PredualOrder`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/PredualOrder.lean), [`FactorGeneration_PredualRange`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/PredualRange.lean).
--
--   **Imports.** It imports the bundle `OAIQ129G001` of this split.
--
--   **Imported by** (directly, in this split): the proof of `OAI.Generator.Tracial.traceOrbit_isSeparable_of_separablePredual_q129`.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ129G001

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_PredualOrder
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.sequencesIsTopologicalRing _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! Operator norm geometry for the original existential Banach-predual gap.
These statements use only concrete Hilbert operators. They do not identify
any predual or prove trace-orbit separability. -/

/-! Bounded self-adjoint sets are weak-star compact for the actual Banach
predual isometry. No predual uniqueness or WOT compatibility is assumed. -/

/-! Positive operator balls are compact in the weak-star topology of the
given Banach predual. The isometry is not assumed weak-operator continuous. -/

/-! Closed and compact order intervals for the given Banach predual.
All inequalities are the concrete operator Loewner order. -/

/-! Monotone order limits in the algebra converge for the actual given
Banach predual. Greatest/least bounds are tested only against members of S,
not against all ambient operators. -/

/-! The actual given predual embeds isometrically into the norm dual of S.
Conjugation accounts for the conjugate-linear predual isometry. These
functionals preserve monotone order limits. No canonical-predual membership
or weak-operator continuity is assumed. -/
section
open Filter
open scoped Topology ComplexConjugate
variable {H X I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (S : StarSubalgebra ℂ (H →L[ℂ] H))
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] S)

theorem predualFunctional_norm (x : X) : ‖predualFunctional S e x‖ = ‖x‖ := by
  apply le_antisymm
  · apply (predualFunctional S e x).opNorm_le_bound (norm_nonneg x)
    intro a
    rw [predualFunctional_apply, Complex.norm_conj]
    exact ((e.symm a).le_opNorm x).trans_eq (by rw [e.symm.norm_map, mul_comm])
  · obtain ⟨g, hg, hx⟩ := exists_dual_vector'' ℂ x
    calc
      ‖x‖ = ‖predualFunctional S e x (e g)‖ := by simp [hx]
      _ ≤ ‖predualFunctional S e x‖ * ‖e g‖ := (predualFunctional S e x).le_opNorm _
      _ ≤ ‖predualFunctional S e x‖ := by
        simpa only [e.norm_map, mul_one] using
          mul_le_mul_of_nonneg_left hg (norm_nonneg (predualFunctional S e x))

/-- A conjugate-linear isometric embedding of the actual given predual. -/
def predualFunctionalIsometry : X →ₗᵢ⋆[ℂ] StrongDual ℂ S where
  toFun := predualFunctional S e
  map_add' x y := by ext a; simp
  map_smul' c x := by ext a; simp
  norm_map' := predualFunctional_norm S e

end

/-! An arbitrary net squeezed into shrinking operator order intervals
converges in the topology of the given Banach predual. The net itself need
not be monotone. No normal-functional decomposition is used. -/
open Filter
open scoped Topology

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_PredualRange
attribute [-instance] _root_.OAI.Generator.Tracial.sequencesIsTopologicalRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! An actual separable Banach predual for the constructed matrix-generated
factor. The existential convention is exactly Generator.HasSeparablePredual. -/

/-! Separability of the actual cyclic predual implies separability of the
trace-vector orbit. This does not identify an arbitrary given Banach predual
with the cyclic predual. -/

/-! The given predual as a closed separating subspace of the algebra norm dual, with its evaluation duality. -/
section
open scoped ComplexConjugate
variable {H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (S : StarSubalgebra ℂ (H →L[ℂ] H))
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] S)

def predualFunctionals : Submodule ℂ (StrongDual ℂ S) :=
  (predualFunctionalIsometry S e).toLinearMap.range

instance predualFunctionals_normed : NormedAddCommGroup (predualFunctionals S e) := inferInstance

instance predualFunctionals_normedSpace : NormedSpace ℂ (predualFunctionals S e) := inferInstance

end

/-! Hahn–Banach comparison of preduals from normal-functional membership and evaluation surjectivity. -/

/-! Conditional comparison with the constructed cyclic predual. Membership
of the given-predual evaluations in that space is an explicit unproved input;
it is not obtained merely from their order-limit convergence. -/

end Generator

end

end OAI
end


