-- Prove2me | Definitions.Def_OAIQ11Fg013
-- name    : OAIQ11Fg013
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T10:01:30.873646+00:00
-- url     : https://prove2.me/theorems/1777d8f0-3c41-469a-a86d-a566603a3fb5
-- title:
--   Definitions bundle OAIQ11Fg013 of the split of OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 6 declarations of OpenAI's Lean: 3 definitions and 3 theorems. The definitions and types are `OAI.Generator.Tracial.quotientL2AddCommGroup`, `OAI.Generator.Tracial.quotientL2AddCommMonoid`, `OAI.Generator.Tracial.quotientOperatorSemiring`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`FactorGeneration_QuotientRepresentation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/QuotientRepresentation.lean).
--
--   **Imports.** It imports the bundle `OAIQ11Fg011` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ11Fg020` and `OAIQ11Fg024`; the statements `OAI_Generator_Tracial_boundedPartialResidual_mem`, `OAI_Generator_Tracial_boundedPartialResidual_projection`, `OAI_Generator_Tracial_conjugateEnd_mem`, `OAI_Generator_Tracial_conjugateGaps_reduced`, `OAI_Generator_Tracial_conjugateWord_formula`, `OAI_Generator_Tracial_coordinateGroupRing_gram_limits`, `OAI_Generator_Tracial_coordinateGroupRing_quotient_single`, `OAI_Generator_Tracial_coordinateGroupRing_single`, `OAI_Generator_Tracial_exists_irreducible_corner_local_piece`, `OAI_Generator_Tracial_quotient_orthogonal_patch_supported`, `OAI_Generator_Tracial_quotient_patch_residual_bound` and `OAI_Generator_Tracial_quotient_unitary_of_zero_residual`; the proofs of `OAI_Generator_Tracial_boundedPartialResidual_projection`, `OAI_Generator_Tracial_conjugateEnd_mem`, `OAI_Generator_Tracial_conjugateGaps_reduced`, `OAI_Generator_Tracial_conjugateWord_formula`, `OAI_Generator_Tracial_conjugate_reduced_word_zero`, `OAI_Generator_Tracial_coordinateGroupRing_gram_limits`, `OAI_Generator_Tracial_coordinateGroupRing_quotient_single`, `OAI_Generator_Tracial_coordinateGroupRing_single`, `OAI_Generator_Tracial_quotient_patch_residual_bound` and `OAI_Generator_Tracial_quotient_unitary_of_zero_residual`.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ11Fg011

section
-- module Solutions.OAIQ11_FG.FactorGeneration_QuotientRepresentation
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Complete operator-norm bounded sequences and their contractive map to the
actual quotient trace Hilbert space. This map is not asserted injective. -/
open Filter
open scoped Topology

/-! The faithful constant embedding into the tracial quotient, with its trace and trace norm, for every ultrafilter. -/
open Filter
open scoped Topology
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

@[simp] theorem constantQuotient_trace (a : M.toStarSubalgebra) :
    quotientTrace τ ω (constantQuotient τ ω a) = τ.trace a := by
  exact tendsto_nhds_unique (traceRep_tendsto τ ω (boundedMap (constantSequence a)))
    tendsto_const_nhds

@[simp] theorem constantQuotient_norm (a : M.toStarSubalgebra) :
    ‖constantQuotient τ ω a‖ = τ.norm₂ a := by
  exact tendsto_nhds_unique (sequence_norm_tendsto τ ω (constantSequence a)) tendsto_const_nhds

@[simp] theorem constantQuotient_inner (a b : M.toStarSubalgebra) :
    inner ℂ (inclusion τ ω (constantQuotient τ ω a))
      (inclusion τ ω (constantQuotient τ ω b)) = τ.trace (star a*b) := by
  rw [inclusion_inner, ← map_star, ← map_mul, constantQuotient_trace]

end

/-! Left multiplication by bounded representatives on the completed trace
Hilbert space. The quotient ideal, not an assumed operator action, determines
which representatives induce the same operator. -/
open Filter
open scoped Topology

/-! Faithful concrete Hilbert-space representation of the tracial quotient
star algebra. Weak operator closedness of its image is not claimed here. -/
open Filter
open scoped Topology

/-! The standard completion/continuous-linear-map structures are not new hypotheses. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

@[instance_reducible] def quotientL2AddCommMonoid : AddCommMonoid (L2 τ ω) :=
  (inferInstance : NormedAddCommGroup (L2 τ ω)).toAddCommGroup.toAddCommMonoid

@[instance_reducible] def quotientL2AddCommGroup : AddCommGroup (L2 τ ω) :=
  (inferInstance : NormedAddCommGroup (L2 τ ω)).toAddCommGroup

attribute [local instance] quotientL2AddCommMonoid quotientL2AddCommGroup

@[instance_reducible] def quotientOperatorSemiring : Semiring (L2 τ ω →L[ℂ] L2 τ ω) :=
  (inferInstance : NormedRing (L2 τ ω →L[ℂ] L2 τ ω)).toRing.toSemiring

attribute [local instance] quotientOperatorSemiring

end

/-! Fixed-index selection for bounded coordinate representatives. -/
open Filter
open scoped Topology
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end


