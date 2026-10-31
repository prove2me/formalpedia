-- Prove2me | Definitions.Def_OAIQ129G014
-- name    : OAIQ129G014
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T21:02:17.721998+00:00
-- url     : https://prove2.me/theorems/b71a97db-1bcb-446f-b449-838d186e93e1
-- title:
--   Definitions bundle OAIQ129G014 of the split of OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.RelativeGeneration.main_theorem` and `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 117 declarations of OpenAI's Lean: 39 definitions, 7 instances and 71 theorems. The definitions and types are `OAI.Generator.Tracial.SuccessiveCoordinateHaar.conjugateUnitary`, `OAI.Generator.Tracial.SuccessiveCoordinateHaar.coordinateConjugates`, `OAI.Generator.Tracial.SuccessiveCoordinateHaar.coordinateLabels`, `OAI.Generator.Tracial.SuccessiveCoordinateHaar.firstOrderTerm`, `OAI.Generator.Tracial.SuccessiveCoordinateHaar.labelUnitary`, `OAI.Generator.Tracial.SuccessiveCoordinateHaar.perturbationMap`, `OAI.Generator.Tracial.SuccessiveCoordinateHaar.perturbedUnitary`, `OAI.Generator.Tracial.SuccessiveCoordinateHaar.perturbedWord`, `OAI.Generator.Tracial.SuccessiveCoordinateHaar.perturbingUnitary`, `OAI.Generator.Tracial.SuccessiveCoordinateHaar.retainedUnitary`, `OAI.Generator.Tracial.SuccessiveCoordinateHaar.targetUnitary`, `OAI.Generator.Tracial.boundedCornerCenter`, `OAI.Generator.Tracial.boundedCornerScalar`, `OAI.Generator.Tracial.conditionalExpectationCLM`, `OAI.Generator.Tracial.conjugateEnd`, `OAI.Generator.Tracial.conjugateGaps`, `OAI.Generator.Tracial.conjugateVariables`, `OAI.Generator.Tracial.constantQuotientUnitary`, `OAI.Generator.Tracial.coordinateGroupRing`, `OAI.Generator.Tracial.cornerCentered`, `OAI.Generator.Tracial.cyclicFamilyValue`, `OAI.Generator.Tracial.cyclicResidualFamily`, `OAI.Generator.Tracial.prefixProduct`, `OAI.Generator.Tracial.prefixVariable`, `OAI.Generator.Tracial.quotientCornerCenter`, `OAI.Generator.Tracial.quotientResidualTrace`, `OAI.Generator.Tracial.relativeDistance`, `OAI.Generator.Tracial.relativeTraceSpace`, `OAI.Generator.Tracial.remainderSequence`, `OAI.Generator.Tracial.residualWordFamily`, `OAI.Generator.Tracial.residualWordValue`, `OAI.Generator.Tracial.sequenceEval`, `OAI.Generator.Tracial.sequenceUnitaryQuotient`, `OAI.Generator.Tracial.subalgebraResidual`, `OAI.Generator.Tracial.traceClosedSpan`, `OAI.Generator.Tracial.traceVectorCLM`, `OAI.Generator.Tracial.unitaryCoordinate`, `OAI.Generator.Tracial.unitaryRepresentation`, `OAI.Generator.Tracial.unitaryWord`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `FactorGeneration_CoordinatePerturbation`, `FactorGeneration_CornerTrace`, `FactorGeneration_Expectations`, `FactorGeneration_FreeGroupMoments`, `FactorGeneration_HaarSequences`, `FactorGeneration_LaurentMoments`, `FactorGeneration_NormalTrace`, `FactorGeneration_PerturbationBounds`, `FactorGeneration_QuotientCorners`, `FactorGeneration_QuotientRepresentation`, `FactorGeneration_RelativeGeneration`, `FactorGeneration_ResidualCompletion`, `FactorGeneration_ResidualMoments`, `FactorGeneration_Ultrapower`, `FactorGeneration_WordCorrelation`, `RelativeGeneration_LocusTopology`.
--
--   **Imports.** It imports the bundles `OAIQ129G010`, `OAIQ129G011` and `OAIQ129G012` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ129G015`; the statements `OAI.Generator.Tracial.SuccessiveCoordinateHaar.commonPerturbation_norm_q129`, `OAI.Generator.Tracial.SuccessiveCoordinateHaar.conjugate_trace_q129`, `OAI.Generator.Tracial.SuccessiveCoordinateHaar.exponential_product_correlation_q129`, `OAI.Generator.Tracial.SuccessiveCoordinateHaar.linearized_correlation_q129`, `OAI.Generator.Tracial.SuccessiveCoordinateHaar.perturbedWord_correlation_q129`, `OAI.Generator.Tracial.exists_exact_residual_iteration_q129` and `OAI.Generator.Tracial.tracial_remainder_of_coordinate_moments_q129`; the proofs of `OAI.Generator.FiniteMatrixStage.exists_finite_matrix_energy_budget_q129`, `OAI.Generator.FiniteMatrixStage.exists_irreducible_matrix_generated_II1_q129`, `OAI.Generator.FiniteMatrixStage.exists_tensor_iterated_energy_descent_q129`, `OAI.Generator.Tracial.SuccessiveCoordinateHaar.commonPerturbation_norm_q129`, `OAI.Generator.Tracial.SuccessiveCoordinateHaar.conjugate_trace_q129`, `OAI.Generator.Tracial.SuccessiveCoordinateHaar.exponential_product_correlation_q129`, `OAI.Generator.Tracial.SuccessiveCoordinateHaar.linearized_correlation_q129`, `OAI.Generator.Tracial.SuccessiveCoordinateHaar.perturbedWord_correlation_q129`, `OAI.Generator.Tracial.exists_coordinate_ordered_unitary_q129`, `OAI.Generator.Tracial.exists_exact_residual_iteration_q129`, `OAI_Generator_Tracial_exists_residual_quotient_increment_q129`, `OAI.Generator.Tracial.exists_unitResidual_local_compression_q129`, `OAI.Generator.Tracial.represented_four_selfAdjoint_generators_q129`, `OAI.Generator.Tracial.represented_relative_generation_q129` and `OAI.Generator.Tracial.tracial_remainder_of_coordinate_moments_q129`.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ129G010
import Definitions.Def_OAIQ129G011
import Definitions.Def_OAIQ129G012

section
-- module Solutions.OAIQ129_RG2.Compat
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
section OAIVecTail
variable {α : Type _}
@[simp] theorem vecConsTail2_1 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_2 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_1 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail3_2 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_3 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_1 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail4_2 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail4_3 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_4 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 4 = f 3 := rfl
end OAIVecTail
@[simp] theorem fin3_mk_0 (h : 0 < 3) : (⟨0, h⟩ : Fin 3) = 0 := rfl
@[simp] theorem fin3_mk_1 (h : 1 < 3) : (⟨1, h⟩ : Fin 3) = 1 := rfl
@[simp] theorem fin3_mk_2 (h : 2 < 3) : (⟨2, h⟩ : Fin 3) = 2 := rfl
@[simp] theorem fin4_mk_0 (h : 0 < 4) : (⟨0, h⟩ : Fin 4) = 0 := rfl
@[simp] theorem fin4_mk_1 (h : 1 < 4) : (⟨1, h⟩ : Fin 4) = 1 := rfl
@[simp] theorem fin4_mk_2 (h : 2 < 4) : (⟨2, h⟩ : Fin 4) = 2 := rfl
@[simp] theorem fin4_mk_3 (h : 3 < 4) : (⟨3, h⟩ : Fin 4) = 3 := rfl
@[simp] theorem fin5_mk_0 (h : 0 < 5) : (⟨0, h⟩ : Fin 5) = 0 := rfl
@[simp] theorem fin5_mk_1 (h : 1 < 5) : (⟨1, h⟩ : Fin 5) = 1 := rfl
@[simp] theorem fin5_mk_2 (h : 2 < 5) : (⟨2, h⟩ : Fin 5) = 2 := rfl
@[simp] theorem fin5_mk_3 (h : 3 < 5) : (⟨3, h⟩ : Fin 5) = 3 := rfl
@[simp] theorem fin5_mk_4 (h : 4 < 5) : (⟨4, h⟩ : Fin 5) = 4 := rfl
/-- `norm_num` cannot decide equalities of `Fin` literals here (oaiq-091). -/
@[simp] theorem fin3_lit_0_1 : ((0 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin3_lit_0_2 : ((0 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_1_0 : ((1 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_1_2 : ((1 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_2_0 : ((2 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_2_1 : ((2 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_0_1 : ((0 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_0_2 : ((0 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_0_3 : ((0 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_1_0 : ((1 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_1_2 : ((1 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_1_3 : ((1 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_2_0 : ((2 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_2_1 : ((2 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_2_3 : ((2 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_3_0 : ((3 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_3_1 : ((3 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_3_2 : ((3 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_0_1 : ((0 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_0_2 : ((0 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_0_3 : ((0 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_0_4 : ((0 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_1_0 : ((1 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_1_2 : ((1 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_1_3 : ((1 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_1_4 : ((1 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_2_0 : ((2 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_2_1 : ((2 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_2_3 : ((2 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_2_4 : ((2 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_3_0 : ((3 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_3_1 : ((3 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_3_2 : ((3 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_3_4 : ((3 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_4_0 : ((4 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_4_1 : ((4 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_4_2 : ((4 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_4_3 : ((4 : Fin 5) = 3) ↔ False := by decide
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_Ultrapower
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.quotientInnerProductSpace _root_.OAI.Generator.Tracial.quotientNormedAddCommGroup _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace UltrapowerBridge

section
open Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (l : Filter ℕ)

instance (priority := high) q129UMonoid : Monoid (unitary (TracialQuotient τ l)) := inferInstance
instance (priority := high) q129UMulOneClass : MulOneClass (unitary (TracialQuotient τ l)) := inferInstance
instance (priority := high) q129UMul : Mul (unitary (TracialQuotient τ l)) := inferInstance
instance (priority := high) q129UOne : One (unitary (TracialQuotient τ l)) := inferInstance
instance (priority := high) q129UInv : Inv (unitary (TracialQuotient τ l)) := inferInstance
instance (priority := high) q129UStar : Star (unitary (TracialQuotient τ l)) := inferInstance

end

open Filter
open scoped Topology

end UltrapowerBridge

/-! Commutation with every bounded subalgebra sequence implies uniform coordinate commutator decay. -/
open Filter
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_CornerTrace
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.Tracial.quotientInnerProductSpace _root_.OAI.Generator.Tracial.quotientNormedAddCommGroup _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Trace estimates in the actual ambient algebra. The corner scalar uses
its normalized trace. These estimates do not assume or assert the existence
of a local-quantizing projection. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

def cornerCentered (p : AlgebraProjection M) (x : M.toStarSubalgebra) : M.toStarSubalgebra :=
  p.val*x*p.val - cornerScalar τ p x • p.val

end

/-! Actual noncommutative L1 on the coordinate algebra: trace(sqrt(x* x)).
The supported L2-to-L1 estimate retains the square root of the support trace.
No quantizing projection or conditional expectation theorem is assumed. -/

/-! A finite compression-energy estimate yields a nonzero corner projection with simultaneous L1 control. -/

/-! The scalar trace estimate for a term with two supported patch letters.
It reduces to the actual compressed middle coefficient and keeps trace(q),
not trace(p), as the scale of the error. -/
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_Expectations
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.quotientInnerProductSpace _root_.OAI.Generator.Tracial.quotientNormedAddCommGroup _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! The orthogonal subalgebra representative of a self-adjoint ambient
operator is constructed, with its operator norm bound. -/

/-! A bounded trace-preserving subalgebra projection from self-adjoint least-distance points. Tracial orthogonality gives uniqueness and the bimodule identities. -/
section
open scoped ComplexStarModule
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem subalgebra_representative_unique (x y z : M.toStarSubalgebra)
    (hy : y.val ∈ N) (hz : z.val ∈ N)
    (hxy : TraceOrthogonal τ (insideAlgebra (M := M) (P := N)) (x-y))
    (hxz : TraceOrthogonal τ (insideAlgebra (M := M) (P := N)) (x-z)) : y=z := by
  have h := hxz.sub τ hxy
  have he : (x-z)-(x-y)=y-z := by abel
  rw [he] at h
  exact sub_eq_zero.mp (h.eq_zero τ (N.sub_mem hy hz))

theorem conditionalExpectation_mem (hNM : N ≤ M) (x : M.toStarSubalgebra) :
    (conditionalExpectation τ hNM x).val ∈ N :=
  (exists_bounded_subalgebra_representative τ hNM x).choose_spec.1
theorem conditionalExpectation_bound (hNM : N ≤ M) (x : M.toStarSubalgebra) :
    ‖conditionalExpectation τ hNM x‖ ≤ 2*‖x‖ :=
  (exists_bounded_subalgebra_representative τ hNM x).choose_spec.2.1
theorem conditionalExpectation_orthogonal (hNM : N ≤ M) (x : M.toStarSubalgebra) :
    TraceOrthogonal τ (insideAlgebra (M := M) (P := N)) (x-conditionalExpectation τ hNM x) :=
  (exists_bounded_subalgebra_representative τ hNM x).choose_spec.2.2

theorem conditionalExpectation_eq_of_orthogonal (hNM : N ≤ M)
    (x y : M.toStarSubalgebra) (hy : y.val ∈ N)
    (h : TraceOrthogonal τ (insideAlgebra (M := M) (P := N)) (x-y)) :
    conditionalExpectation τ hNM x=y :=
  subalgebra_representative_unique τ x _ y (conditionalExpectation_mem τ hNM x) hy
    (conditionalExpectation_orthogonal τ hNM x) h

theorem conditionalExpectation_add (hNM : N ≤ M) (x y : M.toStarSubalgebra) :
    conditionalExpectation τ hNM (x+y)=conditionalExpectation τ hNM x+conditionalExpectation τ hNM y := by
  apply conditionalExpectation_eq_of_orthogonal τ hNM
  · exact N.add_mem (conditionalExpectation_mem τ hNM x) (conditionalExpectation_mem τ hNM y)
  · have h := (conditionalExpectation_orthogonal τ hNM x).add τ
      (conditionalExpectation_orthogonal τ hNM y)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    abel

theorem conditionalExpectation_smul (hNM : N ≤ M) (z : ℂ) (x : M.toStarSubalgebra) :
    conditionalExpectation τ hNM (z • x)=z • conditionalExpectation τ hNM x := by
  apply conditionalExpectation_eq_of_orthogonal τ hNM
  · exact N.smul_mem (conditionalExpectation_mem τ hNM x) z
  · simpa only [smul_sub] using (conditionalExpectation_orthogonal τ hNM x).smul τ z

def conditionalExpectationCLM (hNM : N ≤ M) : M.toStarSubalgebra →L[ℂ] M.toStarSubalgebra :=
  LinearMap.mkContinuous
    { toFun := conditionalExpectation τ hNM
      map_add' := conditionalExpectation_add τ hNM
      map_smul' := conditionalExpectation_smul τ hNM }
    2 (conditionalExpectation_bound τ hNM)

end

/-! The constructed expectation preserves adjoints, is a bimodule map,
and is the orthogonal projection for the trace norm. -/

/-! Positivity of the constructed expectation. The negative spectral part
is an actual subalgebra test operator; tracial orthogonality eliminates it. -/

/-! The constructed expectation satisfies the Schwarz inequality and is
contractive in operator norm. -/

/-! Actual nested subalgebras satisfy the expectation tower identity.
The resulting energy identity is the decreasing-subfactor step of A.1.2. -/

/-! Conditional expectations onto a decreasing sequence of actual
subalgebras converge in L2. This supplies the limiting argument in A.1.2;
it does not construct that source's decreasing subfactors. -/
open Filter
open scoped Topology BigOperators
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_ResidualMoments
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Valid residual-corner identities in the actual quotient. Compression
centering requires two exact moments; global centering alone is insufficient. -/

/-! A countable family containing every original coefficient and every old
nonempty ordered signed word, with both optional endpoints retained. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

def residualWordValue (v : Q τ ω) (x : ℕ → Q τ ω) : ResidualWordIndex → Q τ ω
  | .inl i => x i
  | .inr (first,last,xs,s) => optionalCoefficient x first *
      algebraPatchingWord v (xs.map (fun a => (a.1,x a.2)) ++ [(s,optionalCoefficient x last)])

def residualWordFamily (v : Q τ ω) (x : ℕ → Q τ ω) (i : ℕ) : Q τ ω :=
  match Encodable.decode (α := ResidualWordIndex) i with
  | none => 0
  | some k => residualWordValue τ ω v x k

/-! Ordered mixed words grouped at each increment letter. The intervening
old runs are actual members of the previously enumerated residual family. -/

end

/-! Cyclic endpoint correction for residual patching. Outer endpoints are
multiplied before compression, and the scalar part is handled separately. -/

/-! Countable supported family for actual residual patching, including centered
cyclic products of the two outer blocks. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

def quotientCornerCenter (f z : Q τ ω) : Q τ ω :=
  f*z*f-(quotientTrace τ ω (f*z*f)/quotientTrace τ ω f) • f

def cyclicFamilyValue (f : Q τ ω) (y : ℕ → Q τ ω) : CyclicFamilyIndex → Q τ ω
  | .inl i => f*y i*f
  | .inr (a,b) => quotientCornerCenter τ ω f (optionalCoefficient y b*optionalCoefficient y a)

def cyclicResidualFamily (f : Q τ ω) (y : ℕ → Q τ ω) (i : ℕ) : Q τ ω :=
  match Encodable.decode (α := CyclicFamilyIndex) i with
  | none => 0
  | some k => cyclicFamilyValue τ ω f y k

end

/-! Exact preservation of every original ordered moment under orthogonal
patching, once the constructed cyclic residual family has exact moments. -/
open UltrapowerBridge Filter

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_QuotientCorners
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Exact coordinate centering in projection corners whose traces have a
uniform positive lower bound. The corner scalar is divided by its actual
trace; no global-centering-to-corner-centering implication is assumed. -/
open Filter
open scoped Topology
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem corner_trace_norm_lower (f : Bounded M) (δ : ℝ)
    (hlower : ∀ j,δ ≤ (τ.trace (f.val j)).re) (j : ℕ) :
    δ ≤ ‖τ.trace (f.val j)‖ := (hlower j).trans (Complex.re_le_norm _)

def boundedCornerScalar (f b : Bounded M) (hf : ∀ j,IsStarProjection (f.val j))
    (δ : ℝ) (hδ : 0 < δ) (hlower : ∀ j,δ ≤ (τ.trace (f.val j)).re) : Bounded M :=
  ⟨fun j => (τ.trace (b.val j)/τ.trace (f.val j)) • f.val j,by
    obtain ⟨C,hC,hb⟩ := b.property
    refine ⟨C/δ,div_nonneg hC hδ.le,fun j => ?_⟩
    rw [norm_smul]
    apply (mul_le_of_le_one_right (norm_nonneg _) (hf j).norm_le).trans
    rw [norm_div]
    exact div_le_div₀ hC
      (((τ.norm_trace_le_norm₂ _).trans (τ.norm₂_le_norm _)).trans (hb j))
      hδ (corner_trace_norm_lower τ f δ hlower j)⟩

def boundedCornerCenter (f a : Bounded M) (hf : ∀ j,IsStarProjection (f.val j))
    (δ : ℝ) (hδ : 0 < δ) (hlower : ∀ j,δ ≤ (τ.trace (f.val j)).re) : Bounded M :=
  f*a*f-boundedCornerScalar τ f (f*a*f) hf δ hδ hlower

end

/-! A projection sequence of positive quotient trace can be changed on an
ultrafilter-null set so every coordinate corner has uniformly positive trace.
Coordinates are replaced only by the unit, preserving subalgebra membership. -/
open Filter
open scoped Topology

/-! A projection sequence of positive quotient trace can be changed on an
ultrafilter-null set so every coordinate corner has uniformly positive trace.
Coordinates are replaced only by the unit, preserving subalgebra membership. -/
open Filter
open scoped Topology

/-! Scalar normalization preserves exact corner support and centering. -/
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_QuotientRepresentation
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

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

/-! Fixed-index selection for bounded coordinate representatives. -/
open Filter
open scoped Topology
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

def sequenceEval (n : ℕ) : Sequences M →ₐ[ℂ] M.toStarSubalgebra where
  toFun a := a n
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_ResidualCompletion
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Actual residual projections, null-set masking, and coordinatewise
orthogonal partial-unitary patching. -/

/-! An actual positive residual support increment with exact ordered moments
for arbitrary countably many centered compressed quotient coefficients. -/
open Filter

/-! Faithful-trace completion criterion and the exact quarter-increment
residual estimate for actual orthogonal coordinate patches. -/

/-! Actual moment-preserving residual extensions, retaining coordinate partial
unitaries in N and the quantitative decrease of residual support. -/

/-! Iteration of actual moment-preserving partial-unitary extensions. Every
stage retains its coordinate representatives and a geometric residual bound. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

def quotientResidualTrace (ω : Ultrafilter ℕ) (v : ℕ → PartialUnitary M) : ℝ :=
  (quotientTrace τ ω (quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v))).re

end

/-! Coordinatewise monotone upper bounds and quantitative convergence in the
actual quotient two-norm. No completeness of the quotient is assumed. -/
open UltrapowerBridge Filter
open scoped Topology

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_LaurentMoments
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Extend exact moments by separate trace continuity in the two-norm. No
joint continuity of quotient multiplication, or operator-norm structure on Q,
is assumed. -/
section
open UltrapowerBridge Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

def traceClosedSpan (S : Set (Q τ ω)) : Submodule ℂ (Q τ ω) :=
  (Submodule.span ℂ S).topologicalClosure

/-! Extend exact moments by separate trace continuity in the two-norm. No
joint continuity of quotient multiplication, or operator-norm structure on Q,
is assumed. -/

end

/-! Construct an included Haar unitary and the full nonzero-integer endpoint
formula over any two-norm-separable unital subalgebra of the actual quotient. -/

/-! Extend a trace identity in each factor to the closed linear span of its
allowed values. This uses separate continuity only. -/

/-! Construct an included Haar unitary and the full nonzero-integer endpoint
formula over any two-norm-separable unital subalgebra of the actual quotient. -/

/-! From the endpoint formula to every alternating word shape. -/
open UltrapowerBridge Filter

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_HaarSequences
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! One constructed Haar extension retains endpoint moments, represented
norm-closed freeness, and an actual unitary sequence in the included algebra. -/

/-! Scalar expansion of same-sign gaps. Opposite-sign gaps must be centered,
so deleting a scalar gap can never cancel an entire power. -/

/-! Absorption of base-algebra unitaries, with signed scalar gap expansions. -/

/-! Successive Haar choices in algebraic star subalgebras of the tracial quotient, with freeness retained in their represented operator-norm closures. -/

/-! Free variables and prefixes with Haar endpoint properties of W and y=zW*. Coordinates are retained in the sequence data. -/
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

def prefixVariable (u : unitary (Q τ ω)) (t : ℕ → unitary (Q τ ω)) : ℕ → unitary (Q τ ω)
  | 0 => t 0
  | j+1 => u*t (j+1)

def prefixProduct (u : unitary (Q τ ω)) (t : ℕ → unitary (Q τ ω)) : ℕ → unitary (Q τ ω)
  | 0 => 1
  | j+1 => prefixProduct u t j*prefixVariable τ ω u t j

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_FreeGroupMoments
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Every nonempty reduced word in successive Haar variables has zero trace.
The induction eliminates the largest label, retaining centered lower-label gaps. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

def unitaryWord {A : Type*} (v : A → unitary (Q τ ω)) (w : List (A × Bool)) : Q τ ω :=
  (w.map (fun x => algebraSignedLetter (v x.1 : Q τ ω) (!x.2))).prod

end

/-! The actual free-group representation furnished by successive Haar variables. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

def unitaryRepresentation {A : Type*} (v : A → unitary (Q τ ω)) :
    FreeGroup A →* unitary (Q τ ω) := FreeGroup.lift v

end

/-! Reduced-word moments for p*y*(star p). Distinct labels have centered ratios;
reducedness requires distinct labels precisely at opposite-sign gaps. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)
variable {A : Type*}

def conjugateVariables (p : A → unitary (Q τ ω)) (y : unitary (Q τ ω))
    (a : A) : unitary (Q τ ω) := p a*y*star (p a)

def conjugateGaps (p : A → unitary (Q τ ω)) (a : A × Bool) :
    List (A × Bool) → List (Q τ ω × Bool)
  | [] => []
  | b::w => ((↑(star (p a.1)*p b.1) : Q τ ω),!b.2)::conjugateGaps p b w

def conjugateEnd (p : A → unitary (Q τ ω)) (a : A × Bool) : List (A × Bool) → Q τ ω
  | [] => ↑(star (p a.1))
  | b::w => conjugateEnd p b w

end

/-! Positive and negative conjugate terms in first-order correlation. Same-sign gaps require no centering hypothesis. -/
open UltrapowerBridge Filter

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_CoordinatePerturbation
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Group-ring maps from actual bounded unitary coordinates, with quotient
transport and coordinate Gram limits. -/
section
open UltrapowerBridge Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

def sequenceUnitaryQuotient : unitary (Sequences M) →* unitary (Q τ ω) where
  toFun u := ⟨sequenceQuotient τ ω (u : Sequences M),Unitary.map_mem (sequenceQuotient τ ω) u.property⟩
  map_one' := Subtype.ext (map_one (sequenceQuotient τ ω))
  map_mul' a b := Subtype.ext (map_mul (sequenceQuotient τ ω) (a : Sequences M) (b : Sequences M))

def coordinateGroupRing {A : Type*} (v : A → unitary (Sequences M)) :
    MonoidAlgebra ℂ (FreeGroup A) →ₐ[ℂ] Sequences M :=
  MonoidAlgebra.lift ℂ (Sequences M) (FreeGroup A)
    ((unitary (Sequences M)).subtype.comp (FreeGroup.lift v))

end

/-! Prefix labels and conjugate-word Gram identities for free-group perturbations. -/
section
attribute [local instance] Classical.propDecidable Classical.decEq
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

variable {hNM : N ≤ M} {seed : Set (Q τ ω)}

def SuccessiveCoordinateHaar.labelUnitary (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u : unitary (Q τ ω)) (ell : ℕ) (p : PrefixLabel ell) : unitary (Q τ ω) :=
  unitaryRepresentation τ ω (prefixVariable τ ω u (fun k => (F.step k).t)) p.val

def SuccessiveCoordinateHaar.targetUnitary (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u z : unitary (Q τ ω)) (ell : ℕ) : unitary (Q τ ω) :=
  z*(prefixProduct τ ω u (fun k => (F.step k).t) (ell+1))⁻¹

def SuccessiveCoordinateHaar.conjugateUnitary (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u z : unitary (Q τ ω)) (ell : ℕ) : PrefixLabel ell → unitary (Q τ ω) :=
  conjugateVariables τ ω (F.labelUnitary τ ω u ell) (F.targetUnitary τ ω u z ell)

end

section

/-! The finite-prefix analytic bound in the actual bounded-sequence/tracial
quotient realization. Word moments remain explicit premises: no free-Haar
existence or perturbation construction is asserted by this transport theorem. -/
open Filter
open scoped Topology
attribute [local instance] Classical.propDecidable Classical.decEq
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

def remainderSequence (n : ℕ) (α : ℝ)
    (Φ : MonoidAlgebra ℂ (FreeGroup (PrefixLabel n)) →ₐ[ℂ] Sequences M) : Sequences M :=
  ((finitePerturbationRows n α).map (fun r => NormedSpace.exp (Φ r))).prod -
    1 - ((finitePerturbationRows n α).map Φ).sum

end

/-! The literal bounded coordinate model of the finite-prefix free group.
The t_j sequences are the witnesses retained by the successive construction. -/
section
attribute [local instance] Classical.propDecidable Classical.decEq
open UltrapowerBridge Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

def constantQuotientUnitary (u : unitary M.toStarSubalgebra) : unitary (Q τ ω) :=
  sequenceUnitaryQuotient τ ω (constantSequenceUnitary u)

variable {hNM : N ≤ M} {seed : Set (Q τ ω)}

def SuccessiveCoordinateHaar.coordinateLabels (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u : unitary M.toStarSubalgebra) (ell : ℕ) (p : PrefixLabel ell) : unitary (Sequences M) :=
  FreeGroup.lift (F.coordinateVariables τ ω u) p.val

def SuccessiveCoordinateHaar.coordinateConjugates (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u z : unitary M.toStarSubalgebra) (ell : ℕ) (p : PrefixLabel ell) : unitary (Sequences M) :=
  F.coordinateLabels τ ω u ell p*F.coordinateTarget τ ω u z ell*(F.coordinateLabels τ ω u ell p)⁻¹

def SuccessiveCoordinateHaar.perturbationMap (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u z : unitary M.toStarSubalgebra) (ell : ℕ) :
    MonoidAlgebra ℂ (FreeGroup (PrefixLabel ell)) →ₐ[ℂ] Sequences M :=
  coordinateGroupRing (F.coordinateConjugates τ ω u z ell)

end

/-! The one literal bounded skew-adjoint perturbation K = i h. Every formal
row is its conjugate by the corresponding actual coordinate prefix. -/
attribute [local instance] Classical.propDecidable Classical.decEq
open UltrapowerBridge
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)
variable {hNM : N ≤ M} {seed : Set (Q τ ω)}

theorem SuccessiveCoordinateHaar.commonPerturbation_skew
    (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u z : unitary M.toStarSubalgebra) (ell : ℕ) (α : ℝ) :
    star (F.commonPerturbation τ ω u z ell α) = -F.commonPerturbation τ ω u z ell α := by
  let A : Sequences M := ∑ j : Fin ell,
    let a : Sequences M := ↑((F.coordinatePrefix τ ω u (j.val+1))⁻¹ *
      F.coordinateTarget τ ω u z ell * F.coordinatePrefix τ ω u (j.val+1))
    a-star a
  have hA : star A = -A := by
    unfold A
    rw [star_sum]
    calc
      _ = ∑ j : Fin ell, -(let a : Sequences M := ↑((F.coordinatePrefix τ ω u (j.val+1))⁻¹ *
          F.coordinateTarget τ ω u z ell * F.coordinatePrefix τ ω u (j.val+1)); a-star a) := by
        apply Finset.sum_congr rfl
        intro j _
        dsimp only
        rw [star_sub,star_star,neg_sub]
      _ = _ := Finset.sum_neg_distrib _
  change star ((α/(2*ell) : ℝ) • A) = -((α/(2*ell) : ℝ) • A)
  calc
    _ = (α/(2*ell) : ℝ) • star A := by rw [star_smul,star_trivial]
    _ = (α/(2*ell) : ℝ) • (-A) := congrArg ((α/(2*ell) : ℝ) • ·) hA
    _ = _ := smul_neg _ _

def SuccessiveCoordinateHaar.perturbingUnitary (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u z : unitary M.toStarSubalgebra) (ell : ℕ) (α : ℝ) : unitary (Sequences M) :=
  ⟨NormedSpace.exp (F.commonPerturbation τ ω u z ell α),
    NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
      (show F.commonPerturbation τ ω u z ell α ∈ skewAdjoint (Sequences M) from
        skewAdjoint.mem_iff.mpr (F.commonPerturbation_skew τ ω u z ell α))⟩

def SuccessiveCoordinateHaar.perturbedUnitary (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u z : unitary M.toStarSubalgebra) (ell : ℕ) (α : ℝ) : unitary (Sequences M) :=
  F.perturbingUnitary τ ω u z ell α*constantSequenceUnitary u

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_NormalTrace
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! A genuine linear state with exact equality of real quadratic values,
constructed from the original finite factor predicates by scalar compactness. -/

/-! Construction of a tracial state on the original concrete finite diffuse factor without a supplied trace. -/

/-! Every positive normalized tracial functional agrees with the dimension on
all projections. Lower and upper dyadic bounds use actual partial isometries. -/

/-! Identification of the actual tracial state with the spectral dimension
value, and unrestricted additivity for noncommuting self-adjoint operators. -/

/-! The constructed faithful normalized trace on the original algebra.
Projection-net continuity is proved explicitly; no general normality or
representation theorem is hidden in the definition. -/

/-! The constructed trace is dominated by a finite sum of concrete vector
functionals. The matrix partition is constructed inside the localized corner. -/
section
open scoped BigOperators CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
variable (hunit : (1 : M.toStarSubalgebra) ≠ 0)

attribute [local instance] OAI.Generator.Tracial.dominationCStar
attribute [local instance] OAI.Generator.Tracial.dominationLE
theorem traceFreeTrace_matrix_diagonal {ι : Type*} [Fintype ι]
    (Q : EquivalentPartition (⟨1,IsStarProjection.one _⟩ : AlgebraProjection M) ι)
    (x : M.toStarSubalgebra) :
    (∑ i, traceFreeTrace hfactor hdiff hfinite hunit (Q.stateCoefficient x i i))=
      traceFreeTrace hfactor hdiff hfinite hunit x := by
  let τ := traceFreeTrace hfactor hdiff hfinite hunit
  have ht := (traceFreeTrace_spec hfactor hdiff hfinite hunit).2.2.2.2
  have hi (i : ι) : τ (Q.stateCoefficient x i i)=τ ((Q.leg i).target.val*x) := by
    change τ ((star (Q.leg i).val*x)*(Q.leg i).val)=_
    rw [ht]
    congr 1
  change (∑ i, τ (Q.stateCoefficient x i i))=τ x
  simp_rw [hi]
  rw [← map_sum,← Finset.sum_mul,Q.total,one_mul]

attribute [local instance] OAI.Generator.Tracial.dominationOrder
local instance dominationPreorder_r197f51_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
attribute [local instance] OAI.Generator.Tracial.dominationStarOrder
/-- The scalar Cauchy--Schwarz bound follows from positivity of a centered square. -/
theorem traceFreeTrace_norm_sq_le (x : M.toStarSubalgebra) :
    ‖traceFreeTrace hfactor hdiff hfinite hunit x‖^2 ≤
      (traceFreeTrace hfactor hdiff hfinite hunit (star x*x)).re := by
  let τ := traceFreeTrace hfactor hdiff hfinite hunit
  obtain ⟨_,h1,hpos,hstar,_⟩ := traceFreeTrace_spec hfactor hdiff hfinite hunit
  change τ 1=1 at h1
  change ∀ x : M.toStarSubalgebra, τ (star x)=star (τ x) at hstar
  have h := hpos (star (x-(τ x) • 1)*(x-(τ x) • 1)) (star_mul_self_nonneg _)
  change 0 ≤ (τ (star (x-(τ x) • 1)*(x-(τ x) • 1))).re at h
  have he : τ (star (x-(τ x) • 1)*(x-(τ x) • 1))=
      τ (star x*x)-star (τ x)*(τ x) := by
    simp only [star_sub,star_smul,star_one,sub_mul,mul_sub,smul_mul_assoc,
      mul_smul_comm,mul_one,one_mul,map_sub,map_smul,smul_eq_mul,h1,hstar]
    ring
  rw [he,Complex.sub_re] at h
  change ‖τ x‖^2 ≤ (τ (star x*x)).re
  have hn : (star (τ x)*(τ x)).re=‖τ x‖^2 := by
    rw [RCLike.star_def,Complex.conj_mul',← Complex.ofReal_pow,Complex.ofReal_re]
  rw [hn] at h
  linarith

end

/-! Finite vector-functional representation and actual ultraweak continuity of
the constructed trace. No normality criterion is taken as an axiom. -/
open scoped BigOperators CStarAlgebra

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_WordCorrelation
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! Ordered prefix cancellation for the actual common perturbed unitary.
All identities are identities of bounded coordinate sequences. -/
namespace Tracial

section
attribute [local instance] Classical.propDecidable Classical.decEq
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)
variable {hNM : N ≤ M} {seed : Set (Q τ ω)}

def SuccessiveCoordinateHaar.perturbedWord (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u z : unitary M.toStarSubalgebra) (ell : ℕ) (α : ℝ) : unitary (Sequences M) :=
  F.haarSequence τ ω 0*((List.range ell).map
    (fun k => F.perturbedUnitary τ ω u z ell α*F.haarSequence τ ω (k+1))).prod

end

/-! The exact first-order trace calculation for the manuscript's prefix labels. -/
section
attribute [local instance] Classical.propDecidable Classical.decEq
open UltrapowerBridge Filter
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)
variable {hNM : N ≤ M} {seed : Set (Q τ ω)}

def SuccessiveCoordinateHaar.firstOrderTerm
    (F : SuccessiveCoordinateHaar τ ω hNM seed) (u z : unitary (Q τ ω)) (ell : ℕ) (c : ℂ) : Q τ ω :=
  c • ∑ k : Fin ell,∑ j : Fin ell,
    ((F.conjugateUnitary τ ω u z ell (pairLabel k j) : Q τ ω)-
      star (F.conjugateUnitary τ ω u z ell (pairLabel k j) : Q τ ω))

end

/-! The first-order term is exactly the sum of the mapped formal rows, and
its correlation is the manuscript's alpha/2 coefficient. -/

/-! The uniform trace correlation for the actual product of coordinate
exponentials. Identifying that product with a single-unitary perturbation word
is a separate remaining step. -/

/-! The uniform correlation now belongs to the literal word in one common
perturbed unitary, as required by eq:perturbation-prefix. -/
open UltrapowerBridge

end Tracial

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_PerturbationBounds
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! Exact 2 ell signed coefficients in each formal row. In particular the
identity prefix label is still a nonidentity basis letter in the formal group. -/

/-! Exact trace-two-norm of the single common logarithmic perturbation. -/
namespace Tracial

/-! Sharp trace-two-norm displacement of a skew-adjoint exponential, via the
real path t ↦ exp(t K). This proves the scalar-calculus estimate used in the
manuscript without an extra exponential factor. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

def traceVectorCLM : M.toStarSubalgebra →L[ℂ] H :=
  ({ toFun := fun a => (a : H →L[ℂ] H) τ.vector
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : M.toStarSubalgebra →ₗ[ℂ] H).mkContinuous 1
    (fun a => by
      change τ.norm₂ a ≤ 1*‖a‖
      simpa only [one_mul] using τ.norm₂_le_norm a)

end

/-! A single coordinate satisfies the size and correlation bounds for the
literal word. Its P-valued unitary letters are the retained construction. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)
variable {hNM : N ≤ M} {seed : Set (Q τ ω)}

def unitaryCoordinate (a : unitary (Sequences M)) (n : ℕ) : unitary M.toStarSubalgebra :=
  ⟨(a : Sequences M) n,⟨congrArg (fun b : Sequences M => b n) a.property.1,
    congrArg (fun b : Sequences M => b n) a.property.2⟩⟩

def SuccessiveCoordinateHaar.retainedUnitary (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (j n : ℕ) : unitary N.toStarSubalgebra :=
  ⟨(F.step j).coordinates.val n,(F.step j).unitary_coordinates n⟩

end

/-! The manuscript's two perturbation inequalities, constructed under explicit
faithful vector-trace, irreducibility, diffuseness and trace-vector separability
data. No perturbation endpoint or free-moment premise is assumed. -/
open UltrapowerBridge Filter

end Tracial

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_RelativeGeneration
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.quotientInnerProductSpace _root_.OAI.Generator.Tracial.quotientNormedAddCommGroup _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! Actual finite star polynomials in one unitary variable and coefficients in
an included von Neumann algebra. Both uniform operator bounds and continuity
of trace-vector evaluation are proved by recursion on the expression. -/
open Filter
open scoped Topology

/-! The literal algebra W*(N,u), its trace Hilbert subspace, and density of
actual N-coefficient star-polynomial values in that subspace. -/
open Filter
open scoped Topology
namespace Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (hNM : N ≤ M)

def relativeTraceSpace (u : TraceUnitary τ) : Submodule ℂ H :=
  vectorOrbitClosure (relativeGenerated (N := N) τ u).toStarSubalgebra τ.vector

instance relativeTraceSpace_complete (u : TraceUnitary τ) :
    CompleteSpace (relativeTraceSpace (N := N) τ u) :=
  inferInstanceAs (CompleteSpace (vectorOrbitClosure _ _))

theorem polynomialVector_mem (p : Generator.RelativePolynomial N.toStarSubalgebra)
    (u : TraceUnitary τ) : RelativePolynomial.sectionVector τ hNM p u ∈
      relativeTraceSpace (N := N) τ u :=
  Submodule.le_topologicalClosure _ ⟨⟨(RelativePolynomial.eval τ hNM p u).val,
    RelativePolynomial.valueAlgebra_le τ u (RelativePolynomial.eval_mem τ hNM p u)⟩,rfl⟩

end Tracial

/-! The literal interleaved word belongs to W*(N,u), is unitary, and has
trace norm one. The printed perturbation-size bound tends to zero. -/
open Filter
open scoped Topology

/-! Projection continuity for generated algebras, using the complete trace-unitary metric, dense polynomial sections, and trace-vector separability. -/
open Filter
open scoped Topology
namespace Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (hNM : N ≤ M)

/-! The bounded conditional expectation agrees with the actual Hilbert
projection. Proper subalgebras have a unitary outside them, yielding the
nonzero represented residual used by thm:relative-generation. -/

def subalgebraResidual (x : M.toStarSubalgebra) : M.toStarSubalgebra :=
  x-conditionalExpectation τ hNM x

end Tracial

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.RelativeGeneration_LocusTopology
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.quotientInnerProductSpace _root_.OAI.Generator.Tracial.quotientNormedAddCommGroup _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

open scoped Topology

namespace Generator.Tracial

open UltrapowerBridge

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (hNM : N ≤ M)

def relativeDistance (ξ : H) (unitary : TraceUnitary τ) : ℝ :=
  Metric.infDist ξ (relativeTraceSpace (N := N) τ unitary : Set H)

end Generator.Tracial

end

end OAI
end


