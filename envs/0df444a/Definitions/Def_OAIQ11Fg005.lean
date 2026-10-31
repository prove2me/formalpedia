-- Prove2me | Definitions.Def_OAIQ11Fg005
-- name    : OAIQ11Fg005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T09:35:12.37721+00:00
-- url     : https://prove2.me/theorems/9d88360d-a11d-4799-b79a-734b28c023e0
-- title:
--   Definitions bundle OAIQ11Fg005 of the split of OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 190 declarations of OpenAI's Lean: 88 definitions, 2 inductive types or structures, 2 instances and 98 theorems. The definitions and types are `OAI.Generator.Tracial.CornerPartition.blockStarAlgebra`, `OAI.Generator.Tracial.CornerPartition.blockVonNeumann`, `OAI.Generator.Tracial.CornerPartition.jointPiece`, `OAI.Generator.Tracial.EquivalentPartition`, `OAI.Generator.Tracial.EquivalentPartition.link`, `OAI.Generator.Tracial.EquivalentPartition.matrixVectorFunctional`, `OAI.Generator.Tracial.EquivalentPartition.singleton`, `OAI.Generator.Tracial.EquivalentPartition.stateCoefficient`, `OAI.Generator.Tracial.PartialIsometry.orthogonalPartialSum`, `OAI.Generator.Tracial.PartialIsometry.rangeLink`, `OAI.Generator.Tracial.SpectralInterval`, `OAI.Generator.Tracial.SpectralInterval.midpoint`, `OAI.Generator.Tracial.algebraPositiveResolvent`, `OAI.Generator.Tracial.ambientAbsoluteValue`, `OAI.Generator.Tracial.approxTraceCStar`, `OAI.Generator.Tracial.approxTraceLE`, `OAI.Generator.Tracial.approximationCStar`, `OAI.Generator.Tracial.approximationLE`, `OAI.Generator.Tracial.approximationOrder`, `OAI.Generator.Tracial.approximationPreorder`, `OAI.Generator.Tracial.clippingCStar`, `OAI.Generator.Tracial.conjugateFunctional`, `OAI.Generator.Tracial.cornerCutCStar`, `OAI.Generator.Tracial.cornerCutLE`, `OAI.Generator.Tracial.cornerCutOrder`, `OAI.Generator.Tracial.cornerCutPreorder`, `OAI.Generator.Tracial.cornerExtend`, `OAI.Generator.Tracial.cornerProject`, `OAI.Generator.Tracial.cornerSpace`, `OAI.Generator.Tracial.cornerSpectralShift`, `OAI.Generator.Tracial.cornerStarAlgebra`, `OAI.Generator.Tracial.cornerStateCStar`, `OAI.Generator.Tracial.cornerStateLE`, `OAI.Generator.Tracial.cornerStateOrder`, `OAI.Generator.Tracial.cornerValueCStar`, `OAI.Generator.Tracial.cornerValueLE`, `OAI.Generator.Tracial.cornerValueOrder`, `OAI.Generator.Tracial.dominationCStar`, `OAI.Generator.Tracial.dominationLE`, `OAI.Generator.Tracial.dominationOrder` and 50 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `FactorGeneration_CornerTrace`, `FactorGeneration_DyadicComparison`, `FactorGeneration_Expectations`, `FactorGeneration_FiniteComparison`, `FactorGeneration_FreeWords`, `FactorGeneration_FunctionalLimits`, `FactorGeneration_HilbertLimits`, `FactorGeneration_LocalizedStates`, `FactorGeneration_LongWords`, `FactorGeneration_MonotoneTrace`, `FactorGeneration_NormalTrace`, `FactorGeneration_OperatorLimits`, `FactorGeneration_Pinching`, `FactorGeneration_ProjectionLimits`, `FactorGeneration_RepresentedCorners`, `FactorGeneration_SpectralApproximation`, `FactorGeneration_SpectralPinching`, `FactorGeneration_SpectralStates`, `FactorGeneration_SpectralTruncation`, `FactorGeneration_Subfactors`, `FactorGeneration_Supports`, `FactorGeneration_TraceHilbert`.
--
--   **Imports.** It imports the published bundle `Def_FactorGeneration`; the bundles `OAIQ11Fg001` and `OAIQ11Fg002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ11Fg007`, `OAIQ11Fg008`, `OAIQ11Fg009` and `OAIQ11Fg010`; the statements `OAI_Generator_MatrixUnitSystem_coefficientHom_surjective`, `OAI_Generator_MatrixUnitSystem_coefficient_corner`, `OAI_Generator_MatrixUnitSystem_coefficient_diagonal`, `OAI_Generator_MatrixUnitSystem_relative_product_inside`, `OAI.Generator.Tracial.CornerPartition.block_commutant_mem_subalgebra`, `OAI_Generator_Tracial_boundedCompletedUnitary_unitary`, `OAI_Generator_Tracial_boundedPartialSupport_projection`, `OAI_Generator_Tracial_boundedPartialUnitary_final`, `OAI_Generator_Tracial_boundedPartialUnitary_initial`, `OAI_Generator_Tracial_exists_centered_dense_quotient_family`, `OAI_Generator_Tracial_exists_component_controlled_refinement`, `OAI_Generator_Tracial_exists_quotient_corner_partial_sequence`, `OAI_Generator_Tracial_maskPartialSequence_quotient`, `OAI_Generator_Tracial_optionalCoefficient_range`, `OAI_Generator_Tracial_ordered_sum_zero_of_all_mixed`, `OAI_Generator_Tracial_orthonormal_of_coordinate_moments`, `OAI_Generator_Tracial_quotient_bounded_mul_tendsto`, `OAI_Generator_Tracial_quotient_completed_eq`, `OAI_Generator_Tracial_quotient_fixed_left_tendsto`, `OAI_Generator_Tracial_quotient_fixed_right_tendsto`, `OAI_Generator_Tracial_quotient_ordered_moment_zero`, `OAI_Generator_Tracial_quotient_partial_core_tendsto`, `OAI_Generator_Tracial_quotient_partial_signed_tendsto`, `OAI_Generator_Tracial_quotient_residual_all_words_centered`, `OAI_Generator_Tracial_quotient_residual_word_centered`, `OAI_Generator_Tracial_quotient_residual_word_unit_right`, `OAI_Generator_Tracial_quotient_unitary_of_coordinates`, `OAI_Generator_Tracial_signedLetter_integer` and `OAI_Generator_Tracial_signed_conjugate`; the proofs of `OAI_Generator_MatrixUnitSystem_coefficientHom_surjective`, `OAI_Generator_MatrixUnitSystem_coefficient_corner`, `OAI_Generator_MatrixUnitSystem_coefficient_diagonal`, `OAI_Generator_MatrixUnitSystem_relative_product_inside`, `OAI_Generator_MatrixUnitSystem_two_generators_of_four_commutant_generators`, `OAI_Generator_Tracial_boundedPartialSupport_projection`, `OAI_Generator_Tracial_bounded_coordinate_unitaries_inclusion`, `OAI_Generator_Tracial_exists_centered_dense_quotient_family`, `OAI_Generator_Tracial_exists_coordinate_monotone_upper`, `OAI_Generator_Tracial_exists_exact_residual_step`, `OAI_Generator_Tracial_exists_supported_centered_contraction`, `OAI_Generator_Tracial_optionalCoefficient_range`, `OAI_Generator_Tracial_ordered_sum_zero_of_all_mixed`, `OAI_Generator_Tracial_orthonormal_of_coordinate_moments`, `OAI_Generator_Tracial_quotientMap_eq_of_eventuallyEq`, `OAI_Generator_Tracial_quotient_bounded_mul_tendsto`, `OAI_Generator_Tracial_quotient_completed_eq`, `OAI_Generator_Tracial_quotient_fixed_left_tendsto`, `OAI_Generator_Tracial_quotient_fixed_right_tendsto`, `OAI_Generator_Tracial_quotient_partial_core_tendsto`, `OAI_Generator_Tracial_quotient_partial_signed_tendsto`, `OAI_Generator_Tracial_quotient_residual_all_words_centered`, `OAI_Generator_Tracial_quotient_residual_word_centered`, `OAI_Generator_Tracial_quotient_residual_word_unit_right`, `OAI_Generator_Tracial_quotient_unitary_of_coordinates`, `OAI_Generator_Tracial_represented_four_selfAdjoint_generators`, `OAI_Generator_Tracial_signedLetter_integer`, `OAI_Generator_Tracial_signed_conjugate` and `OAI_Generator_idempotent_mem_wstar_of_gap`.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_FactorGeneration
import Definitions.Def_OAIQ11Fg001
import Definitions.Def_OAIQ11Fg002

section
-- module Solutions.OAIQ11_FG.FactorGeneration_OperatorLimits
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator

/-! Operator-norm completeness of the manuscript's concrete algebra, derived
from its actual double-commutant property. No quotient completeness is assumed. -/
namespace Tracial

/-! Bounded operator families have weak operator ultralimits. This is proved
from Banach--Alaoglu and Riesz representation, not assumed as compactness. -/
open Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! Operator-norm balls of an actual von Neumann algebra are compact for the
weak operator topology, using the previously constructed operator ultralimits. -/

theorem weakOperatorBall_isCompact (M : VonNeumannAlgebra H) (C : ℝ) :
    IsCompact (weakOperatorBall M C) := by
  classical
  by_cases hC : 0 ≤ C
  · apply isCompact_iff_ultrafilter_le_nhds'.mpr
    intro ω hω
    let a : (H →WOT[ℂ] H) → M.toStarSubalgebra := fun T =>
      if h : T ∈ weakOperatorBall M C then ⟨T.toCLM,h.1⟩ else 0
    have ha (T : H →WOT[ℂ] H) : ‖a T‖ ≤ C := by
      dsimp [a]
      split_ifs with h
      · exact h.2
      · change ‖(0 : H →L[ℂ] H)‖ ≤ C
        simpa only [norm_zero] using hC
    obtain ⟨T,hT,ht⟩ := exists_weak_operator_ultralimit ω (fun U => (a U).val) C hC ha
    have hm := weak_operator_limit_mem M a T ht
    refine ⟨ContinuousLinearMapWOT.ofCLM T,⟨hm,hT⟩,?_⟩
    have hl : Tendsto (fun U => ContinuousLinearMapWOT.ofCLM (a U).val)
        (ω : Filter (H →WOT[ℂ] H)) (𝓝 (ContinuousLinearMapWOT.ofCLM T)) :=
      ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto.mpr ht
    have he : (fun U => ContinuousLinearMapWOT.ofCLM (a U).val) =ᶠ[ω] id := by
      filter_upwards [show ∀ᶠ U in (ω : Filter (H →WOT[ℂ] H)),U ∈ weakOperatorBall M C from hω]
        with U hU
      simp only [a,dite_eq_left hU,ContinuousLinearMapWOT.ofCLM_toCLM,id_eq]
    exact hl.congr' he
  · have he : weakOperatorBall M C=∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro T hT
      exact hC ((norm_nonneg _).trans hT.2)
    rw [he]
    exact isCompact_empty

end Tracial

/-! Operator order bounds are closed in the weak operator topology. -/

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_ProjectionLimits
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! A nonzero projection in a diffuse tracial algebra contains nonzero projections of arbitrarily small trace. -/

/-! Monotone projection limits with trace bounds, giving chain bounds for prescribed trace cuts. -/

/-! Exact trace cuts in a diffuse coordinate algebra. -/

/-! Algebraic part of Popa 1308.3982v3, Lemma 3.2: adding a supported
partial unitary in the residual corner. The small mixed-word estimates and
the existence of an appropriate patch are separate analytic requirements. -/

/-! Dyadic projections inside a diffuse algebra with faithful trace. -/
section
open UltrapowerBridge
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q = q ∧ q*p = q)

theorem orthogonal_subprojections {p q a b : AlgebraProjection M}
    (hpq : p.val*q.val=0) (ha : a ≤ p) (hb : b ≤ q) : a.val*b.val=0 := by
  calc a.val*b.val = (a.val*p.val)*(q.val*b.val) := by rw [projection_mul_of_le ha,hb]
       _ = a.val*(p.val*q.val)*b.val := by simp only [mul_assoc]
       _ = 0 := by rw [hpq,mul_zero,zero_mul]

end

/-! Finite spectral sums in the constructed dyadic projection algebras. -/
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

variable {ι : Type*} [Fintype ι]

def projectionSum (a : ι → AlgebraProjection M) (c : ι → ℂ) : M.toStarSubalgebra :=
  ∑ i, c i • (a i).val

theorem projectionSum_star (a : ι → AlgebraProjection M) (c : ι → ℂ) :
    star (projectionSum a c)=projectionSum a (fun i => star (c i)) := by
  simp only [projectionSum,star_sum,star_smul,(a _).property.isSelfAdjoint.star_eq]

theorem projectionSum_mul (a : ι → AlgebraProjection M)
    (ha : ∀ i j, i ≠ j → (a i).val*(a j).val=0) (c d : ι → ℂ) :
    projectionSum a c*projectionSum a d=projectionSum a (fun i => c i*d i) := by
  classical
  unfold projectionSum
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  rw [Finset.sum_eq_single i]
  · rw [smul_mul_assoc,mul_smul_comm,smul_smul,(a i).property.isIdempotentElem.eq]
  · intro j _ hji
    rw [smul_mul_assoc,mul_smul_comm,ha i j hji.symm,smul_zero,smul_zero]
  · simp

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_CornerTrace
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.sequencesIsTopologicalRing _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Trace estimates in the actual ambient algebra. The corner scalar uses
its normalized trace. These estimates do not assume or assert the existence
of a local-quantizing projection. -/

/-! Actual noncommutative L1 on the coordinate algebra: trace(sqrt(x* x)).
The supported L2-to-L1 estimate retains the square root of the support trace.
No quantizing projection or conditional expectation theorem is assumed. -/
section
open scoped CStarAlgebra
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

attribute [local instance] OAI.Generator.Tracial.instCStarAlgebraSubtypeContinuousLinearMapComplexIdMemStarSubalgebra_solutions
attribute [local instance] OAI.Generator.Tracial.instPartialOrderSubtypeContinuousLinearMapComplexIdMemStarSubalgebra_solutions
attribute [local instance] OAI.Generator.Tracial.instLESubtypeContinuousLinearMapComplexIdMemStarSubalgebra_solutions
attribute [local instance] OAI.Generator.Tracial.instStarOrderedRingSubtypeContinuousLinearMapComplexIdMemStarSubalgebra_solutions
def traceAbs (x : M.toStarSubalgebra) : M.toStarSubalgebra := CFC.sqrt (star x*x)

end

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
-- module Solutions.OAIQ11_FG.FactorGeneration_HilbertLimits
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator

/-! Multiplication and adjoint limits in L2, with the necessary uniform
operator norm bounds stated explicitly. -/

/-! A separating vector for a concrete von Neumann algebra is cyclic for its
commutant. The original representation need not be cyclic for the algebra. -/
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

instance vectorOrbitClosure_complete (S : StarSubalgebra ℂ (H →L[ℂ] H)) (ξ : H) :
    CompleteSpace (vectorOrbitClosure S ξ) :=
  inferInstanceAs (CompleteSpace (vectorOrbitMap S ξ).range.topologicalClosure)

theorem mem_vectorOrbitClosure (S : StarSubalgebra ℂ (H →L[ℂ] H)) (ξ : H) :
    ξ ∈ vectorOrbitClosure S ξ :=
  Submodule.le_topologicalClosure _ ⟨1,rfl⟩

end

/-! Restrict the faithful trace representation to the closure of M times its
trace vector. This constructs a faithful, isometric, cyclic representation on
an actual Hilbert subspace. No Banach predual or WOT-closed image is asserted. -/

/-! A real linear functional continuous for bounded trace-two-norm sequences
is WOT continuous on the unit ball. Closed convex slices of the trace-vector
ball supply the conversion; no identification of the two topologies is assumed. -/
open Filter
open scoped Topology

/-! On a uniformly operator-norm bounded family in a faithfully vector-traced
von Neumann algebra, L2 convergence implies strong and adjoint-strong convergence
in the original Hilbert space. -/
open Filter
open scoped Topology

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_Supports
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed _root_.OAI.Generator.vectorOrbitClosure_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Kernel and range projections constructed in the actual von Neumann algebra.
Membership follows from commutant invariance, with no spectral theorem assumed. -/

/-! Spectral sign cuts from continuous positive parts and actual range projections.
These are constructed operators, not assumed Borel functional calculus data. -/
open scoped CStarAlgebra
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance positiveSupportCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance positiveSupportOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance positiveSupportPreorder_r2838f1_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance positiveSupportLE_r2838f1_1 : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance positiveSupportStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

end

/-! A polar operator is constructed by extending the isometry on a range.
No polar-decomposition or projection-comparison hypothesis is used. -/

/-! Polar decomposition inside the given concrete von Neumann algebra. -/
open scoped CStarAlgebra

/-! Exact initial and final support projections of the constructed polar part. -/
open scoped CStarAlgebra
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_FiniteComparison
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator

/-! The closed span of algebra translates of a projection range gives its
central support. All operators act on the original Hilbert space; no trace,
cyclic vector, separability, finiteness, or comparison theorem is assumed. -/

/-! The original finiteness predicate excludes proper self-equivalence of a
projection. Projection comparison is connected to the unchanged IsII1Factor
predicate, with no representation, trace, or separability premise. -/

/-! Arbitrary-chain bounds with moving orthogonal initial and final supports, obtained from successive fixed-multiplier weak operator limits without a trace. -/
namespace Tracial
open Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

namespace PartialIsometry

theorem target_mono {v w : PartialIsometry M} (h : v ≤ w) : v.target ≤ w.target := by
  apply (v.target_le_iff_mul w.target).mpr
  calc _ = w.target.val*(w.val*v.support.val) := by rw [h]
       _ = v.val := by rw [← mul_assoc,w.target_mul,h]

/-! Simultaneous least initial and final support bounds for arbitrary directed
partial-isometry nets. The actual ultralimit is chosen once for all bounds. -/

end PartialIsometry
end Tracial

/-! Complete actual partial isometries to unitaries in a finite factor.
The construction uses projection comparison and finiteness, without a trace. -/
open scoped CStarAlgebra

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_DyadicComparison
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator

/-! Halving every projection in a diffuse factor without a trace.
Maximality leaves no residual corner: a diffuse residual splits into two
nonzero orthogonal projections, and a polar link gives a strict extension. -/
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Tracial
variable {M : VonNeumannAlgebra H}

/-- A proper diffuse subprojection splits a nonzero corner into orthogonal pieces. -/
theorem traceFree_exists_orthogonal_split
    (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
      ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (p : AlgebraProjection M) (hp : p.val≠0) :
    ∃ q r : AlgebraProjection M, q ≤ p ∧ r ≤ p ∧ q.val≠0 ∧ r.val≠0 ∧
      q.val*r.val=0 ∧ q.val+r.val=p.val := by
  obtain ⟨q,hq,hq0,hqp,hpq,hqp'⟩ := hdiff p.val p.property hp
  let r : AlgebraProjection M := ⟨p.val-q,hq.sub_of_mul_eq_right p.property hpq⟩
  refine ⟨⟨q,hq⟩,r,hpq,?_,hq0,sub_ne_zero.mpr hqp.symm,?_,?_⟩
  · change p.val*(p.val-q)=p.val-q
    rw [mul_sub,p.property.isIdempotentElem.eq,hpq]
  · change q*(p.val-q)=0
    rw [mul_sub,hqp',hq.isIdempotentElem.eq,sub_self]
  · change q+(p.val-q)=p.val
    abel

end Tracial

end

/-! Finite partitions with explicit equivalence witnesses and compatible binary
refinement. The common initial projection is halved once and its two pieces
are transported to every old piece, so all new pieces remain equivalent. -/
section
open scoped BigOperators
namespace Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-- A partition of p with actual partial isometries from a common projection.
The cross identities encode orthogonality. This structure is constructed below. -/
structure EquivalentPartition (p : AlgebraProjection M) (ι : Type*) [Fintype ι] where
  base : AlgebraProjection M
  leg : ι → PartialIsometry M
  initial : ∀ i, (leg i).support=base
  cross : ∀ i j, i≠j → star (leg i).val*(leg j).val=0
  total : ∑ i, (leg i).target.val=p.val
  bound : ∀ i, (leg i).target ≤ p

namespace EquivalentPartition
variable {p : AlgebraProjection M} {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem orthogonal (E : EquivalentPartition p ι) (i j : ι) (hij : i≠j) :
    (E.leg i).target.val*(E.leg j).target.val=0 := by
  change ((E.leg i).val*star (E.leg i).val)*((E.leg j).val*star (E.leg j).val)=0
  calc _ = (E.leg i).val*(star (E.leg i).val*(E.leg j).val)*star (E.leg j).val := by
           simp only [mul_assoc]
       _ = 0 := by rw [E.cross i j hij,mul_zero,zero_mul]

/-- Every ordered pair of pieces has a displayed equivalence witness. -/
def link (E : EquivalentPartition p ι) (i j : ι) : PartialIsometry M :=
  (E.leg j).compose (E.leg i).adjoint (by
    have h : (E.leg i).adjoint.target=(E.leg i).support := by
      apply Subtype.ext
      change star (E.leg i).val*star (star (E.leg i).val)=(E.leg i).support.val
      rw [star_star,(E.leg i).initial]
    rw [h,E.initial,E.initial])

theorem link_support (E : EquivalentPartition p ι) (i j : ι) :
    (E.link i j).support=(E.leg i).target := rfl

theorem link_target (E : EquivalentPartition p ι) (i j : ι) :
    (E.link i j).target=(E.leg j).target := by
  apply Subtype.ext
  change ((E.leg j).val*star (E.leg i).val)*star ((E.leg j).val*star (E.leg i).val)=_
  calc _ = (E.leg j).val*(star (E.leg i).val*(E.leg i).val)*star (E.leg j).val := by
           simp only [star_mul,star_star,mul_assoc]
       _ = (E.leg j).val*star (E.leg j).val := by
           rw [(E.leg i).initial,E.initial,← E.initial j,(E.leg j).mul_support]
       _ = _ := rfl

/-- Depth zero consists of the original projection itself. -/
def singleton (p : AlgebraProjection M) : EquivalentPartition p Unit where
  base := p
  leg _ := PartialIsometry.onProjection p
  initial _ := rfl
  cross i j hij := (hij (Subsingleton.elim _ _)).elim
  total := by simp only [PartialIsometry.onProjection_target,Fintype.sum_unique]
  bound _ := by rw [PartialIsometry.onProjection_target]

end EquivalentPartition
end Tracial

/-! Coherent dyadic equivalent partitions and matrix units, constructed from
scalar center and diffuseness without a trace. DyadicIndex is reused as a
finite binary index type; no tracial partition construction is used. -/
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Tracial
variable {M : VonNeumannAlgebra H}
namespace EquivalentPartition
variable {p : AlgebraProjection M} {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- A partition of a nonzero projection has no zero piece, since every
piece is equivalent to every other piece by the displayed links. -/
theorem target_ne_zero (E : EquivalentPartition p ι) (hp : p.val≠0) (i : ι) :
    (E.leg i).target.val≠0 := by
  intro hi
  have hz (j : ι) : (E.leg j).target.val=0 := by
    have hw : (E.link i j).val=0 := by
      have hm := (E.link i j).mul_support
      rw [E.link_support,hi,mul_zero] at hm
      exact hm.symm
    rw [← E.link_target i j]
    change (E.link i j).val*star (E.link i j).val=0
    rw [hw,zero_mul]
  have ht := E.total
  simp only [hz,Finset.sum_const_zero] at ht
  exact hp ht.symm

end EquivalentPartition

end Tracial

end

/-! Actual sums of countable orthogonal partial isometries, including least
initial/final support identities. No trace or countable-cofinality premise. -/
namespace Tracial

section
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace PartialIsometry

variable (a : ℕ → PartialIsometry M)
variable (hp : ∀ i j, i ≠ j → (a i).support.val*(a j).support.val=0)
variable (hq : ∀ i j, i ≠ j → (a i).target.val*(a j).target.val=0)

include hp hq in
theorem exists_orthogonalPartialSum (n : ℕ) :
    ∃ v : PartialIsometry M, v.val=∑ i ∈ Finset.range n, (a i).val ∧
      v.support.val=∑ i ∈ Finset.range n, (a i).support.val ∧
      v.target.val=∑ i ∈ Finset.range n, (a i).target.val := by
  induction n with
  | zero => exact ⟨zero, by simp [zero], by simp [zero], by simp [zero,target]⟩
  | succ n ih =>
    obtain ⟨v,hv,hs,ht⟩ := ih
    have ho₁ : v.support.val*(a n).support.val=0 := by
      rw [hs,Finset.sum_mul]
      exact Finset.sum_eq_zero (fun i hi => hp i n (Nat.ne_of_lt (Finset.mem_range.mp hi)))
    have ho₂ : v.target.val*(a n).target.val=0 := by
      rw [ht,Finset.sum_mul]
      exact Finset.sum_eq_zero (fun i hi => hq i n (Nat.ne_of_lt (Finset.mem_range.mp hi)))
    refine ⟨patch v (a n) ho₁ ho₂, ?_, ?_, ?_⟩
    · change v.val+(a n).val=_
      rw [hv,Finset.sum_range_succ]
    · change v.support.val+(a n).support.val=_
      rw [hs,Finset.sum_range_succ]
    · rw [patch_target,ht,Finset.sum_range_succ]

def orthogonalPartialSum (n : ℕ) : PartialIsometry M :=
  (exists_orthogonalPartialSum a hp hq n).choose

theorem orthogonalPartialSum_val (n : ℕ) :
    (orthogonalPartialSum a hp hq n).val=∑ i ∈ Finset.range n, (a i).val :=
  (exists_orthogonalPartialSum a hp hq n).choose_spec.1

theorem orthogonalPartialSum_support (n : ℕ) :
    (orthogonalPartialSum a hp hq n).support.val=∑ i ∈ Finset.range n, (a i).support.val :=
  (exists_orthogonalPartialSum a hp hq n).choose_spec.2.1

theorem orthogonalPartialSum_target (n : ℕ) :
    (orthogonalPartialSum a hp hq n).target.val=∑ i ∈ Finset.range n, (a i).target.val :=
  (exists_orthogonalPartialSum a hp hq n).choose_spec.2.2

theorem le_orthogonalPartialSum (i n : ℕ) (hin : i < n) :
    a i ≤ orthogonalPartialSum a hp hq n := by
  change (orthogonalPartialSum a hp hq n).val*(a i).support.val=(a i).val
  rw [orthogonalPartialSum_val,Finset.sum_mul]
  apply Finset.sum_eq_single_of_mem i (Finset.mem_range.mpr hin) _ |>.trans (a i).mul_support
  intro j _ hji
  calc (a j).val*(a i).support.val = ((a j).val*(a j).support.val)*(a i).support.val := by
         rw [(a j).mul_support]
       _ = 0 := by rw [mul_assoc,hp j i hji,mul_zero]

theorem orthogonalPartialSum_monotone : Monotone (orthogonalPartialSum a hp hq) := by
  apply monotone_nat_of_le_succ
  intro n
  let v := orthogonalPartialSum a hp hq n
  have ho₁ : v.support.val*(a n).support.val=0 := by
    rw [orthogonalPartialSum_support,Finset.sum_mul]
    exact Finset.sum_eq_zero (fun i hi => hp i n (Nat.ne_of_lt (Finset.mem_range.mp hi)))
  have ho₂ : v.target.val*(a n).target.val=0 := by
    rw [orthogonalPartialSum_target,Finset.sum_mul]
    exact Finset.sum_eq_zero (fun i hi => hq i n (Nat.ne_of_lt (Finset.mem_range.mp hi)))
  have he : orthogonalPartialSum a hp hq (n+1)=patch v (a n) ho₁ ho₂ := by
    apply ext
    change (orthogonalPartialSum a hp hq (n+1)).val=v.val+(a n).val
    rw [orthogonalPartialSum_val,show v.val=∑ i ∈ Finset.range n, (a i).val from
      orthogonalPartialSum_val a hp hq n,Finset.sum_range_succ]
  rw [he]
  exact v.le_patch (a n) ho₁ ho₂

end PartialIsometry
end

/-! Projection equivalence and subequivalence are witnessed by actual partial
isometries in the original algebra. No dimension or trace oracle is used. -/
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace PartialIsometry

/-- Link two ranges whose displayed partial isometries have the same source. -/
def rangeLink (v w : PartialIsometry M) (h : v.support=w.support) : PartialIsometry M :=
  w.compose v.adjoint (by rw [adjoint_target,h])

end PartialIsometry

/-! Finiteness excludes an infinite family of nonzero equivalent orthogonal
projections. The shift and both of its least supports are constructed. -/

/-! Finite comparison and cancellation with actual partial isometries.
No trace, dimension, or representation is assumed. -/
end Tracial

/-! Actual finite sums of orthogonal partial isometries and finite subsets of
equivalent partitions. The finite subset is arbitrary, without an index order. -/
open scoped BigOperators

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_Pinching
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Finite pinching in the actual ambient algebra. The squared L2 energy
is a sum of the energies of the mutually orthogonal compression blocks.
These identities do not postulate a local-quantizing partition. -/
section
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

namespace CornerPartition
variable {p : AlgebraProjection M} (Q : CornerPartition p)

theorem piece_le (i : Fin Q.size) : Q.piece i ≤ p := by
  change p.val * (Q.piece i).val = (Q.piece i).val
  rw [← Q.total, Finset.sum_mul]
  simpa only [(Q.piece i).property.isIdempotentElem.eq] using
    (Finset.sum_eq_single i (fun j _ hji => Q.orthogonal j i hji)
      (fun h => (h (Finset.mem_univ i)).elim))

end CornerPartition

/-! Actual compression energies and the energy lost by finite pinching.
No existence statement about small-energy partitions is assumed here. -/

namespace CornerPartition
variable {p : AlgebraProjection M} (Q : CornerPartition p)

/-! Partition refinement decreases the actual compression energy. The final
selection theorem retains membership in the prescribed subalgebra. -/

theorem pinch_corner_compression (x : M.toStarSubalgebra) :
    Q.pinch (p.val*x*p.val) = Q.pinch x := by
  unfold pinch
  apply Finset.sum_congr rfl
  intro i _
  have hl : p.val*(Q.piece i).val = (Q.piece i).val := Q.piece_le i
  have hr := projection_mul_of_le (Q.piece_le i)
  simp only [← mul_assoc, hr]
  simp only [mul_assoc, hl]

end CornerPartition

end

/-! Actual finite refinement of a corner partition by partitions of its blocks.
The dependent family of block sizes is flattened without changing any piece.
No small-energy partition is an input to these constructions. -/
section
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

namespace CornerPartition
variable {p : AlgebraProjection M}

variable (Q : CornerPartition p) (R : (i : Fin Q.size) → CornerPartition (Q.piece i))

theorem blockFamily_orthogonal (a b : (i : Fin Q.size) × Fin (R i).size) (hab : a ≠ b) :
    ((R a.1).piece a.2).val * ((R b.1).piece b.2).val = 0 := by
  by_cases h : a.1=b.1
  · obtain ⟨i,j⟩ := a
    obtain ⟨k,l⟩ := b
    dsimp at h ⊢
    subst k
    exact (R i).orthogonal j l (fun h => hab (by cases h; rfl))
  · exact orthogonal_subprojections (Q.orthogonal a.1 b.1 h)
      ((R a.1).piece_le a.2) ((R b.1).piece_le b.2)

theorem blockFamily_total :
    (∑ a : (i : Fin Q.size) × Fin (R i).size, ((R a.1).piece a.2).val) = p.val := by
  rw [Fintype.sum_sigma]
  simpa only [(R _).total] using Q.total

end CornerPartition

end

/-! Centered energy and the block scalar term that refinement preserves.
A blockwise descent applies to centered compressions, not to their full energy. -/

/-! Energy of compatible block refinements, including the scalar term.
The scalar term is necessary even when the original operator has trace zero. -/
open scoped BigOperators
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_SpectralTruncation
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Positivity of the tracial pairing does not require the two positive
operators to commute. These estimates will control spectral truncation. -/

/-! Upper spectral truncation of a self-adjoint operator. The truncation
remains in the original operator ball and has a positive discarded part. -/

/-! Spectral truncation forces a self-adjoint least-distance point in a
subalgebra ball to have norm at most the norm of the ambient test operator. -/

/-! Two-sided spectral clipping and trace-norm control. The auxiliary trace
is explicit; the trace-free construction supplies it on its actual closure. -/
open scoped CStarAlgebra
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance clippingCStar : CStarAlgebra M.toStarSubalgebra := {}

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_SpectralPinching
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.sequencesIsTopologicalRing _root_.OAI.Generator.predualAlgebraDualNormed _root_.OAI.Generator.vectorOrbitClosure_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Actual sign splitting inside a prescribed residual corner. -/
section
open scoped CStarAlgebra BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance cornerCutCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance cornerCutOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance cornerCutPreorder : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance cornerCutLE : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance cornerCutStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

/-- Functional calculus positive parts retain a given right support. -/
theorem positivePart_right_support (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x)
    (p : AlgebraProjection M) (hp : x*p.val=x) : x⁺*p.val=x⁺ := by
  have he : x⁺*(1-p.val)=x⁻*(1-p.val) := by
    apply sub_eq_zero.mp
    rw [← sub_mul,CFC.posPart_sub_negPart x hx,mul_sub,mul_one,hp,sub_self]
  have hz : star (x⁺*(1-p.val))*(x⁺*(1-p.val))=0 := by
    nth_rw 2 [he]
    rw [star_mul,star_sub,star_one,p.property.isSelfAdjoint.star_eq,
      (CFC.posPart_nonneg x).isSelfAdjoint.star_eq]
    calc (1-p.val)*x⁺*(x⁻*(1-p.val)) = (1-p.val)*(x⁺*x⁻)*(1-p.val) := by
           simp only [mul_assoc]
      _ = 0 := by rw [CFC.posPart_mul_negPart,mul_zero,zero_mul]
  have h := (CStarRing.star_mul_self_eq_zero_iff _).mp hz
  rw [mul_sub,mul_one,sub_eq_zero] at h
  exact h.symm

def cornerSpectralShift (p : AlgebraProjection M) (x : M.toStarSubalgebra) (t : ℝ) :
    M.toStarSubalgebra := p.val*x*p.val-(t : ℂ) • p.val

theorem cornerSpectralShift_selfAdjoint (p : AlgebraProjection M)
    (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) (t : ℝ) :
    IsSelfAdjoint (cornerSpectralShift p x t) := by
  change star (p.val*x*p.val-(t : ℂ) • p.val) = _
  simp only [cornerSpectralShift,star_sub,star_mul,star_smul,p.property.isSelfAdjoint.star_eq,hx.star_eq,
    Complex.star_def,Complex.conj_ofReal,mul_assoc]

theorem cornerSpectralShift_support (p : AlgebraProjection M) (x : M.toStarSubalgebra) (t : ℝ) :
    cornerSpectralShift p x t*p.val=cornerSpectralShift p x t := by
  simp only [cornerSpectralShift,sub_mul,smul_mul_assoc,mul_assoc,p.property.isIdempotentElem.eq]

end

/-! The constructed spectral splitting preserves the compressed operator.
This is distinct from using that splitting to reduce other operators' energy. -/

/-! Interval bounds propagated through constructed spectral corner splits. -/
section
open scoped CStarAlgebra
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance intervalCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance intervalOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance intervalPreorder : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance intervalLE : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance intervalStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

theorem compress_scalar_shift {p q : AlgebraProjection M} (hqp : q ≤ p)
    (x : M.toStarSubalgebra) (t : ℝ) :
    q.val*(p.val*x*p.val-(t : ℂ) • p.val)*q.val =
      q.val*x*q.val-(t : ℂ) • q.val := by
  have hl : p.val*q.val=q.val := hqp
  have hr := projection_mul_of_le hqp
  simp only [mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc]
  simp only [← mul_assoc,hr]
  simp only [mul_assoc,hl,q.property.isIdempotentElem.eq]

theorem lower_bound_compress {p q : AlgebraProjection M} (hqp : q ≤ p)
    (x : M.toStarSubalgebra) (t : ℝ)
    (h : 0 ≤ p.val*x*p.val-(t : ℂ) • p.val) :
    0 ≤ q.val*x*q.val-(t : ℂ) • q.val := by
  have hh := star_left_conjugate_nonneg h q.val
  rw [q.property.isSelfAdjoint.star_eq,compress_scalar_shift hqp] at hh
  exact hh

theorem upper_bound_compress {p q : AlgebraProjection M} (hqp : q ≤ p)
    (x : M.toStarSubalgebra) (t : ℝ)
    (h : p.val*x*p.val-(t : ℂ) • p.val ≤ 0) :
    q.val*x*q.val-(t : ℂ) • q.val ≤ 0 := by
  have hh := star_left_conjugate_nonneg (neg_nonneg.mpr h) q.val
  rw [q.property.isSelfAdjoint.star_eq,mul_neg,neg_mul,compress_scalar_shift hqp] at hh
  exact neg_nonneg.mp hh

structure SpectralInterval (x : M.toStarSubalgebra) where
  proj : AlgebraProjection M
  lo : ℝ
  hi : ℝ
  lower : 0 ≤ proj.val*x*proj.val-(lo : ℂ) • proj.val
  upper : proj.val*x*proj.val-(hi : ℂ) • proj.val ≤ 0

namespace SpectralInterval
variable {x : M.toStarSubalgebra} (I : SpectralInterval x) (hx : IsSelfAdjoint x)

def midpoint : ℝ := (I.lo+I.hi)/2

end SpectralInterval

end

/-! Finite dyadic trees of actual spectral interval cuts. -/
section
open scoped CStarAlgebra BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-! Finite spectral approximations constructed by successive sign cuts.
The approximation bound is proved from the leaf intervals. -/
local instance approximationCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance approximationOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance approximationPreorder : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance approximationLE : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance approximationStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

namespace SpectralInterval
variable {x : M.toStarSubalgebra} (I : SpectralInterval x) (hx : IsSelfAdjoint x)

theorem error_upper : I.proj.val*x*I.proj.val-(I.lo : ℂ) • I.proj.val ≤
    ((I.hi-I.lo : ℝ) : ℂ) • I.proj.val := by
  calc I.proj.val*x*I.proj.val-(I.lo : ℂ) • I.proj.val ≤
      (I.hi : ℂ) • I.proj.val-(I.lo : ℂ) • I.proj.val :=
        sub_le_sub_right (sub_nonpos.mp I.upper) _
    _ = _ := by rw [← sub_smul,Complex.ofReal_sub]

end SpectralInterval

/-- Start the construction with the actual operator norm bounds in any corner. -/
def initialSpectralInterval (p : AlgebraProjection M) (x : M.toStarSubalgebra)
    (hx : IsSelfAdjoint x) : SpectralInterval x := by
  let oneP : AlgebraProjection M := ⟨1,IsStarProjection.one _⟩
  have hp : p ≤ oneP := one_mul _
  have hs (r : ℝ) : algebraMap ℝ M.toStarSubalgebra r=(r : ℂ) • (1 : M.toStarSubalgebra) := by
    rw [Algebra.algebraMap_eq_smul_one,Complex.coe_smul]
  refine ⟨p,-‖x‖,‖x‖,?_,?_⟩
  · apply lower_bound_compress hp x (-‖x‖)
    have h := hx.neg_algebraMap_norm_le_self
    rw [hs] at h
    change 0 ≤ 1*x*1-((-‖x‖ : ℝ) : ℂ) • (1 : M.toStarSubalgebra)
    simpa only [one_mul,mul_one,Complex.ofReal_neg,neg_smul] using sub_nonneg.mpr h
  · apply upper_bound_compress hp x ‖x‖
    have h := hx.le_algebraMap_norm_self
    rw [hs] at h
    change 1*x*1-(‖x‖ : ℂ) • (1 : M.toStarSubalgebra) ≤ 0
    simpa only [one_mul,mul_one] using sub_nonpos.mpr h

end

/-! Constructed cuts preserve commutation with other operators. -/
section
open scoped CStarAlgebra
open UltrapowerBridge ContinuousLinearMap LinearMap
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance spectralCommutationCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance spectralCommutationOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance spectralCommutationStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

end

/-! Spectral interval partitions in the commutant of a prescribed operator. -/
open scoped BigOperators
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_SpectralApproximation
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Common finite refinements of two commuting corner partitions. -/
section
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace CornerPartition
variable {p : AlgebraProjection M} (Q R : CornerPartition p)
variable (hc : ∀ i j, Commute (Q.piece i).val (R.piece j).val)

def jointPiece (a : Fin Q.size × Fin R.size) : AlgebraProjection M :=
  ⟨(Q.piece a.1).val*(R.piece a.2).val,
    (Q.piece a.1).property.mul (R.piece a.2).property (hc a.1 a.2)⟩

theorem jointPiece_le_left (a : Fin Q.size × Fin R.size) : Q.jointPiece R hc a ≤ Q.piece a.1 := by
  change (Q.piece a.1).val*((Q.piece a.1).val*(R.piece a.2).val)=(Q.piece a.1).val*(R.piece a.2).val
  rw [← mul_assoc,(Q.piece a.1).property.isIdempotentElem.eq]

theorem jointPiece_le_right (a : Fin Q.size × Fin R.size) : Q.jointPiece R hc a ≤ R.piece a.2 := by
  change (R.piece a.2).val*((Q.piece a.1).val*(R.piece a.2).val)=(Q.piece a.1).val*(R.piece a.2).val
  rw [← mul_assoc,← (hc a.1 a.2).eq,mul_assoc,(R.piece a.2).property.isIdempotentElem.eq]

theorem jointPiece_orthogonal (a b : Fin Q.size × Fin R.size) (hab : a ≠ b) :
    (Q.jointPiece R hc a).val*(Q.jointPiece R hc b).val=0 := by
  by_cases h : a.1=b.1
  · have h₂ : a.2 ≠ b.2 := fun h₂ => hab (Prod.ext h h₂)
    exact orthogonal_subprojections (R.orthogonal a.2 b.2 h₂)
      (Q.jointPiece_le_right R hc a) (Q.jointPiece_le_right R hc b)
  · exact orthogonal_subprojections (Q.orthogonal a.1 b.1 h)
      (Q.jointPiece_le_left R hc a) (Q.jointPiece_le_left R hc b)

theorem jointPiece_total : (∑ a : Fin Q.size × Fin R.size, (Q.jointPiece R hc a).val)=p.val := by
  change (∑ a : Fin Q.size × Fin R.size, (Q.piece a.1).val*(R.piece a.2).val)=p.val
  rw [Fintype.sum_prod_type]
  simp only [← Finset.mul_sum,R.total,projection_mul_of_le (Q.piece_le _)]
  exact Q.total

/-- A spectral sum on Q is represented exactly on the common refinement. -/
theorem joint_sum_left (c : Fin Q.size → ℂ) :
    (∑ a : Fin Q.size × Fin R.size, c a.1 • (Q.jointPiece R hc a).val)=
      ∑ i, c i • (Q.piece i).val := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  change (∑ j, c i • ((Q.piece i).val*(R.piece j).val))=_
  rw [← Finset.smul_sum,← Finset.mul_sum,R.total,projection_mul_of_le (Q.piece_le i)]

theorem joint_sum_right (c : Fin R.size → ℂ) :
    (∑ a : Fin Q.size × Fin R.size, c a.2 • (Q.jointPiece R hc a).val)=
      ∑ j, c j • (R.piece j).val := by
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  change (∑ i, c j • ((Q.piece i).val*(R.piece j).val))=_
  rw [← Finset.smul_sum,← Finset.sum_mul,Q.total]
  have hleft : p.val*(R.piece j).val=(R.piece j).val := R.piece_le j
  rw [hleft]

end CornerPartition

/-! Simultaneous finite spectral approximation of two commuting self-adjoint
operators. The same actual partition is used for both. -/

end

/-! Finite spectral approximation for an actual normal operator. -/

/-! Transport constructed spectral partitions through an actual inclusion of
von Neumann algebras on the same Hilbert space. -/
section
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

def includedProjection (h : N ≤ M) (p : AlgebraProjection N) : AlgebraProjection M :=
  ⟨algebraInclusion h p.val,by
    constructor
    · change algebraInclusion h p.val * algebraInclusion h p.val = algebraInclusion h p.val
      rw [← map_mul,p.property.isIdempotentElem.eq]
    · change star (algebraInclusion h p.val)=algebraInclusion h p.val
      rw [← map_star,p.property.isSelfAdjoint.star_eq]⟩

end

/-! Finite simultaneous spectral approximation of any commuting self-adjoint
family, preserving a prior partition and the entire common commutant. -/

/-! Finite orthogonal families can be completed to unit partitions. Refining
blocks retains explicit disjoint index sets whose sums recover those blocks. -/
open scoped BigOperators
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_Subfactors
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! The actual von Neumann algebra of operators in N commuting with a finite
projection partition. Its double-commutant identity and completeness are
proved, so spectral approximation can be performed inside this algebra. -/
section
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}
namespace CornerPartition
variable {p : AlgebraProjection M} (Q : CornerPartition p)

def blockStarAlgebra (N : VonNeumannAlgebra H) : StarSubalgebra ℂ (H →L[ℂ] H) where
  carrier := {a | a ∈ N ∧ ∀ i, (Q.piece i).val.val*a=a*(Q.piece i).val.val}
  zero_mem' := ⟨N.zero_mem,by simp⟩
  one_mem' := ⟨N.one_mem,by simp⟩
  add_mem' ha hb := ⟨N.add_mem ha.1 hb.1,by
    intro i
    simp only [mul_add,add_mul,ha.2 i,hb.2 i]⟩
  mul_mem' ha hb := ⟨N.mul_mem ha.1 hb.1,by
    intro i
    rw [← mul_assoc,ha.2 i,mul_assoc,hb.2 i,← mul_assoc]⟩
  algebraMap_mem' c := ⟨N.toStarSubalgebra.algebraMap_mem c,by
    intro i
    exact (Algebra.commutes c _).symm⟩
  star_mem' ha := ⟨star_mem ha.1,by
    intro i
    have hs : star (Q.piece i).val.val=(Q.piece i).val.val :=
      congrArg Subtype.val (Q.piece i).property.isSelfAdjoint.star_eq
    simpa only [star_mul,hs] using (congrArg star (ha.2 i)).symm⟩

theorem blockStarAlgebra_bicommutant (N : VonNeumannAlgebra H) :
    Set.centralizer (Set.centralizer (Q.blockStarAlgebra N : Set (H →L[ℂ] H))) =
      (Q.blockStarAlgebra N : Set (H →L[ℂ] H)) := by
  apply Set.Subset.antisymm
  · intro a ha
    refine ⟨?_,?_⟩
    · change a ∈ (N : Set (H →L[ℂ] H))
      rw [← N.centralizer_centralizer]
      intro b hb
      exact ha b (fun c hc => hb c hc.1)
    · intro i
      apply ha
      intro b hb
      exact (hb.2 i).symm
  · intro a ha b hb
    exact (hb a ha).symm

def blockVonNeumann (N : VonNeumannAlgebra H) : VonNeumannAlgebra H where
  toStarSubalgebra := Q.blockStarAlgebra N
  centralizer_centralizer' := Q.blockStarAlgebra_bicommutant N

end CornerPartition

end

/-! Irreducibility passes to actual corners. Spectral approximation reduces
self-adjoint corner commutants to their projections; no corner-factor or
normalized-trace existence statement is assumed. -/

/-! The relative commutant of a finite block algebra consists of scalars on
each block. This statement is proved from coordinate irreducibility. -/

/-! Orthogonality to the prescribed subalgebra is stronger than global
centering. It is preserved by compressions and conjugations from that
subalgebra and removes every block scalar term exactly. -/

/-! A corner whose only projections are zero and its unit is scalar.
The proof constructs spectral approximations; minimality is not a scalar-corner axiom. -/

/-! Diffuseness descends to an irreducible von Neumann subalgebra of a
diffuse finite tracial algebra. Finiteness follows from the actual faithful trace. -/
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_Expectations
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! The orthogonal subalgebra representative of a self-adjoint ambient
operator is constructed, with its operator norm bound. -/

/-! A bounded trace-preserving subalgebra projection from self-adjoint least-distance points. Tracial orthogonality gives uniqueness and the bimodule identities. -/

/-! The constructed expectation preserves adjoints, is a bimodule map,
and is the orthogonal projection for the trace norm. -/

/-! Positivity of the constructed expectation. The negative spectral part
is an actual subalgebra test operator; tracial orthogonality eliminates it. -/

/-! The constructed expectation satisfies the Schwarz inequality and is
contractive in operator norm. -/
section
open scoped CStarAlgebra
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}
local instance expectationContractiveCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance expectationContractiveOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance expectationContractivePreorder : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance expectationContractiveLE : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE

end

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
-- module Solutions.OAIQ11_FG.FactorGeneration_FreeWords
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

namespace Generator

/-! Distinct nonidentity off-diagonal prefix ratios, distinguished by abelian exponent coordinates. Labels start at zero. -/

theorem exponentCoordinate_prefix (i n : ℕ) :
    Multiplicative.toAdd (exponentCoordinate i (freePrefix n)) =
      if i < n then 1 else 0 := by
  induction n with
  | zero => simp [freePrefix]
  | succ n ih =>
    rw [freePrefix, map_mul, toAdd_mul, ih]
    simp only [exponentCoordinate, FreeGroup.lift_apply_of, toAdd_ofAdd]
    split_ifs <;> omega

theorem freePrefix_injective : Function.Injective freePrefix := by
  intro k j h
  have hk := congrArg (fun g => Multiplicative.toAdd (exponentCoordinate k g)) h
  have hj := congrArg (fun g => Multiplicative.toAdd (exponentCoordinate j g)) h
  simp only [exponentCoordinate_prefix] at hk hj
  omega

theorem prefixRatio_eq_one_iff (k j : ℕ) : prefixRatio k j = 1 ↔ k = j := by
  rw [prefixRatio, mul_inv_eq_one]
  exact freePrefix_injective.eq_iff

/-! The exact multiplicity sum for prefix ratios, with labels g_(k+1) indexed by k : Fin n. -/
noncomputable section
open scoped BigOperators

attribute [local instance] OAI.Generator.instDecidableEqFreeGroupNat_solutions
theorem pairRatio_eq_one_iff {n : ℕ} (ij : Fin n × Fin n) :
    pairRatio ij = 1 ↔ ij.1 = ij.2 := by
  simp [pairRatio, prefixRatio_eq_one_iff, Fin.ext_iff]

/-- For n > 0 this is exactly the image of all ordered pairs in the source. -/
theorem ratioLabels_eq_image {n : ℕ} (hn : 0 < n) :
    ratioLabels n = (Finset.univ : Finset (Fin n × Fin n)).image pairRatio := by
  classical
  ext p
  simp only [ratioLabels, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro (rfl | ⟨ij, _, hp⟩)
    · exact ⟨(⟨0, hn⟩, ⟨0, hn⟩), (pairRatio_eq_one_iff _).mpr rfl⟩
    · exact ⟨ij, hp⟩
  · rintro ⟨ij, rfl⟩
    by_cases hij : ij.1 = ij.2
    · exact Or.inl ((pairRatio_eq_one_iff _).mpr hij)
    · exact Or.inr ⟨ij, by simp [hij], rfl⟩

end

/-! Ordered prefix products. The element h denotes the unitary exponential of a self-adjoint operator, not its logarithm. The final letter is unperturbed. -/

end Generator

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_FunctionalLimits
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.sequencesIsTopologicalRing _root_.OAI.Generator.predualAlgebraDualNormed _root_.OAI.Generator.vectorOrbitClosure_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator

/-! A functional bounded by a Hilbert-valued linear map factors through one
inner product. The proof uses the actual range, Hahn--Banach, and Riesz. -/

/-! A separable normed space has a countable family of bounded linear
functionals separating its points. All functionals are constructed by
Hahn--Banach at a countable dense family of vectors. -/

/-! Hermitian symmetrization and complex polarization for bounded functionals.
No tracial functional or finite factor is supplied to these algebraic lemmas. -/
open scoped CStarAlgebra
namespace Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance polarizationCStar : CStarAlgebra M.toStarSubalgebra := {}

def conjugateFunctional (φ : M.toStarSubalgebra →L[ℂ] ℂ) :
    M.toStarSubalgebra →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun x => star (φ (star x))
      map_add' := by intros; simp only [star_add,map_add]
      map_smul' := by intros; simp only [star_smul,map_smul,star_star,RingHom.id_apply] }
    ‖φ‖ (fun x => by
      change ‖star (φ (star x))‖ ≤ ‖φ‖*‖x‖
      simpa only [norm_star] using φ.le_opNorm (star x))

theorem conjugateFunctional_apply (φ : M.toStarSubalgebra →L[ℂ] ℂ)
    (x : M.toStarSubalgebra) : conjugateFunctional φ x=star (φ (star x)) := rfl

theorem conjugateFunctional_norm_le (φ : M.toStarSubalgebra →L[ℂ] ℂ) :
    ‖conjugateFunctional φ‖ ≤ ‖φ‖ := by
  apply (conjugateFunctional φ).opNorm_le_bound (norm_nonneg φ)
  intro x
  simpa only [conjugateFunctional_apply,norm_star] using φ.le_opNorm (star x)

def hermitianFunctional (φ : M.toStarSubalgebra →L[ℂ] ℂ) :
    M.toStarSubalgebra →L[ℂ] ℂ := (1/2 : ℂ) • (φ+conjugateFunctional φ)

theorem hermitianFunctional_apply (φ : M.toStarSubalgebra →L[ℂ] ℂ)
    (x : M.toStarSubalgebra) : hermitianFunctional φ x=(φ x+star (φ (star x)))/2 := by
  simp only [hermitianFunctional,smul_apply,add_apply,
    conjugateFunctional_apply,smul_eq_mul]
  ring

theorem hermitianFunctional_norm_le (φ : M.toStarSubalgebra →L[ℂ] ℂ) :
    ‖hermitianFunctional φ‖ ≤ ‖φ‖ := by
  change ‖(1/2 : ℂ) • (φ+conjugateFunctional φ)‖ ≤ _
  rw [norm_smul]
  have h := norm_add_le φ (conjugateFunctional φ)
  have h' := conjugateFunctional_norm_le φ
  norm_num
  linarith

theorem hermitianFunctional_star (φ : M.toStarSubalgebra →L[ℂ] ℂ)
    (x : M.toStarSubalgebra) : hermitianFunctional φ (star x)=star (hermitianFunctional φ x) := by
  simp only [hermitianFunctional_apply,star_star,star_div₀,star_add,star_ofNat]
  rw [add_comm]

theorem hermitianFunctional_selfAdjoint (φ : M.toStarSubalgebra →L[ℂ] ℂ)
    (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) :
    hermitianFunctional φ x=((φ x).re : ℂ) := by
  rw [hermitianFunctional_apply,hx.star_eq]
  exact (Complex.re_eq_add_conj _).symm

theorem hermitianFunctional_one (φ : M.toStarSubalgebra →L[ℂ] ℂ) (hφ : φ 1=1) :
    hermitianFunctional φ 1=1 := by
  rw [hermitianFunctional_selfAdjoint φ 1 (IsSelfAdjoint.one _),hφ]
  rfl

/-- Equality of complex quadratic values polarizes to the full trace identity. -/
theorem functional_trace_of_quadratic (φ : M.toStarSubalgebra →L[ℂ] ℂ)
    (hφ : ∀ x : M.toStarSubalgebra, φ (star x*x)=φ (x*star x))
    (x y : M.toStarSubalgebra) : φ (x*y)=φ (y*x) := by
  have hp := hφ (x+star y)
  have hi := hφ (x+Complex.I • star y)
  simp only [star_add,star_star,add_mul,mul_add,map_add] at hp
  simp only [star_add,star_smul,star_star,add_mul,mul_add,smul_mul_assoc,
    mul_smul_comm,map_add,map_smul,smul_eq_mul] at hi
  rw [hφ x,← hφ y] at hp hi
  simp only [show star Complex.I = -Complex.I from Complex.conj_I] at hi
  linear_combination (norm := ring_nf) -(1/2 : ℂ)*hp - (Complex.I/2)*hi
  simp only [Complex.I_sq]
  ring

theorem hermitianFunctional_trace (φ : M.toStarSubalgebra →L[ℂ] ℂ)
    (hφ : ∀ x : M.toStarSubalgebra, (φ (star x*x)).re=(φ (x*star x)).re)
    (x y : M.toStarSubalgebra) : hermitianFunctional φ (x*y)=hermitianFunctional φ (y*x) := by
  apply functional_trace_of_quadratic
  intro z
  rw [hermitianFunctional_selfAdjoint φ _ (IsSelfAdjoint.star_mul_self z),
    hermitianFunctional_selfAdjoint φ _ (IsSelfAdjoint.mul_star_self z),hφ z]

end Tracial

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_SpectralStates
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Additivity on commuting self-adjoint operators, proved using actual common
spectral refinements. The commutation hypothesis is essential to this proof. -/
open scoped BigOperators

/-! Positive spectral approximants, positivity of the constructed scalar, and
order preservation on commuting self-adjoint operators. -/
open scoped BigOperators CStarAlgebra
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance spectralValueCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance spectralValueOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance spectralValuePreorder : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance spectralValueLE : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance spectralValueStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

end

/-! A nonzero positive operator dominates a positive multiple of an actual
nonzero spectral projection. This proves faithfulness without linearity. -/
open scoped CStarAlgebra
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance spectralFaithfulCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance spectralFaithfulOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance spectralFaithfulPreorder : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance spectralFaithfulLE : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance spectralFaithfulStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

end

/-! Unitary conjugacy preserves projection dimension and its constructed
spectral extension. No trace identity is assumed. -/
open scoped BigOperators

/-! The constructed scalar agrees on x*x and xx*, by an actual unitary polar
decomposition. This is a quadratic identity, not unrestricted additivity. -/
open scoped CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance spectralSquareCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance spectralSquareOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance spectralSquareStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_LocalizedStates
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.sequencesIsTopologicalRing _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Localization of actual signed vector/dimension values. Fixed strict
sublevel sets, rather than a limiting strict inequality, supply Zorn bounds. -/
open Filter
open scoped Topology

/-! Tight multiplicative localization of an actual Hilbert vector functional
against the constructed projection dimension. The corner is constructed. -/

/-! Positive spectral approximants inside an actual projection corner, and
extension of localized projection inequalities to positive operators. -/
open scoped BigOperators CStarAlgebra
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance cornerValueCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance cornerValueOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance cornerValuePreorder_r2838f1_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance cornerValueLE : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance cornerValueStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

/-- The actual bounded complex-linear vector functional on the original algebra. -/
def vectorFunctional (ξ : H) : M.toStarSubalgebra →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun x => inner ℂ ξ (x.val ξ)
      map_add' := fun x y => inner_add_right _ _ _
      map_smul' := fun c x => inner_smul_right _ _ _ }
    (‖ξ‖^2) (fun x => by
      calc ‖inner ℂ ξ (x.val ξ)‖ ≤ ‖ξ‖*‖x.val ξ‖ := norm_inner_le_norm _ _
           _ ≤ ‖ξ‖*(‖x.val‖*‖ξ‖) := mul_le_mul_of_nonneg_left (x.val.le_opNorm ξ) (norm_nonneg _)
           _ = ‖ξ‖^2*‖x‖ := by change ‖ξ‖*(‖x‖*‖ξ‖)=_; ring)

theorem vectorFunctional_apply (ξ : H) (x : M.toStarSubalgebra) :
    vectorFunctional ξ x=inner ℂ ξ (x.val ξ) := rfl

theorem vectorFunctional_norm_le (ξ : H) : ‖vectorFunctional (M := M) ξ‖ ≤ ‖ξ‖^2 :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

end

/-! Projection localization yields actual positive-operator inequalities for
bounded linear functionals, and a nearly cyclic functional on the corner. -/
open scoped BigOperators CStarAlgebra
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance localizedCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance localizedOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance localizedPreorder_r2838f1_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance localizedLE : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance localizedStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

end

/-! An actual positive normalized vector functional with arbitrarily small
multiplicative failure of cyclicity on a nonzero corner. No trace is assumed. -/
open scoped CStarAlgebra
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance cornerStateCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance cornerStateOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance cornerStatePreorder_r2838f1_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance cornerStateLE : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance cornerStateStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

theorem vectorFunctional_star_mul_self (ξ : H) (x : M.toStarSubalgebra) :
    vectorFunctional ξ (star x*x)=(‖x.val ξ‖^2 : ℂ) := by
  change inner ℂ ξ (star x.val (x.val ξ))=_
  rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right,
    inner_self_eq_norm_sq_to_K]
  norm_cast

theorem vectorFunctional_positive (ξ : H) (x : M.toStarSubalgebra) (hx : 0 ≤ x) :
    0 ≤ (vectorFunctional ξ x).re := by
  let b := CFC.sqrt x
  have hb : star b=b := (CFC.sqrt_nonneg x).isSelfAdjoint.star_eq
  have he : star b*b=x := by rw [hb]; exact CFC.sqrt_mul_sqrt_self x hx
  rw [← he,vectorFunctional_star_mul_self]
  norm_cast
  positivity

end

/-! A full finite matrix partition can be rebased into every nonzero corner.
The legs are constructed partial isometries, not assumed matrix units. -/
open scoped BigOperators
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace EquivalentPartition
variable {p : AlgebraProjection M} {ι : Type*} [Fintype ι]

theorem base_ne_zero (E : EquivalentPartition p ι) (hp : p.val≠0) : E.base.val≠0 := by
  intro hz
  have hl (i : ι) : (E.leg i).val=0 := by
    have h := (E.leg i).mul_support
    rw [E.initial,hz,mul_zero] at h
    exact h.symm
  have ht := E.total
  have hz' (i : ι) : (E.leg i).target.val=0 := by
    change (E.leg i).val*star (E.leg i).val=0
    rw [hl,zero_mul]
  rw [show (∑ i, (E.leg i).target.val)=0 from Finset.sum_eq_zero (fun i _ => hz' i)] at ht
  exact hp ht.symm

end EquivalentPartition

end

/-! Extension of a vector functional through actual matrix-partition legs.
Finite coefficient identities transfer the corner quadratic inequality. -/
open scoped BigOperators CStarAlgebra
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace EquivalentPartition
variable {p : AlgebraProjection M} {ι : Type*} [Fintype ι]

/-- Matrix coefficient in the common initial corner. -/
def stateCoefficient (Q : EquivalentPartition p ι) (x : M.toStarSubalgebra) (i j : ι) :
    M.toStarSubalgebra := star (Q.leg i).val*x*(Q.leg j).val

theorem stateCoefficient_left (Q : EquivalentPartition p ι) (x : M.toStarSubalgebra) (i j : ι) :
    Q.base.val*Q.stateCoefficient x i j=Q.stateCoefficient x i j := by
  have hs : Q.base.val*star (Q.leg i).val=star (Q.leg i).val := by
    have h := congrArg star (Q.leg i).mul_support
    simpa only [star_mul,Q.initial,Q.base.property.isSelfAdjoint.star_eq] using h
  change Q.base.val*(star (Q.leg i).val*x*(Q.leg j).val)=_
  rw [← mul_assoc,← mul_assoc,hs]
  rfl

theorem stateCoefficient_right (Q : EquivalentPartition p ι) (x : M.toStarSubalgebra) (i j : ι) :
    Q.stateCoefficient x i j*Q.base.val=Q.stateCoefficient x i j := by
  change (star (Q.leg i).val*x*(Q.leg j).val)*Q.base.val=_
  rw [mul_assoc,← Q.initial j,(Q.leg j).mul_support]
  rfl

theorem stateCoefficient_star (Q : EquivalentPartition p ι) (x : M.toStarSubalgebra) (i j : ι) :
    star (Q.stateCoefficient x i j)=Q.stateCoefficient (star x) j i := by
  simp only [stateCoefficient,star_mul,star_star,mul_assoc]

theorem stateCoefficient_mul (Q : EquivalentPartition p ι) (hp : p.val=1)
    (x y : M.toStarSubalgebra) (i j : ι) :
    Q.stateCoefficient (x*y) i j=∑ k, Q.stateCoefficient x i k*Q.stateCoefficient y k j := by
  have he (k : ι) : Q.stateCoefficient x i k*Q.stateCoefficient y k j=
      star (Q.leg i).val*x*(Q.leg k).target.val*y*(Q.leg j).val := by
    simp only [stateCoefficient,PartialIsometry.target,mul_assoc]
  simp only [he]
  rw [← Finset.sum_mul,← Finset.sum_mul,← Finset.mul_sum,Q.total,hp,mul_one]
  simp only [stateCoefficient,mul_assoc]

/-- An actual finite sum of bounded vector functionals. -/
def matrixVectorFunctional (Q : EquivalentPartition p ι) (ξ : H) : M.toStarSubalgebra →L[ℂ] ℂ :=
  ∑ i, vectorFunctional ((Q.leg i).val.val ξ)

theorem matrixVectorFunctional_apply (Q : EquivalentPartition p ι) (ξ : H) (x : M.toStarSubalgebra) :
    Q.matrixVectorFunctional ξ x=∑ i, vectorFunctional ξ (Q.stateCoefficient x i i) := by
  change (∑ i, vectorFunctional ((Q.leg i).val.val ξ)) x=_
  rw [sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  change inner ℂ ((Q.leg i).val.val ξ) (x.val ((Q.leg i).val.val ξ))=
    inner ℂ ξ (star (Q.leg i).val.val (x.val ((Q.leg i).val.val ξ)))
  rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]

theorem matrixVectorFunctional_one (Q : EquivalentPartition p ι) (ξ : H) :
    Q.matrixVectorFunctional ξ 1=(∑ i, ‖(Q.leg i).val.val ξ‖^2 : ℝ) := by
  simp only [matrixVectorFunctional,sum_apply,vectorFunctional_apply]
  change (∑ i, inner ℂ ((Q.leg i).val.val ξ) ((Q.leg i).val.val ξ))=_
  simp only [inner_self_eq_norm_sq_to_K,Complex.ofReal_sum,Complex.ofReal_pow]
  norm_cast

theorem matrixVectorFunctional_norm_le (Q : EquivalentPartition p ι) (ξ : H) :
    ‖Q.matrixVectorFunctional ξ‖ ≤ ∑ i, ‖(Q.leg i).val.val ξ‖^2 := by
  change ‖∑ i, vectorFunctional (M := M) ((Q.leg i).val.val ξ)‖ ≤ _
  calc ‖∑ i, vectorFunctional (M := M) ((Q.leg i).val.val ξ)‖ ≤
      ∑ i, ‖vectorFunctional (M := M) ((Q.leg i).val.val ξ)‖ :=
        norm_sum_le Finset.univ (fun i : ι => vectorFunctional (M := M) ((Q.leg i).val.val ξ))
    _ ≤ ∑ i, ‖(Q.leg i).val.val ξ‖^2 :=
      Finset.sum_le_sum (fun i _ => vectorFunctional_norm_le (M := M) ((Q.leg i).val.val ξ))

theorem matrixVectorFunctional_nearly_cyclic (Q : EquivalentPartition p ι) (hp : p.val=1)
    (ξ : H) (ε : ℝ)
    (hcorner : ∀ x : M.toStarSubalgebra, Q.base.val*x=x → x*Q.base.val=x →
      (vectorFunctional ξ (star x*x)).re ≤ (1+ε)*(vectorFunctional ξ (x*star x)).re)
    (x : M.toStarSubalgebra) :
    (Q.matrixVectorFunctional ξ (star x*x)).re ≤
      (1+ε)*(Q.matrixVectorFunctional ξ (x*star x)).re := by
  have hl : (Q.matrixVectorFunctional ξ (star x*x)).re=
      ∑ i, ∑ j, (vectorFunctional ξ (star (Q.stateCoefficient x j i)*Q.stateCoefficient x j i)).re := by
    rw [Q.matrixVectorFunctional_apply,Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Q.stateCoefficient_mul hp,map_sum,Complex.re_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [Q.stateCoefficient_star]
  have hr : (Q.matrixVectorFunctional ξ (x*star x)).re=
      ∑ i, ∑ j, (vectorFunctional ξ (Q.stateCoefficient x j i*star (Q.stateCoefficient x j i))).re := by
    rw [Q.matrixVectorFunctional_apply,Complex.re_sum]
    simp_rw [Q.stateCoefficient_mul hp,map_sum,Complex.re_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    rw [Q.stateCoefficient_star]
  rw [hl,hr,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun j _ => hcorner (Q.stateCoefficient x j i)
    (Q.stateCoefficient_left x j i) (Q.stateCoefficient_right x j i))

end EquivalentPartition
end

/-! Globally defined positive unital linear functionals with arbitrarily small multiplicative quadratic trace error. -/
open scoped BigOperators CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance approxTraceCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance approxTraceOrder_r2838f1_1 : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance approxTracePreorder_r2838f1_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance approxTraceLE : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_LongWords
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator

/-! Factorial coefficient majorization in every homogeneous degree. -/

/-! The nonlinear remainder of the actual ordered convolution-operator
exponentials, evaluated at δ₁, without assumed degree estimates. -/

/-! Signed rows B_k and positive rows A_k with free basis indexed by prefix ratios in FreeGroup Nat. -/

/-! Transfer of the nonlinear estimate to an algebra with a continuous Hilbert
realization and orthonormal reduced-word images, without an independence hypothesis. -/

/-! The exact finite free basis and its injective realization in a countable free basis. -/
section
open scoped BigOperators
open Generator.FreeConvolution
local notation "G" => FreeGroup ℕ
local notation "F" => FreeGroup G

local instance instDecidableEqFreeGroupNat_solutions_3_r2838f1_1 : DecidableEq G := Classical.decEq _
attribute [local instance] OAI.Generator.instDecidableEqFreeGroupNat_solutions

def pairLabel {n : ℕ} (k j : Fin n) : PrefixLabel n :=
  ⟨pairRatio (k, j), by
    rw [ratioLabels_eq_image (Nat.zero_lt_of_lt k.isLt)]
    exact Finset.mem_image.mpr ⟨(k, j), Finset.mem_univ _, rfl⟩⟩

def prefixWordEmbedding (n : ℕ) : FreeGroup (PrefixLabel n) →* F :=
  FreeGroup.map Subtype.val

def prefixRingEmbedding (n : ℕ) : MonoidAlgebra ℂ (FreeGroup (PrefixLabel n)) →ₐ[ℂ]
    MonoidAlgebra ℂ F := MonoidAlgebra.mapDomainAlgHom ℂ ℂ (prefixWordEmbedding n)

@[simp] theorem prefixRingEmbedding_single (n : ℕ) (g : FreeGroup (PrefixLabel n)) (c : ℂ) :
    prefixRingEmbedding n (MonoidAlgebra.single g c) =
      MonoidAlgebra.single (prefixWordEmbedding n g) c := by
  exact MonoidAlgebra.mapDomain_single

/-- Literal B_k in the free group on the finite label set S. -/
def finitePerturbationRow {n : ℕ} (α : ℝ) (k : Fin n) :
    MonoidAlgebra ℂ (FreeGroup (PrefixLabel n)) :=
  (α / (2 * n)) • ∑ j : Fin n,
    (MonoidAlgebra.single (FreeGroup.of (pairLabel k j)) 1 -
     MonoidAlgebra.single ((FreeGroup.of (pairLabel k j))⁻¹) 1)

end

/-! Exact finite-basis version of the source's nonlinear estimate. Unlike the
ambient transport lemma, only reduced words in F_S occur in the hypothesis. -/
open scoped BigOperators InnerProductSpace

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_MonotoneTrace
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.sequencesIsTopologicalRing _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator

/-! Bounded positive monotone nets have actual least upper bounds in M.
Every displayed vector-trace bound passes to the constructed bound. -/
section
open Filter
open scoped Topology
namespace Tracial

/-! Positivity, order, and faithfulness of the actual vector trace, using
ambient operator order throughout. No identification with subtype spectral
order is needed. -/
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

theorem ambient_sqrt_mem (a : M.toStarSubalgebra) (ha : 0 ≤ a.val) :
    CFC.sqrt a.val ∈ M.toStarSubalgebra := by
  let : IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := base_norm_closed M
  rw [CFC.sqrt_eq_real_sqrt a.val ha, cfcₙ_eq_cfc Real.continuous_sqrt.continuousOn]
  exact cfc_mem (𝕜' := ℂ) Real.sqrt a.property

end Tracial

end

/-! Absolute values in the represented algebra, with ambient order bounds
and the actual trace two-norm. -/
namespace Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

def ambientAbsoluteValue (a : M.toStarSubalgebra) : M.toStarSubalgebra :=
  ⟨CFC.abs a.val, ambient_sqrt_mem (star a*a) (star_mul_self_nonneg a.val)⟩

end Tracial

/-! The bounded monotone transform a ↦ 1 - (1+a)⁻¹ of positive operators.
Its bounds prepare a construction of decreasing order majorants from small
trace tails. No tail majorant or predual continuity is asserted here. -/

/-! Decreasing positive order majorants for positive contractions with
summable trace. The finite-tail resolvents and their least upper bounds are
constructed in the actual algebra. -/
open Filter
open scoped Topology BigOperators
namespace Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

def algebraPositiveResolvent (a : M.toStarSubalgebra) : M.toStarSubalgebra := by
  let : IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := base_norm_closed M
  exact ⟨positiveResolvent a.val,
    cfc_mem (𝕜' := ℂ) (fun t : ℝ => 1 - (1+t)⁻¹) a.property⟩

end Tracial

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_NormalTrace
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! A genuine linear state with exact equality of real quadratic values,
constructed from the original finite factor predicates by scalar compactness. -/
section
open Filter
open scoped Topology CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance quadraticStateCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance quadraticStateOrder_r2838f1_1 : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance quadraticStatePreorder_r2838f1_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance quadraticStateLE : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE

end

/-! Construction of a tracial state on the original concrete finite diffuse factor without a supplied trace. -/
section
open scoped CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance tracialStateCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance tracialStateOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance tracialStatePreorder_r2838f1_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance tracialStateLE : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance tracialStateStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

end

/-! Every positive normalized tracial functional agrees with the dimension on
all projections. Lower and upper dyadic bounds use actual partial isometries. -/
section
open scoped BigOperators CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance stateDimensionCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance stateDimensionOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance stateDimensionPreorder_r2838f1_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance stateDimensionLE : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance stateDimensionStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

theorem algebraProjection_nonneg (p : AlgebraProjection M) : 0 ≤ p.val := by
  have h : star p.val*p.val=p.val := by
    rw [p.property.isSelfAdjoint.star_eq,p.property.isIdempotentElem.eq]
  rw [← h]
  exact star_mul_self_nonneg _

theorem tracialFunctional_equivalent (φ : M.toStarSubalgebra →L[ℂ] ℂ)
    (htrace : ∀ x y : M.toStarSubalgebra, φ (x*y)=φ (y*x))
    {p q : AlgebraProjection M} (h : p.Equivalent q) : φ p.val=φ q.val := by
  obtain ⟨v,hv,ht⟩ := h
  rw [← hv,← ht,← v.initial]
  exact htrace (star v.val) v.val

end

/-! Identification of the actual tracial state with the spectral dimension
value, and unrestricted additivity for noncommuting self-adjoint operators. -/
section
open scoped BigOperators CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance spectralAdditivityCStar : CStarAlgebra M.toStarSubalgebra := {}

end

/-! The constructed faithful normalized trace on the original algebra.
Projection-net continuity is proved explicitly; no general normality or
representation theorem is hidden in the definition. -/
section
open Filter
open scoped Topology CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance traceCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance traceOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance tracePreorder_r2838f1_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance traceLE : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance traceStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

end

/-! The constructed trace is dominated by a finite sum of concrete vector
functionals. The matrix partition is constructed inside the localized corner. -/
section
open scoped BigOperators CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance dominationCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance dominationOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance dominationPreorder_r2838f1_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance dominationLE : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance dominationStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

end

/-! Finite vector-functional representation and actual ultraweak continuity of
the constructed trace. No normality criterion is taken as an axiom. -/
open scoped BigOperators CStarAlgebra

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_RepresentedCorners
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed _root_.OAI.Generator.predualFunctionals_normed _root_.OAI.Generator.predualFunctionals_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! The actual corner on pH. Extension by zero identifies its operators with
supported ambient operators; weak closedness is proved by WOT continuity. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (p : AlgebraProjection M)

def cornerSpace : Submodule ℂ H where
  carrier := {x | p.val.val x=x}
  zero_mem' := by simp
  add_mem' hx hy := by simp_all
  smul_mem' c x hx := by simp_all

@[simp] theorem mem_cornerSpace (x : H) : x ∈ cornerSpace p ↔ p.val.val x=x := Iff.rfl

instance cornerSpace_complete : CompleteSpace (cornerSpace p) := by
  have hc : IsClosed (cornerSpace p : Set H) := isClosed_eq p.val.val.continuous continuous_id
  exact hc.completeSpace_coe

def cornerProject : H →L[ℂ] cornerSpace p :=
  p.val.val.codRestrict (cornerSpace p) (fun x => by
    change p.val.val (p.val.val x)=p.val.val x
    exact congrArg (fun a : M.toStarSubalgebra => a.val x) p.property.isIdempotentElem.eq)

@[simp] theorem cornerProject_coe (x : H) : (cornerProject p x).val=p.val.val x := rfl
@[simp] theorem cornerProject_subtype (x : cornerSpace p) : cornerProject p x.val=x :=
  Subtype.ext x.property

theorem cornerProject_inner (x : H) (y : cornerSpace p) :
    inner ℂ (cornerProject p x) y=inner ℂ x y.val := by
  change inner ℂ (p.val.val x) y.val=inner ℂ x y.val
  have hs : star p.val.val=p.val.val := congrArg Subtype.val p.property.isSelfAdjoint.star_eq
  rw [← hs,ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_left,y.property]

def cornerExtend (a : cornerSpace p →L[ℂ] cornerSpace p) : H →L[ℂ] H :=
  (cornerSpace p).subtypeL.comp (a.comp (cornerProject p))

@[simp] theorem cornerExtend_apply (a : cornerSpace p →L[ℂ] cornerSpace p) (x : H) :
    cornerExtend p a x=(a (cornerProject p x)).val := rfl

@[simp] theorem cornerExtend_zero : cornerExtend p 0=0 := by ext x; rfl
@[simp] theorem cornerExtend_add (a b : cornerSpace p →L[ℂ] cornerSpace p) :
    cornerExtend p (a+b)=cornerExtend p a+cornerExtend p b := by ext x; rfl
@[simp] theorem cornerExtend_smul (c : ℂ) (a : cornerSpace p →L[ℂ] cornerSpace p) :
    cornerExtend p (c • a)=c • cornerExtend p a := by ext x; rfl
@[simp] theorem cornerExtend_one : cornerExtend p 1=p.val.val := by ext x; rfl
@[simp] theorem cornerExtend_mul (a b : cornerSpace p →L[ℂ] cornerSpace p) :
    cornerExtend p (a*b)=cornerExtend p a*cornerExtend p b := by
  ext x
  simp only [mul_apply_eq_comp,cornerExtend_apply,cornerProject_subtype]

@[simp] theorem cornerExtend_star (a : cornerSpace p →L[ℂ] cornerSpace p) :
    cornerExtend p (star a)=star (cornerExtend p a) := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  rw [cornerExtend_apply,← cornerProject_inner,ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (a (cornerProject p y)) (cornerProject p x)=_
  rw [← inner_conj_symm,cornerProject_inner,inner_conj_symm]
  rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
  rfl

theorem cornerExtend_injective : Function.Injective (cornerExtend p) := by
  intro a b hab
  ext x
  have h := congrArg (fun T : H →L[ℂ] H => T x.val) hab
  simpa only [cornerExtend_apply,cornerProject_subtype] using h

@[simp] theorem cornerExtend_left (a : cornerSpace p →L[ℂ] cornerSpace p) :
    p.val.val*cornerExtend p a=cornerExtend p a := by
  ext x
  exact (a (cornerProject p x)).property

@[simp] theorem cornerExtend_right (a : cornerSpace p →L[ℂ] cornerSpace p) :
    cornerExtend p a*p.val.val=cornerExtend p a := by
  rw [← cornerExtend_one p,← cornerExtend_mul,mul_one]

def cornerStarAlgebra : StarSubalgebra ℂ (cornerSpace p →L[ℂ] cornerSpace p) where
  carrier := {a | cornerExtend p a ∈ M}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' ha hb := by simpa using M.add_mem ha hb
  mul_mem' ha hb := by simpa using M.mul_mem ha hb
  algebraMap_mem' c := by
    change cornerExtend p (c • 1) ∈ M
    simpa using M.toStarSubalgebra.smul_mem p.val.property c
  star_mem' ha := by simpa using star_mem ha

theorem cornerExtend_wot_continuous : Continuous (fun a : cornerSpace p →WOT[ℂ] cornerSpace p =>
    ContinuousLinearMapWOT.ofCLM (cornerExtend p a.toCLM)) := by
  apply ContinuousLinearMapWOT.continuous_iff.mpr
  intro x y
  simp only [ContinuousLinearMapWOT.ofCLM_apply,cornerExtend_apply,← cornerProject_inner]
  exact ContinuousLinearMapWOT.continuous_inner_apply continuous_id _ _

theorem cornerStarAlgebra_wotClosed : WOTClosed (cornerStarAlgebra p) :=
  (vonNeumann_wotClosed M).preimage (cornerExtend_wot_continuous p)

/-! Compression and extension are inverse on supported operators. -/

end

/-! The normalized faithful vector trace on the actual corner pH. -/

/-! Subcorner inclusion, inherited diffuseness/irreducibility, and L2 separability. -/

/-! Transport actual unit partitions on pH to ambient partitions of p. -/

/-! Actual centered pNp pinching partitions and local pieces. The corner,
normalized trace, structural properties, and separability are constructed. -/
open scoped BigOperators
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_TraceHilbert
attribute [-instance] _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! A separate type with the constructed trace inner product. Its norm is the
trace two-norm; the original concrete algebra retains its operator norm.
Lean's inner product is linear in the second argument. -/
section
open scoped ComplexConjugate CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

local instance traceHilbertCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance traceHilbertOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance traceHilbertStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

end

/-! The trace two-norm bound for left multiplication uses the original
operator norm and positivity of a concrete sandwich. -/

/-! Bounded left multiplication on the actual constructed trace Hilbert space.
All representation laws are proved on its dense algebraic subspace. -/

/-! Bounded right multiplication and its commutation with the constructed
left action. These supply separation on the actual double commutant. -/

/-! The actual double commutant of the new representation, with a constructed
faithful tracial vector. Equality with the original image is a later theorem. -/

/-! The constructed representation is WOT continuous on every original
operator-norm ball. This does not assert whole-carrier WOT continuity. -/
open scoped ComplexConjugate CStarAlgebra BigOperators

end Generator.Tracial

end

end OAI
end


