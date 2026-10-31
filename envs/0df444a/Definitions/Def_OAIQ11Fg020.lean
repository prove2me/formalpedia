-- Prove2me | Definitions.Def_OAIQ11Fg020
-- name    : OAIQ11Fg020
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T10:11:15.88195+00:00
-- url     : https://prove2.me/theorems/3679b645-7a0b-4433-85ef-5538a3695657
-- title:
--   Definitions bundle OAIQ11Fg020 of the split of OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 10 declarations of OpenAI's Lean: 5 definitions, 1 inductive type or structure and 4 theorems. The definitions and types are `OAI.Generator.Tracial.CoordinateHaarData`, `OAI.Generator.Tracial.HaarEndpoints`, `OAI.Generator.Tracial.boundedCompletedUnitary`, `OAI.Generator.Tracial.integerValueWord`, `OAI.Generator.Tracial.quotientOperatorAlgebra`, `OAI.Generator.Tracial.quotientOperatorNonAssocSemiring`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`FactorGeneration_CoordinateUnitaries`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/CoordinateUnitaries.lean), [`FactorGeneration_DyadicComparison`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/DyadicComparison.lean), [`FactorGeneration_HaarSequences`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/HaarSequences.lean), [`FactorGeneration_LaurentMoments`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/LaurentMoments.lean), [`FactorGeneration_QuotientRepresentation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/QuotientRepresentation.lean).
--
--   **Imports.** It imports the bundles `OAIQ11Fg012` and `OAIQ11Fg013` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ11Fg021` and `OAIQ11Fg046`; the statements `OAI.Generator.Tracial.HaarEndpoints.mul_left` and `OAI.Generator.Tracial.nonempty_coordinateHaarData`; the proofs of `OAI.Generator.Tracial.exactOrderedMoments_partial_limit`, `OAI.Generator.Tracial.exists_coordinate_reduced_unitary`, `OAI.Generator.Tracial.select_coordinate_with_bounds`, `OAI.Generator.Tracial.singlyGenerated_of_tracialRepresentation`, `OAI_Generator_Tracial_traceFreeSubalgebra_selfAdjoint_approximation` and `OAI.Generator.Tracial.tracial_remainder_of_coordinate_moments`.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ11Fg012
import Definitions.Def_OAIQ11Fg013

set_option maxHeartbeats 1000000

section
-- module Solutions.OAIQ11_FG.FactorGeneration_QuotientRepresentation
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
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

attribute [local instance] quotientL2AddCommMonoid quotientL2AddCommGroup

@[instance_reducible] def quotientOperatorNonAssocSemiring : NonUnitalNonAssocSemiring (L2 τ ω →L[ℂ] L2 τ ω) :=
  (inferInstance : NormedRing (L2 τ ω →L[ℂ] L2 τ ω)).toRing.toSemiring.toNonUnitalSemiring.toNonUnitalNonAssocSemiring

attribute [local instance] quotientOperatorSemiring quotientOperatorNonAssocSemiring

@[instance_reducible] def quotientOperatorAlgebra : Algebra ℂ (L2 τ ω →L[ℂ] L2 τ ω) :=
  ContinuousLinearMap.algebra

attribute [local instance] quotientOperatorAlgebra

theorem quotientOperatorSemitopology : IsSemitopologicalSemiring (L2 τ ω →L[ℂ] L2 τ ω) :=
  inferInstance

end

/-! Fixed-index selection for bounded coordinate representatives. -/
open Filter
open scoped Topology
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_LaurentMoments
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

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

/-! Extend exact moments by separate trace continuity in the two-norm. No
joint continuity of quotient multiplication, or operator-norm structure on Q,
is assumed. -/

def integerValueWord (v : unitary (Q τ ω)) (n : ℤ) : List (Q τ ω × ℤ) → Q τ ω → Q τ ω
  | [],b => (↑(v^n) : Q τ ω)*b
  | (d,m)::xs,b => (↑(v^n) : Q τ ω)*d*integerValueWord v m xs b

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
-- module Solutions.OAIQ11_FG.FactorGeneration_CoordinateUnitaries
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Complete each supported partial unitary by the identity on its orthogonal
complement. If the quotient support is one, the quotient value is unchanged. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

def boundedCompletedUnitary (u : ℕ → PartialUnitary M) : Bounded M :=
  boundedPartialUnitary u+(1-boundedPartialSupport u)

@[simp] theorem boundedCompletedUnitary_apply (u : ℕ → PartialUnitary M) (j : ℕ) :
    (boundedCompletedUnitary u).val j=(u j).completed := rfl

end

/-! Ordered independence with actual coordinate unitaries in the included
algebra, obtained by completing the constructed partial-unitary coordinates. -/

/-! Two coordinate-unitary witnesses produce the reduced-moment Haar precursor
while retaining actual unitary coordinates in the included algebra. -/

/-! Full integer endpoint moments and an actual included coordinate-unitary
Haar witness, before imposing an operator topology on generated algebras. -/
open UltrapowerBridge Filter

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_DyadicComparison
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
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

/-! Finite partitions with explicit equivalence witnesses and compatible binary
refinement. The common initial projection is halved once and its two pieces
are transported to every old piece, so all new pieces remain equivalent. -/

/-! Actual sums of countable orthogonal partial isometries, including least
initial/final support identities. No trace or countable-cofinality premise. -/

/-! Actual finite sums of orthogonal partial isometries and finite subsets of
equivalent partitions. The finite subset is arbitrary, without an index order. -/
open scoped BigOperators
namespace Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace EquivalentPartition
variable {p : AlgebraProjection M} {ι : Type*} [Fintype ι]

/-! Exact finite cardinal comparison of sums of equivalent nonzero projections.
Finiteness prevents a larger collection from embedding in a smaller one. -/

theorem subset_le_subset_iff (E : EquivalentPartition p ι) (hp : p.val≠0)
    (s t : Finset ι) : E.subset s ≤ E.subset t ↔ s ⊆ t := by
  constructor
  · intro h i hi
    by_contra hit
    have hh := (E.subset_le_iff s _).mp h i hi
    change (E.subset t).val*(E.leg i).target.val=(E.leg i).target.val at hh
    rw [E.subset_mul_piece_of_not_mem t i hit] at hh
    exact E.target_ne_zero hp i hh.symm
  · exact E.subset_mono

theorem subset_subequivalent_of_card_le (E : EquivalentPartition p ι)
    (s t : Finset ι) (h : s.card ≤ t.card) : (E.subset s).Subequivalent (E.subset t) := by
  obtain ⟨u,hut,hu⟩ := Finset.exists_subset_card_eq h
  exact AlgebraProjection.subequivalent_trans
    (E.subset_equivalent_of_card_eq s u hu.symm).subequivalent
    (AlgebraProjection.subequivalent_of_le (E.subset_mono hut))

end EquivalentPartition
end Tracial

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_HaarSequences
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! One constructed Haar extension retains endpoint moments, represented
norm-closed freeness, and an actual unitary sequence in the included algebra. -/
section
attribute [local instance] quotientL2AddCommMonoid quotientL2AddCommGroup
  quotientOperatorSemiring quotientOperatorNonAssocSemiring quotientOperatorAlgebra
  quotientOperatorSemitopology
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

/-- Full endpoint formula; the internal factors alone must be centered. -/
def HaarEndpoints (D : Subalgebra ℂ (Q τ ω)) (t : unitary (Q τ ω)) : Prop :=
  ∀ c ∈ D,∀ d ∈ D,∀ n : ℤ,n ≠ 0 → ∀ xs : List (Q τ ω × ℤ),
    (∀ z ∈ xs,z.1 ∈ D ∧ quotientTrace τ ω z.1=0 ∧ z.2 ≠ 0) →
    quotientTrace τ ω (c*integerValueWord τ ω t n xs d)=0

structure CoordinateHaarData (hNM : N ≤ M) (D : Subalgebra ℂ (Q τ ω)) where
  t : unitary (Q τ ω)
  coordinates : Bounded N
  unitary_coordinates : ∀ j,coordinates.val j ∈ unitary N.toStarSubalgebra
  represents : quotientInclusion τ hNM (ω : Filter ℕ)
    (quotientMap (restrictedTrace τ hNM) (ω : Filter ℕ) coordinates)=(t : Q τ ω)
  endpoints : HaarEndpoints τ ω D t

end

/-! Scalar expansion of same-sign gaps. Opposite-sign gaps must be centered,
so deleting a scalar gap can never cancel an entire power. -/

/-! Absorption of base-algebra unitaries, with signed scalar gap expansions. -/

/-! Successive Haar choices in algebraic star subalgebras of the tracial quotient, with freeness retained in their represented operator-norm closures. -/

/-! Free variables and prefixes with Haar endpoint properties of W and y=zW*. Coordinates are retained in the sequence data. -/
open UltrapowerBridge Filter

end Generator.Tracial

end

end OAI
end


