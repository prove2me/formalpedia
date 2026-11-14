-- Prove2me | Definitions.Def_Q260K062
-- name    : Q260K062
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T06:27:15.579931+00:00
-- url     : https://prove2.me/theorems/90bf5f0d-dea0-4c5c-9dec-2a83e9229d86
-- title:
--   Definitions bundle Q260K062 of the split of OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 35 declarations of OpenAI's Lean: 14 definitions, 1 instance and 20 theorems. The definitions and types are `OAI.KadisonKastler.centralVectorSpace`, `OAI.KadisonKastler.concreteDerivation`, `OAI.KadisonKastler.concreteDiagonalSequence`, `OAI.KadisonKastler.concreteDiagonalSequenceUnitary`, `OAI.KadisonKastler.concreteDiagonalUnitary`, `OAI.KadisonKastler.expectedTrace`, `OAI.KadisonKastler.matrixEntrySequence`, `OAI.KadisonKastler.matrixLiftConcreteOrder`, `OAI.KadisonKastler.matrixLiftUnitaryAt`, `OAI.KadisonKastler.matrixSequenceOfEntries`, `OAI.KadisonKastler.matrixSequenceQuotient`, `OAI.KadisonKastler.sequenceMatrixEquiv`, `OAI.KadisonKastler.sequenceMatrixHom`, `OAI.KadisonKastler.sequenceScalarHom`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`KadisonKastler_CentralVectorSpace`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/CentralVectorSpace.lean), [`KadisonKastler_CommonRightAction`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/CommonRightAction.lean), [`KadisonKastler_CompleteAmplification`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/CompleteAmplification.lean), [`KadisonKastler_ExpectedCentralizer`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/ExpectedCentralizer.lean), [`KadisonKastler_MatrixCommutantLifts`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/MatrixCommutantLifts.lean), [`KadisonKastler_MatrixLiftConjugation`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/MatrixLiftConjugation.lean), [`KadisonKastler_MatrixSequences`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/MatrixSequences.lean), [`KadisonKastler_OperatorFieldValues`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/OperatorFieldValues.lean), [`KadisonKastler_OperatorMeanStar`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/OperatorMeanStar.lean).
--
--   **Imports.** It imports the bundle `Q260K061` of this split.
--
--   **Imported by** (directly, in this split): the bundle `Q260K027`.
-- source:
--   OpenAI, Universal strong Kadison–Kastler stability (result family 289), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 289; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-strong-Kadison-Kastler-stability-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Module.LinearMap.Rat
import Mathlib.Algebra.Module.Rat
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.Sublists
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Composition
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Sym.Card
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.LinearAlgebra.Countable
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Basic
import Mathlib.Tactic
import Mathlib.Tactic.DeriveCountable
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Topology.Bases
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.ThickenedIndicator
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_Q260K061

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CommonRightAction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Common right actions in a cyclic representation

Two operators in the same commutant are equal if they agree on the cyclic
vector. Equality of the right actions obtained this way makes the product
of the two tracial conjugations commute with both module actions.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable [CompleteSpace H]

/-- The standard tracial conjugation turns a left multiplier into the
right multiplier by its adjoint, first on the dense algebra vectors. -/
theorem conjugationOperator_algebraVector
    (M : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hJ : ∀ x : Algebra M, J (x.val Ω) = (star x).val Ω)
    (a x : Algebra M) :
    conjugationOperator J a.val (x.val Ω) = (x * star a).val Ω := by
  rw [conjugationOperator_apply, hJ]
  change J ((a * star x).val Ω) = (x * star a).val Ω
  rw [hJ, star_mul, star_star]

/-- In a cyclic standard tracial representation the conjugated left
multiplier lies in the commutant of the whole algebra. -/
theorem conjugationOperator_mem_commutant
    (M : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hJ : ∀ x : Algebra M, J (x.val Ω) = (star x).val Ω)
    (hcyclic : DenseRange (fun x : Algebra M => x.val Ω)) (a : Algebra M) :
    conjugationOperator J a.val ∈ M.commutant := by
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro b hb
  let bM : Algebra M := ⟨b, hb⟩
  have he : (fun ξ => (b * conjugationOperator J a.val) ξ) =
      fun ξ => (conjugationOperator J a.val * b) ξ :=
    hcyclic.equalizer (b * conjugationOperator J a.val).continuous
      (conjugationOperator J a.val * b).continuous (by
        funext x
        change b (conjugationOperator J a.val (x.val Ω)) =
          conjugationOperator J a.val (b (x.val Ω))
        rw [conjugationOperator_algebraVector M J Ω hJ]
        change (bM * (x * star a)).val Ω =
          conjugationOperator J a.val ((bM * x).val Ω)
        rw [conjugationOperator_algebraVector M J Ω hJ, mul_assoc])
  ext ξ
  exact congrFun he ξ

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CentralVectorSpace
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.conjugationOperator_one _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.matrixAlgebraEquiv_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.spatialTransportEquiv_apply _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Central vectors and the relative commutant

The central-vector space used in Haagerup's construction is a closed
complex subspace. A one-dimensional central-vector space detects an
irreducible inclusion once its generating vector is separating.
-/

namespace KadisonKastler

open UltrapowerBridge

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {N P M : VonNeumannAlgebra H}

/-- Vectors on which left and conjugate-right multiplication agree. -/
def centralVectorSpace (N : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H) : Submodule ℂ H where
  carrier := {ξ | ∀ a : Algebra N, a.val ξ = conjugationOperator J (star a).val ξ}
  zero_mem' := by simp only [Set.mem_ofPred_eq, map_zero, implies_true]
  add_mem' := by
    intro ξ η hξ hη a
    simp only [map_add, hξ a, hη a]
  smul_mem' := by
    intro c ξ hξ a
    simp only [map_smul, hξ a]

@[simp] theorem mem_centralVectorSpace (J : H ≃ₗᵢ⋆[ℂ] H) (ξ : H) :
    ξ ∈ centralVectorSpace N J ↔
      ∀ a : Algebra N, a.val ξ = conjugationOperator J (star a).val ξ := Iff.rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixSequences
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.TraceQuotientMap.comapEquiv_quotient _root_.OAI.KadisonKastler.boundedSequenceMapHom_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.realTrace_apply _root_.OAI.KadisonKastler.traceCenter_apply _root_.OAI.KadisonKastler.traceStateRepresentation_vector _root_.OAI.KadisonKastler.traceStateRight_vector _root_.OAI.KadisonKastler.traceStateVector_sub _root_.OAI.KadisonKastler.traceTwoNorm_eq_zero_iff _root_.OAI.KadisonKastler.traceTwoNorm_neg _root_.OAI.KadisonKastler.traceTwoNorm_zero _root_.OAI.KadisonKastler.trace_traceCenter _root_.OAI.KadisonKastler.tracialQuotientLinear_map _root_.OAI.KadisonKastler.tracialSequenceContinuous_apply _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.tracialSequenceValue_one _root_.OAI.KadisonKastler.varyingSequenceMap_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Finite matrices and bounded sequences

Entrywise evaluation identifies bounded sequences of finite matrices
with finite matrices of bounded sequences. Applying a tracial quotient
to the entries gives the normalized matrix trace formula.
-/

namespace KadisonKastler

open Filter
open scoped Topology BigOperators BoundedContinuousFunction

noncomputable section

variable {B C ι : Type*} [CStarAlgebra B] [CStarAlgebra C] [Fintype ι] [DecidableEq ι]

local instance matrixSequencesOrder_r581bdb_1 : PartialOrder B := CStarAlgebra.spectralOrder _
local instance matrixSequencesStarOrder_r581bdb_1 : StarOrderedRing B := CStarAlgebra.spectralOrderedRing _
attribute [local instance] OAI.KadisonKastler.matrixSequencesTargetOrder
attribute [local instance] OAI.KadisonKastler.matrixSequencesTargetStarOrder
local instance matrixSequencesBoundedOrder_r581bdb_1 : PartialOrder (BoundedSequence B) := CStarAlgebra.spectralOrder _
local instance matrixSequencesBoundedStarOrder_r581bdb_1 : StarOrderedRing (BoundedSequence B) :=
  CStarAlgebra.spectralOrderedRing _
/-- A matrix entry of a bounded sequence is itself a bounded sequence. -/
def matrixEntrySequence (x : BoundedSequence (CStarMatrix ι ι B)) (i j : ι) :
    BoundedSequence B :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun k => x k i j)
    continuous_of_discreteTopology ‖x‖
    (fun k => CStarMatrix.norm_entry_le_norm.trans (x.norm_coe_le_norm k))

@[simp]
theorem matrixEntrySequence_apply (x : BoundedSequence (CStarMatrix ι ι B))
    (i j : ι) (k : ℕ) : matrixEntrySequence x i j k = x k i j := rfl

/-- Assemble finitely many bounded entries into a bounded matrix sequence. -/
def matrixSequenceOfEntries (x : CStarMatrix ι ι (BoundedSequence B)) :
    BoundedSequence (CStarMatrix ι ι B) where
  toFun k := CStarMatrix.ofMatrix fun i j => x i j k
  continuous_toFun := continuous_of_discreteTopology
  map_bounded' := by
    apply Metric.isBounded_range_iff.mp
    change Bornology.IsBounded (Set.range (fun k : ℕ => fun i j : ι => x i j k))
    apply Bornology.forall_isBounded_image_eval_iff.mp
    intro i
    rw [← Set.range_comp]
    apply Bornology.forall_isBounded_image_eval_iff.mp
    intro j
    simpa only [← Set.range_comp, Function.comp_def] using (x i j).isBounded_range

@[simp]
theorem matrixSequenceOfEntries_apply (x : CStarMatrix ι ι (BoundedSequence B))
    (k : ℕ) (i j : ι) : matrixSequenceOfEntries x k i j = x i j k := rfl

omit [DecidableEq ι] in
theorem boundedSequence_sum_apply (x : ι → BoundedSequence B) (k : ℕ) :
    (∑ i, x i) k = ∑ i, x i k :=
  map_sum (boundedSequenceEval k) x Finset.univ

/-- Entrywise transposition of the sequence index and matrix indices. -/
def sequenceMatrixHom : BoundedSequence (CStarMatrix ι ι B) →⋆ₐ[ℂ]
    CStarMatrix ι ι (BoundedSequence B) where
  toFun x := CStarMatrix.ofMatrix fun i j => matrixEntrySequence x i j
  map_one' := by
    ext i j k
    change (1 : CStarMatrix ι ι B) i j = (1 : CStarMatrix ι ι (BoundedSequence B)) i j k
    rw [CStarMatrix.one_apply, CStarMatrix.one_apply]
    split_ifs <;> rfl
  map_mul' x y := by
    ext i j k
    change (x k * y k) i j =
      (∑ l, matrixEntrySequence x i l * matrixEntrySequence y l j) k
    rw [boundedSequence_sum_apply]
    simp only [BoundedContinuousFunction.mul_apply, matrixEntrySequence_apply, CStarMatrix.mul_apply]
  map_zero' := by
    ext i j k
    rfl
  map_add' x y := by
    ext i j k
    rfl
  commutes' z := by
    ext i j k
    change (algebraMap ℂ (CStarMatrix ι ι B) z) i j =
      (algebraMap ℂ (CStarMatrix ι ι (BoundedSequence B)) z) i j k
    rw [CStarMatrix.algebraMap_apply, CStarMatrix.algebraMap_apply]
    split_ifs <;> rfl
  map_star' x := by
    ext i j k
    rfl

@[simp]
theorem sequenceMatrixHom_apply (x : BoundedSequence (CStarMatrix ι ι B))
    (i j : ι) (k : ℕ) : sequenceMatrixHom x i j k = x k i j := rfl

theorem sequenceMatrixHom_bijective : Function.Bijective (sequenceMatrixHom (ι := ι) (B := B)) := by
  constructor
  · intro x y h
    ext k i j
    exact congrArg (fun z : CStarMatrix ι ι (BoundedSequence B) => z i j k) h
  · intro x
    refine ⟨matrixSequenceOfEntries x, ?_⟩
    ext i j k
    rfl

/-- The actual star-algebra equivalence between the two bounded-sequence constructions. -/
def sequenceMatrixEquiv : BoundedSequence (CStarMatrix ι ι B) ≃⋆ₐ[ℂ]
    CStarMatrix ι ι (BoundedSequence B) :=
  StarAlgEquiv.ofBijective sequenceMatrixHom sequenceMatrixHom_bijective

@[simp]
theorem sequenceMatrixEquiv_apply (x : BoundedSequence (CStarMatrix ι ι B))
    (i j : ι) (k : ℕ) : sequenceMatrixEquiv x i j k = x k i j := rfl

variable [Nonempty ι] {τ : FaithfulTracialState B} {σ : FaithfulTracialState C}
  {ω : Ultrafilter ℕ}

/-- Apply a tracial quotient to each finite matrix entry. -/
def matrixSequenceQuotient (Q : TraceQuotientMap τ σ ω) :
    BoundedSequence (CStarMatrix ι ι B) →⋆ₐ[ℂ] CStarMatrix ι ι C :=
  (coefficientMatrixMap Q.quotient).comp sequenceMatrixHom

omit [Nonempty ι] in
@[simp]
theorem matrixSequenceQuotient_apply (Q : TraceQuotientMap τ σ ω)
    (x : BoundedSequence (CStarMatrix ι ι B)) (i j : ι) :
    matrixSequenceQuotient Q x i j = Q.quotient (matrixEntrySequence x i j) := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixCommutantLifts
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.TraceQuotientMap.comapEquiv_quotient _root_.OAI.KadisonKastler.boundedSequenceMapHom_apply _root_.OAI.KadisonKastler.matrixScalarHom_mul_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mul_matrixScalarHom_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Unitary lifts respecting the scalar matrix commutant

The matrix ultrapower equivalence identifies the scalar-matrix commutant
with the diagonal coefficient quotient. The proved coordinatewise finite
polar construction then gives a lift which is diagonal at every coordinate.
-/

namespace KadisonKastler

noncomputable section

variable {A B C ι : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]
  [Fintype ι] [DecidableEq ι]

local instance diagonalLiftSourceOrder_r581bdb_1 : PartialOrder A := CStarAlgebra.spectralOrder _
local instance diagonalLiftSourceStarOrder_r581bdb_1 : StarOrderedRing A := CStarAlgebra.spectralOrderedRing _
local instance diagonalLiftSequenceOrder_r581bdb_1 : PartialOrder (BoundedSequence A) :=
  CStarAlgebra.spectralOrder _
local instance diagonalLiftSequenceStarOrder_r581bdb_1 : StarOrderedRing (BoundedSequence A) :=
  CStarAlgebra.spectralOrderedRing _
attribute [local instance] OAI.KadisonKastler.diagonalLiftTargetOrder
attribute [local instance] OAI.KadisonKastler.diagonalLiftTargetStarOrder
local instance diagonalLiftComplexOrder_r581bdb_1 : PartialOrder ℂ := CStarAlgebra.spectralOrder _
local instance diagonalLiftComplexStarOrder_r581bdb_1 : StarOrderedRing ℂ := CStarAlgebra.spectralOrderedRing _
/-- Diagonal amplification of a bounded sequence, as an actual star homomorphism. -/
def sequenceScalarHom : BoundedSequence A →⋆ₐ[ℂ] BoundedSequence (CStarMatrix ι ι A) :=
  (sequenceMatrixEquiv (B := A) (ι := ι)).symm.toStarAlgHom.comp matrixScalarHom

@[simp]
theorem sequenceScalarHom_apply (x : BoundedSequence A) (k : ℕ) (i j : ι) :
    sequenceScalarHom x k i j = if i = j then x k else 0 := by
  have h := congrArg (fun m : CStarMatrix ι ι (BoundedSequence A) => m i j k)
    ((sequenceMatrixEquiv (B := A) (ι := ι)).apply_symm_apply (matrixScalarHom x))
  change (sequenceMatrixEquiv.symm (matrixScalarHom x)) k i j = _
  change (sequenceMatrixEquiv.symm (matrixScalarHom x)) k i j =
    (if i = j then x else 0) k at h
  by_cases hij : i = j
  · simpa only [hij, ite_true, if_true] using h
  · simp only [hij, ite_false, if_false] at h ⊢
    exact h.trans (map_zero (boundedSequenceEval (B := A) k))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixLiftConjugation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealPartialOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.Generator.Tracial.cyclicCoefficient_apply _root_.OAI.Generator.Tracial.cyclicPredualEvaluation_apply _root_.OAI.Generator.Tracial.traceFreeCopy_inner _root_.OAI.Generator.Tracial.traceFreeInclusion_inner _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.finiteDiagonalMap_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.spatialTransportEquiv_apply _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply _root_.OAI.KadisonSimilarity.predualRestriction_apply _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Conjugating finite-matrix lifts by a diagonal unitary

Conjugating the inner matrix units changes only the finite matrix algebra
in which a representative lies. Both the concrete embedding and its
bounded sequence version respect this conjugation exactly.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {A B ι κ : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

section Concrete

local instance matrixLiftScalarOrder_r581bdb_1 : PartialOrder ℂ := CStarAlgebra.spectralOrder _
local instance matrixLiftScalarStarOrder_r581bdb_1 : StarOrderedRing ℂ := CStarAlgebra.spectralOrderedRing _
local instance matrixLiftSourceOrder_r581bdb_1 : PartialOrder A := CStarAlgebra.spectralOrder _
local instance matrixLiftSourceStarOrder_r581bdb_1 : StarOrderedRing A := CStarAlgebra.spectralOrderedRing _
local instance matrixLiftTargetOrder_r581bdb_1 : PartialOrder B := CStarAlgebra.spectralOrder _
local instance matrixLiftTargetStarOrder_r581bdb_1 : StarOrderedRing B := CStarAlgebra.spectralOrderedRing _
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {n j : ℕ} [NeZero n]

local instance matrixLiftConcreteOrder : PartialOrder (Algebra M) := CStarAlgebra.spectralOrder _
local instance matrixLiftConcreteStarOrder : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _

/-- The concrete diagonal amplification of an inner unitary. -/
def concreteDiagonalUnitary (z : unitary (Algebra M)) :
    unitary (Algebra (matrixVonNeumann (ι := Fin n) M)) :=
  Unitary.map (StarMonoidHom.ofClass
    ((matrixAlgebraHom M).comp (matrixScalarHom (ι := Fin n)))) z

omit [NeZero n] in
@[simp]
theorem concreteDiagonalUnitary_coe (z : unitary (Algebra M)) :
    (concreteDiagonalUnitary (n := n) z : Algebra (matrixVonNeumann (ι := Fin n) M)) =
      matrixAlgebraHom M (matrixScalarHom (z : Algebra M)) := rfl

/-- The coordinate unitary of a bounded unitary sequence. -/
def matrixLiftUnitaryAt (z : unitary (BoundedSequence (Algebra M))) (k : ℕ) :
    unitary (Algebra M) :=
  Unitary.map (StarMonoidHom.ofClass (boundedSequenceEval (B := Algebra M) k)) z

@[simp]
theorem matrixLiftUnitaryAt_coe (z : unitary (BoundedSequence (Algebra M))) (k : ℕ) :
    (matrixLiftUnitaryAt z k : Algebra M) = (z : BoundedSequence (Algebra M)) k := rfl

/-- The diagonal bounded sequence, represented on the concrete Hilbert matrix space. -/
def concreteDiagonalSequence (z : BoundedSequence (Algebra M)) :
    BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M)) :=
  boundedSequenceMapHom (matrixAlgebraHom (ι := Fin n) M) (sequenceScalarHom (ι := Fin n) z)

omit [NeZero n] in
@[simp]
theorem concreteDiagonalSequence_apply (z : BoundedSequence (Algebra M)) (k : ℕ) :
    concreteDiagonalSequence (n := n) z k = matrixAlgebraHom M (matrixScalarHom (z k)) := by
  rw [concreteDiagonalSequence, boundedSequenceMapHom_apply]
  congr 1
  apply CStarMatrix.ext
  intro i j
  exact sequenceScalarHom_apply z k i j

/-- The diagonal sequence remains an actual unitary before passing to a quotient. -/
def concreteDiagonalSequenceUnitary (z : unitary (BoundedSequence (Algebra M))) :
    unitary (BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M))) :=
  Unitary.map (StarMonoidHom.ofClass
    ((boundedSequenceMapHom (matrixAlgebraHom (ι := Fin n) M)).comp
      (sequenceScalarHom (ι := Fin n)))) z

omit [NeZero n] in
@[simp]
theorem concreteDiagonalSequenceUnitary_coe
    (z : unitary (BoundedSequence (Algebra M))) :
    (concreteDiagonalSequenceUnitary (n := n) z :
        BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M))) =
      concreteDiagonalSequence (n := n) (z : BoundedSequence (Algebra M)) := rfl

end Concrete

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CompleteAmplification
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.Generator.Tracial.cyclicCoefficient_apply _root_.OAI.Generator.Tracial.cyclicPredualEvaluation_apply _root_.OAI.Generator.Tracial.traceFreeCopy_inner _root_.OAI.Generator.Tracial.traceFreeInclusion_inner _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.spatialTransportEquiv_apply _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply _root_.OAI.KadisonSimilarity.predualRestriction_apply _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The uniform completely bounded derivation estimate for II₁ factors -/

namespace KadisonKastler

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

local instance completeAmplificationSourceOrder_r581bdb_1 : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance completeAmplificationSourceStarOrder_r581bdb_1 : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _
local instance completeAmplificationOperatorOrder_r581bdb_1 : PartialOrder (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrder _
local instance completeAmplificationOperatorStarOrder_r581bdb_1 : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _
/-- The bounded derivation on the original represented algebra. -/
def concreteDerivation (M : VonNeumannAlgebra H) (h : H →L[ℂ] H) :
    Algebra M →L[ℂ] (H →L[ℂ] H) :=
  ((innerDerivation h).comp M.toStarSubalgebra.subtype.toLinearMap).mkContinuous
    (2 * ‖h‖) (fun x => by
      change ‖h * x.val - x.val * h‖ ≤ 2 * ‖h‖ * ‖x‖
      calc
        _ ≤ ‖h * x.val‖ + ‖x.val * h‖ := norm_sub_le _ _
        _ ≤ ‖h‖ * ‖x‖ + ‖x‖ * ‖h‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
        _ = 2 * ‖h‖ * ‖x‖ := by ring)

@[simp]
theorem concreteDerivation_apply (M : VonNeumannAlgebra H) (h : H →L[ℂ] H)
    (x : Algebra M) : concreteDerivation M h x = h * x.val - x.val * h := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ExpectedCentralizer
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.TraceQuotientMap.comapEquiv_quotient _root_.OAI.KadisonKastler.matrixSequenceQuotient_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.traceStateRepresentation_vector _root_.OAI.KadisonKastler.traceStateRight_vector _root_.OAI.KadisonKastler.traceStateVector_sub _root_.OAI.KadisonKastler.tracialQuotientLinear_map _root_.OAI.KadisonKastler.tracialSequenceContinuous_apply _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.tracialSequenceValue_one _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A finite expected subfactor gives a centralizing functional

The trace in this construction is only on the finite subfactor. Composing
it with a bimodular conditional expectation gives a functional on the
ambient algebra which centralizes that subfactor. No traciality of the
ambient algebra is asserted or used.
-/

namespace KadisonKastler

noncomputable section

section Abstract

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

/-- The functional obtained by composing a finite trace and an expectation. -/
def expectedTrace (τ : FaithfulTracialState A) (E : B →L[ℂ] A) : B →L[ℂ] ℂ :=
  τ.toContinuousLinearMap.comp E

@[simp]
theorem expectedTrace_apply (τ : FaithfulTracialState A) (E : B →L[ℂ] A) (x : B) :
    expectedTrace τ E x = τ.toLinearMap (E x) := rfl

end Abstract

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_OperatorMeanStar
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Adjoint preservation of operator-field averaging -/

namespace KadisonKastler

open MeasureTheory Filter
open scoped BoundedContinuousFunction

noncomputable section

variable {D H : Type*} [MeasurableSpace D] {μ : Measure D}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace WeakOperatorField

theorem coefficient_star (T : WeakOperatorField (H := H) μ) (ξ η : H) :
    coefficient (star T) ξ η = star (coefficient T η ξ) := by
  rw [← quotient_representative T, ← map_star, coefficient_quotient,
    coefficient_quotient, WeakOperatorRepresentative.coefficient_star]

end WeakOperatorField

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_OperatorFieldValues
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Von Neumann algebra values of measurable operator fields

Commuting with constant operators in the commutant is a norm-closed
condition. Countably many strong-operator tests identify this condition
with pointwise membership outside one null set.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Pointwise BoundedContinuousFunction

noncomputable section

variable {D H : Type*} [MeasurableSpace D] {μ : Measure D}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem isClosed_operatorFieldAlgebra (M : VonNeumannAlgebra H) :
    IsClosed (operatorFieldAlgebra (μ := μ) M : Set (WeakOperatorField (H := H) μ)) :=
  Set.isClosed_centralizer _

instance operatorFieldAlgebraCStar (M : VonNeumannAlgebra H) :
    CStarAlgebra (operatorFieldAlgebra (μ := μ) M) :=
  StarSubalgebra.cstarAlgebra _ (h_closed := isClosed_operatorFieldAlgebra M)

end

end KadisonKastler

end OAI
end


