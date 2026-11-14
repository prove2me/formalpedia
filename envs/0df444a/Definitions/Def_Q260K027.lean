-- Prove2me | Definitions.Def_Q260K027
-- name    : Q260K027
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T06:37:09.529123+00:00
-- url     : https://prove2.me/theorems/36e7a6f7-08cd-404c-9224-7a55197737ac
-- title:
--   Definitions bundle Q260K027 of the split of OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 21 declarations of OpenAI's Lean: 5 definitions and 16 theorems. The definitions and types are `OAI.KadisonKastler.operatorFieldFamilyInclusion`, `OAI.KadisonKastler.tracialHilbertConjugation`, `OAI.KadisonKastler.tracialStarIsometry`, `OAI.KadisonKastler.typeICyclicHom`, `OAI.KadisonKastler.typeICyclicOperator`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`KadisonKastler_CommonRightAction`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/CommonRightAction.lean), [`KadisonKastler_ConcreteTraceHilbert`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/ConcreteTraceHilbert.lean), [`KadisonKastler_RestrictedOperatorMean`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/RestrictedOperatorMean.lean), [`KadisonKastler_TracialHilbertConjugation`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/TracialHilbertConjugation.lean), [`KadisonKastler_TypeICyclicRepresentation`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/TypeICyclicRepresentation.lean).
--
--   **Imports.** It imports the bundle `Q260K062` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q260K030` and `Q260K063`; the statements `OAI.KadisonKastler.FiniteVectorTrace.traceSeparable`, `OAI.KadisonKastler.ScalarBoundaryMean.exists_measurable_cocycle_near_representation`, `OAI.KadisonKastler.ScalarBoundaryMean.operatorFieldFamilyInclusion_translate`, `OAI.KadisonKastler.TypeIIIFactor.exists_centered_selfAdjoint_implementer`, `OAI.KadisonKastler.TypeIIIFactor.exists_countable_amplification_unitary`, `OAI.KadisonKastler.TypeIIIFactor.exists_isometry_onto_projection`, `OAI.KadisonKastler.TypeIIIFactor.exists_nonzero_projection_partition`, `OAI.KadisonKastler.exists_selfAdjoint_split_of_finite_commutant_corner`, `OAI_KadisonKastler_exists_selfAdjoint_split_of_typeIII_commutant_of_projection_countability`, `OAI.KadisonKastler.exists_unique_cyclic_factor_of_mem_orbitClosure`, `OAI.KadisonKastler.exists_universal_modular_rows`, `OAI.KadisonKastler.finiteCoefficientConjugations_of_separable_bound`, `OAI.KadisonKastler.hasOperatorValues_of_mem`, `OAI_KadisonKastler_publishedFieldTomiyama`, `OAI_KadisonKastler_publishedFiniteType`, `OAI.KadisonKastler.publishedProperInfiniteProjectionCopies` and `OAI.KadisonKastler.publishedTypeIIIProjectionComparison`; the proofs of `OAI.KadisonKastler.TypeIIIFactor.exists_isometry_onto_projection`, `OAI.KadisonKastler.factor_of_extreme_signed_derivation_extension`, `OAI.KadisonKastler.finiteCoefficientConjugations_of_separable_bound`, `OAI.KadisonKastler.hasOperatorValues_of_mem`, `OAI_KadisonKastler_publishedFieldTomiyama`, `OAI.KadisonKastler.publishedTypeIIIProjectionComparison` and `OAI.KadisonKastler.relative_irreducibility_of_near_increasing_matrices`.
-- source:
--   OpenAI, Universal strong Kadison–Kastler stability (result family 289), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 289; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-strong-Kadison-Kastler-stability-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.List
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
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
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
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Real.Sqrt
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
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.RingTheory.Congruence.Hom
import Mathlib.RingTheory.TwoSidedIdeal.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Lattice
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
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_Q260K062

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ConcreteTraceHilbert
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The canonical separable trace Hilbert realization

The trace completion provides the Hilbert-space norm estimates used
by boundary comparison.
-/

namespace KadisonKastler

open TopologicalSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

theorem traceHilbert_factor (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (x : Algebra M) (hx : ∀ y : Algebra M, y * x = x * y) :
    ∃ c : ℂ, x = c • (1 : Algebra M) := by
  obtain ⟨c, hc⟩ := hM.factor x hx
  exact ⟨c, by simpa only [Algebra.algebraMap_eq_smul_one] using hc⟩

theorem traceHilbert_nonzero (hM : Generator.IsII1Factor M.toStarSubalgebra) :
    (1 : Algebra M) ≠ 0 := by
  intro h
  exact hM.nonzero (congrArg Subtype.val h).symm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CommonRightAction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

/-- Concrete commutant members agreeing on a cyclic vector are equal. -/
theorem operator_eq_of_mem_commutant_of_eq_on_cyclicVector
    (M : VonNeumannAlgebra H) (Ω : H)
    (hcyclic : DenseRange (fun x : Algebra M => x.val Ω))
    (q r : H →L[ℂ] H) (hq : q ∈ M.commutant) (hr : r ∈ M.commutant)
    (hΩ : q Ω = r Ω) : q = r := by
  apply operator_eq_of_commute_of_eq_on_cyclicVector
    (fun x : Algebra M => x.val) Ω hcyclic q r
  · intro x
    exact (VonNeumannAlgebra.mem_commutant_iff.mp hq x.val x.property).symm
  · intro x
    exact (VonNeumannAlgebra.mem_commutant_iff.mp hr x.val x.property).symm
  · exact hΩ

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RestrictedOperatorMean
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.WeakOperatorRepresentative.evalHom_apply _root_.OAI.KadisonKastler.WeakOperatorRepresentative.eval_kernelProjection _root_.OAI.KadisonKastler.WeakOperatorRepresentative.eval_positiveKernelProjection _root_.OAI.KadisonKastler.WeakOperatorRepresentative.topElement_val _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.tracialQuotientLinear_map _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Equivariant averaging within a von Neumann algebra

The constant-commutant description of the field algebra is invariant under
boundary pullback. Restricting the constructed mean therefore keeps both
the cocycle and its correction in the prescribed von Neumann algebra.
-/

namespace KadisonKastler

open MeasureTheory
open scoped BoundedContinuousFunction

noncomputable section

variable {G D H : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace D] {μ : Measure D} [IsFiniteMeasure μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

variable (M : VonNeumannAlgebra H)

/-- The inclusion of bounded M-valued field families into all field families. -/
def operatorFieldFamilyInclusion : (G →ᵇ operatorFieldAlgebra (μ := μ) M) →⋆ₐ[ℂ]
    (G →ᵇ WeakOperatorField (H := H) μ) where
  toFun F := BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun g => (F g : WeakOperatorField (H := H) μ)) ‖F‖ (fun g => F.norm_coe_le_norm g)
  map_one' := by ext g; rfl
  map_mul' F K := by ext g; rfl
  map_zero' := by ext g; rfl
  map_add' F K := by ext g; rfl
  commutes' c := by ext g; rfl
  map_star' F := by ext g; rfl

omit [Group G] [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace H] in
@[simp]
theorem operatorFieldFamilyInclusion_apply (F : G →ᵇ operatorFieldAlgebra (μ := μ) M)
    (g : G) : operatorFieldFamilyInclusion (G := G) (D := D) (H := H) (μ := μ) M F g = (F g : WeakOperatorField (H := H) μ) := rfl

omit [Group G] [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace H] in
theorem norm_operatorFieldFamilyInclusion_le (F : G →ᵇ operatorFieldAlgebra (μ := μ) M) :
    ‖operatorFieldFamilyInclusion (G := G) (D := D) (H := H) (μ := μ) M F‖ ≤ ‖F‖ :=
  (BoundedContinuousFunction.norm_le (norm_nonneg F)).mpr (fun g => F.norm_coe_le_norm g)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TracialHilbertConjugation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.TraceQuotientMap.comapEquiv_quotient _root_.OAI.KadisonKastler.expectedTrace_apply _root_.OAI.KadisonKastler.matrixSequenceQuotient_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.traceStateRepresentation_vector _root_.OAI.KadisonKastler.traceStateRight_vector _root_.OAI.KadisonKastler.traceStateVector_sub _root_.OAI.KadisonKastler.tracialQuotientLinear_map _root_.OAI.KadisonKastler.tracialSequenceContinuous_apply _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.tracialSequenceValue_one _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Constructing tracial conjugation on a Hilbert completion

The adjoint operation is an isometry for a faithful trace. Its extension
to any dense trace-Hilbert realization is an involutive conjugate-linear
isometry; no standard-form conjugation is postulated.
-/

namespace KadisonKastler

noncomputable section

variable {A E : Type*} [CStarAlgebra A]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The adjoint map extends isometrically to the trace Hilbert space. -/
def tracialStarIsometry (τ : FaithfulTracialState A) (J : A →ₗ[ℂ] E)
    (hJ : ∀ a, ‖J a‖ = traceTwoNorm τ a) (hdense : DenseRange J) : E →ₗᵢ⋆[ℂ] E :=
  (starVectorMap J).extendOfIsometry hdense (fun a => by
    change ‖J (star a)‖ = ‖J a‖
    rw [hJ, hJ, traceTwoNorm_star])

@[simp]
theorem tracialStarIsometry_embedding (τ : FaithfulTracialState A) (J : A →ₗ[ℂ] E)
    (hJ : ∀ a, ‖J a‖ = traceTwoNorm τ a) (hdense : DenseRange J) (a : A) :
    tracialStarIsometry τ J hJ hdense (J a) = J (star a) :=
  LinearMap.extendOfIsometry_eq _ _ _ a

theorem tracialStarIsometry_involutive (τ : FaithfulTracialState A) (J : A →ₗ[ℂ] E)
    (hJ : ∀ a, ‖J a‖ = traceTwoNorm τ a) (hdense : DenseRange J) :
    Function.Involutive (tracialStarIsometry τ J hJ hdense) := by
  let T := tracialStarIsometry τ J hJ hdense
  have hT (a : A) : T (J a) = J (star a) := tracialStarIsometry_embedding τ J hJ hdense a
  have he : (fun ξ => T (T ξ)) = fun ξ => ξ :=
    hdense.equalizer (T.continuous.comp T.continuous) continuous_id (by
      funext a
      change T (T (J a)) = J a
      rw [hT, hT, star_star])
  exact fun ξ => congrFun he ξ

/-- The constructed involution, packaged as a conjugate-linear isometric
equivalence. -/
def tracialHilbertConjugation (τ : FaithfulTracialState A) (J : A →ₗ[ℂ] E)
    (hJ : ∀ a, ‖J a‖ = traceTwoNorm τ a) (hdense : DenseRange J) : E ≃ₗᵢ⋆[ℂ] E :=
  LinearIsometryEquiv.ofSurjective (tracialStarIsometry τ J hJ hdense)
    (tracialStarIsometry_involutive τ J hJ hdense).surjective

@[simp]
theorem tracialHilbertConjugation_embedding (τ : FaithfulTracialState A) (J : A →ₗ[ℂ] E)
    (hJ : ∀ a, ‖J a‖ = traceTwoNorm τ a) (hdense : DenseRange J) (a : A) :
    tracialHilbertConjugation τ J hJ hdense (J a) = J (star a) :=
  tracialStarIsometry_embedding τ J hJ hdense a

theorem tracialHilbertConjugation_involutive (τ : FaithfulTracialState A) (J : A →ₗ[ℂ] E)
    (hJ : ∀ a, ‖J a‖ = traceTwoNorm τ a) (hdense : DenseRange J) :
    Function.Involutive (tracialHilbertConjugation τ J hJ hdense) :=
  tracialStarIsometry_involutive τ J hJ hdense

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TypeICyclicRepresentation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.concreteDerivation_apply _root_.OAI.KadisonKastler.concreteDiagonalSequenceUnitary_coe _root_.OAI.KadisonKastler.concreteDiagonalSequence_apply _root_.OAI.KadisonKastler.concreteDiagonalUnitary_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.matrixAlgebraEquiv_apply _root_.OAI.KadisonKastler.matrixLiftUnitaryAt_coe _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The irreducible cyclic representation afforded by a minimal projection

A nonzero vector in a minimal projection determines a faithful irreducible
cyclic representation of a factor.  The construction uses the actual closed
orbit in the given Hilbert space; no classification theorem is invoked.
-/

namespace KadisonKastler

open Generator Generator.Tracial
open scoped Topology

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

def typeICyclicOperator (ξ : H) (a : Algebra M) :
    typeICyclicSpace M ξ →L[ℂ] typeICyclicSpace M ξ :=
  a.val.restrict (fun _ hy => vectorOrbitClosure_invariant _ _ a hy)

@[simp] theorem typeICyclicOperator_apply (ξ : H) (a : Algebra M)
    (y : typeICyclicSpace M ξ) : (typeICyclicOperator ξ a y : H) = a.val y := rfl

theorem typeICyclicOperator_star (ξ : H) (a : Algebra M) :
    typeICyclicOperator ξ (star a) = star (typeICyclicOperator ξ a) := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  change inner ℂ y.val (star a.val x.val) =
    inner ℂ y (star (typeICyclicOperator ξ a) x)
  simp only [ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]
  rfl

def typeICyclicHom (ξ : H) : Algebra M →⋆ₐ[ℂ]
    (typeICyclicSpace M ξ →L[ℂ] typeICyclicSpace M ξ) where
  toFun := typeICyclicOperator ξ
  map_one' := by ext y; rfl
  map_mul' _ _ := by ext y; rfl
  map_zero' := by ext y; rfl
  map_add' _ _ := by ext y; rfl
  commutes' _ := by ext y; rfl
  map_star' := typeICyclicOperator_star ξ

@[simp] theorem typeICyclicHom_apply (ξ : H) (a : Algebra M)
    (y : typeICyclicSpace M ξ) : (typeICyclicHom ξ a y : H) = a.val y := rfl

theorem typeICyclicHom_cyclic (ξ : H) :
    DenseRange (fun a : Algebra M => typeICyclicHom ξ a (typeICyclicVector M ξ)) := by
  intro y
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨z, ⟨a, rfl⟩, ha⟩ := Metric.mem_closure_iff.mp y.property ε hε
  exact ⟨typeICyclicHom ξ a (typeICyclicVector M ξ), ⟨a, rfl⟩, ha⟩

theorem minimal_corner_scalar (p : AlgebraProjection M)
    (hp : IsMinimalProjectionIn M p) (a : Algebra M)
    (hl : p.val * a = a) (hr : a * p.val = a) : ∃ z : ℂ, a = z • p.val := by
  apply corner_scalar_of_projections p _ a hl hr
  intro q hq
  exact (hp.2 q hq).imp id (congrArg Subtype.val)

/-- The minimal projection restricts to a rank-one projection. -/
theorem typeICyclicProjection_range (p : AlgebraProjection M)
    (hp : IsMinimalProjectionIn M p) (ξ : H) (hpξ : p.val.val ξ = ξ)
    (y : typeICyclicSpace M ξ) :
    ∃ z : ℂ, typeICyclicHom ξ p.val y = z • typeICyclicVector M ξ := by
  let L : Submodule ℂ H := Submodule.span ℂ {ξ}
  have hclosed : IsClosed (L : Set H) := L.closed_of_finiteDimensional
  have hK : typeICyclicSpace M ξ ≤ L.comap p.val.val.toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · rintro y ⟨a, rfl⟩
      obtain ⟨z, hz⟩ := minimal_corner_scalar p hp (p.val * a * p.val)
        (by rw [← mul_assoc, ← mul_assoc, p.property.isIdempotentElem.eq])
        (by rw [mul_assoc, p.property.isIdempotentElem.eq])
      have he := congrArg (fun b : Algebra M => b.val ξ) hz
      change p.val.val (a.val (p.val.val ξ)) = z • p.val.val ξ at he
      rw [hpξ] at he
      change p.val.val (a.val ξ) ∈ L
      rw [he]
      exact L.smul_mem z (Submodule.subset_span (Set.mem_singleton ξ))
    · exact hclosed.preimage p.val.val.continuous
  obtain ⟨z, hz⟩ := Submodule.mem_span_singleton.mp (hK y.property)
  exact ⟨z, Subtype.ext hz.symm⟩

/-- Every operator commuting with this cyclic representation is scalar. -/
theorem typeICyclicHom_commutant (p : AlgebraProjection M)
    (hp : IsMinimalProjectionIn M p) (ξ : H) (hpξ : p.val.val ξ = ξ)
    (T : typeICyclicSpace M ξ →L[ℂ] typeICyclicSpace M ξ)
    (hT : ∀ a : Algebra M, typeICyclicHom ξ a * T = T * typeICyclicHom ξ a) :
    ∃ z : ℂ, T = z • 1 := by
  have hfix : typeICyclicHom ξ p.val (T (typeICyclicVector M ξ)) =
      T (typeICyclicVector M ξ) := by
    have he := congrArg (fun S : typeICyclicSpace M ξ →L[ℂ] typeICyclicSpace M ξ =>
      S (typeICyclicVector M ξ)) (hT p.val)
    have hpfix : typeICyclicHom ξ p.val (typeICyclicVector M ξ) =
        typeICyclicVector M ξ := Subtype.ext hpξ
    change typeICyclicHom ξ p.val (T (typeICyclicVector M ξ)) =
      T (typeICyclicHom ξ p.val (typeICyclicVector M ξ)) at he
    rwa [hpfix] at he
  obtain ⟨z, hz⟩ := typeICyclicProjection_range p hp ξ hpξ (T (typeICyclicVector M ξ))
  rw [hfix] at hz
  refine ⟨z, ?_⟩
  apply DFunLike.ext'
  apply (typeICyclicHom_cyclic (M := M) ξ).equalizer T.continuous (z • (1 :
    typeICyclicSpace M ξ →L[ℂ] typeICyclicSpace M ξ)).continuous
  funext a
  have he := congrArg (fun S : typeICyclicSpace M ξ →L[ℂ] typeICyclicSpace M ξ =>
    S (typeICyclicVector M ξ)) (hT a)
  change typeICyclicHom ξ a (T (typeICyclicVector M ξ)) =
    T (typeICyclicHom ξ a (typeICyclicVector M ξ)) at he
  change T (typeICyclicHom ξ a (typeICyclicVector M ξ)) =
    z • typeICyclicHom ξ a (typeICyclicVector M ξ)
  rw [← he, hz, map_smul]

end

end KadisonKastler

end OAI
end


