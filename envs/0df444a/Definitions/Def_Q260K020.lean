-- Prove2me | Definitions.Def_Q260K020
-- name    : Q260K020
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T04:51:17.306936+00:00
-- url     : https://prove2.me/theorems/2e703666-27c0-46d3-a896-668321bb9974
-- title:
--   Definitions bundle Q260K020 of the split of OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 56 declarations of OpenAI's Lean: 24 definitions, 4 instances and 28 theorems. The definitions and types are `OAI.KadisonKastler.WeakOperatorRepresentative.projectionField`, `OAI.KadisonKastler.finiteProjectionSum`, `OAI.KadisonKastler.fullSourceFamily`, `OAI.KadisonKastler.matrixOrbitSample`, `OAI.KadisonKastler.nestedMeanRowsL`, `OAI.KadisonKastler.nestedScalarMeanL`, `OAI.KadisonKastler.operatorCochainContraction`, `OAI.KadisonKastler.projectionComplement`, `OAI.KadisonKastler.quotientStrongUnitBallTests`, `OAI.KadisonKastler.randomWalkSplit`, `OAI.KadisonKastler.reducingRepresentation`, `OAI.KadisonKastler.regularActionMultiplier`, `OAI.KadisonKastler.regularCoreConjugation`, `OAI.KadisonKastler.regularCoreMonomial`, `OAI.KadisonKastler.rowAdjointVector`, `OAI.KadisonKastler.sourceFamily`, `OAI.KadisonKastler.spatialMatrixCoefficient`, `OAI.KadisonKastler.spatialMatrixHom`, `OAI.KadisonKastler.spectralPartitionNonzeroIndex`, `OAI.KadisonKastler.twoStateSourceEmbedding`, `OAI.KadisonKastler.twoStateSummandProjection`, `OAI.KadisonKastler.twoStateTargetEmbedding`, `OAI.KadisonKastler.varyingSequenceHom`, `OAI.KadisonKastler.varyingUnitarySequence`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `KadisonKastler_FaithfulReducingNorm`, `KadisonKastler_FiniteMatrixFreeModel`, `KadisonKastler_HardyEvaluationConstruction`, `KadisonKastler_HardyKernelShift`, `KadisonKastler_InfiniteFactorProperInfiniteness`, `KadisonKastler_MatrixOrbitSampleLaw`, `KadisonKastler_NestedMeanEquivariance`, `KadisonKastler_NestedScalarMeans`, `KadisonKastler_NormalTwoStateGeometry`, `KadisonKastler_NormalTwoStateSupports`, `KadisonKastler_NormalizerTopology`, `KadisonKastler_OperatorCochainColumn`, `KadisonKastler_ProperInfiniteProjectionCopies`, `KadisonKastler_QuotientStrongTests`, `KadisonKastler_RandomWalkPathAction`, `KadisonKastler_RandomWalkShiftLaw`, `KadisonKastler_RegularActionPackets`, `KadisonKastler_RegularActionSpectral`, `KadisonKastler_RegularCoreConjugation`, `KadisonKastler_RegularCoreCovariance`, `KadisonKastler_RowVectorEstimate`, `KadisonKastler_ScalarPacketMeasure`, `KadisonKastler_ShiftInvariantFunctions`, `KadisonKastler_SpatialMatrix`, `KadisonKastler_TracialSequenceQuotient`, `KadisonKastler_TypeIIISpectralMatrix`, `KadisonKastler_VaryingUnitaryLifts`, `KadisonKastler_WeakFieldProjectionDensity`.
--
--   **Imports.** It imports the published bundle `Def_StrongKadisonKastler`; the bundles `Q260K010`, `Q260K012`, `Q260K013`, `Q260K014` and `Q260K015` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q260K025` and `Q260K066`; the statements `OAI.KadisonKastler.exists_matrixOrbit_graphCost_le_ten`, `OAI.KadisonKastler.matrixOrbit_graphPairing_tendsto` and `OAI.KadisonKastler.regularCoreEmbedding_symmetry_of_balance`; the proofs of `OAI_KadisonKastler_TypeIIIFactor_exists_bounded_selfAdjoint_split`, `OAI.KadisonKastler.TypeIIIFactor.exists_isometry_onto_projection`, `OAI_KadisonKastler_TypeIIIFactor_exists_relative_matrix_stage_near_projection`, `OAI.KadisonKastler.cochainSymmetrize_residual_bound`, `OAI.KadisonKastler.constructed_exists_normalizing_representation`, `OAI.KadisonKastler.exists_bounded_conjugacy_from_centralPair`, `OAI.KadisonKastler.exists_countable_source_partition`, `OAI.KadisonKastler.exists_countable_source_partition_of_full`, `OAI.KadisonKastler.exists_matrixOrbit_graphCost_le_ten`, `OAI_KadisonKastler_exists_positive_matrix_central_unit_vector`, `OAI_KadisonKastler_expectedMatrixSubfactorModel_of_bicentralizer`, `OAI_KadisonKastler_expectedMatrixSubfactorModel_of_central_contraction`, `OAI_KadisonKastler_expectedMatrixSubfactorModel_of_local_refinement`, `OAI.KadisonKastler.matrixOrbit_graphPairing_tendsto`, `OAI_KadisonKastler_positiveCone_polar_conjugation`, `OAI.KadisonKastler.projection_equivalent_one_of_not_finite`, `OAI.KadisonKastler.publishedTypeIIIProjectionComparison` and `OAI.KadisonKastler.quadraticCochainSolver_of_modular_rows`.
-- source:
--   OpenAI, Universal strong Kadison–Kastler stability (result family 289), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 289; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-strong-Kadison-Kastler-stability-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Rat
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Interval.Set.Group
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
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.SpecialFunctions.PosPart
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Complex.Spectrum
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.MeanErgodic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Normed.Module.RieszLemma
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Banach
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
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
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
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Countable
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.ConditionalExpectation.AEMeasurable
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.Trim
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.Probability.Distributions.Cauchy
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ProductMeasure
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.RingTheory.Congruence.Hom
import Mathlib.RingTheory.TwoSidedIdeal.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Lattice
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.DeriveCountable
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Topology.Bases
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
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
import Definitions.Def_StrongKadisonKastler
import Definitions.Def_Q260K010
import Definitions.Def_Q260K012
import Definitions.Def_Q260K013
import Definitions.Def_Q260K014
import Definitions.Def_Q260K015

section
-- module Solutions.OAIQ075_KS.KadisonKastler_QuotientStrongTests
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Strong test fields from norm-dense quotient generators

The same fixed sequence in a separable source C-star algebra gives strong
unit-ball tests in each fiber representation. Nonfaithful fiber maps are
handled by the proved exact contraction-lifting theorem.
-/

namespace KadisonKastler

open TopologicalSpace

noncomputable section

universe u v

variable {A : Type u} [CStarAlgebra A]
  {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [SeparableSpace H]

def quotientStrongUnitBallTests
    (hK : PublishedKaplanskyDensity.{v}) (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (s : ℕ → A) (hs : ∀ j, ‖s j‖ ≤ 1)
    (hd : ∀ a : A, ‖a‖ ≤ 1 → ∀ ε : ℝ, 0 < ε → ∃ j, ‖a - s j‖ < ε) :
    StrongUnitBallTestSequence (generatedVonNeumannAlgebra φ.range) where
  op j := φ (s j)
  mem j := ⟨subset_generatedVonNeumannAlgebra φ.range ⟨s j, rfl⟩,
    (NonUnitalStarAlgHom.norm_apply_le φ _).trans (hs j)⟩
  dense T hT := by
    obtain ⟨ξ, hξ⟩ := exists_dense_seq (α := H)
    exact exists_strong_sequence_of_countable_tests ξ hξ (Set.range (fun j => φ (s j)))
      (by rintro _ ⟨j, rfl⟩; exact (NonUnitalStarAlgHom.norm_apply_le φ _).trans (hs j))
      T hT.2 (countableStrongTests_of_quotient_dense hK φ s hd ξ T hT)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_InfiniteFactorProperInfiniteness
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # An infinite factor is properly infinite

A proper isometry supplies an infinite orthogonal sequence of equivalent
wandering projections.  A maximal orthogonal family of partial isometries
with sources under the first wandering projection covers the identity by
factoriality.  Separability makes this family countable, so its ranges can
be mapped into the even and odd wandering projections separately.

No trace, dimension function, or published projection comparison is used.
-/

namespace KadisonKastler

open Generator.Tracial
open scoped BigOperators Topology

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

def projectionComplement (p : AlgebraProjection M) : AlgebraProjection M :=
  ⟨1 - p.val, p.property.one_sub⟩

def sourceFamily (p : AlgebraProjection M)
    (s : Set (PartialIsometry M)) : Prop :=
  (∀ v ∈ s, v.support ≤ p ∧ v.support.val ≠ 0) ∧
    s.Pairwise (fun v w => v.target.val * w.target.val = 0)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TypeIIISpectralMatrix
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.crossMatchingFintype _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Finite spectral partitions in a type III factor are matrix diagonals -/

namespace KadisonKastler

open Generator Generator.Tracial
open scoped BigOperators

noncomputable section

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
  [Fintype ι] [DecidableEq ι] {M : VonNeumannAlgebra H}



/-- Discard the zero spectral pieces without changing the spectral sum. -/
abbrev spectralPartitionNonzeroIndex {p : AlgebraProjection M} (Q : CornerPartition p) :=
  {i : Fin Q.size // (Q.piece i).val ≠ 0}

instance spectralPartitionNonzeroIndexFintype {p : AlgebraProjection M} (Q : CornerPartition p) :
    Fintype (spectralPartitionNonzeroIndex Q) := by
  classical
  exact Subtype.fintype _

instance spectralPartitionNonzeroIndexDecidableEq {p : AlgebraProjection M} (Q : CornerPartition p) :
    DecidableEq (spectralPartitionNonzeroIndex Q) := Classical.decEq _


end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FaithfulReducingNorm
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Norms in nonzero reducing representations of a simple algebra -/

namespace KadisonKastler

noncomputable section

universe u

variable {B H : Type u} [CStarAlgebra B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (E : Submodule ℂ H) [CompleteSpace E]
  (π : B →⋆ₐ[ℂ] (H →L[ℂ] H))
  (hE : ∀ b, E.starProjection * π b = π b * E.starProjection)

def reducingRepresentation : B →⋆ₐ[ℂ] (E →L[ℂ] E) :=
  (reducingRestriction E π.range (by
    rintro ⟨T, b, rfl⟩
    exact invariant_of_commutes_starProjection E (π b) (hE b))).comp
      (π.codRestrict π.range (fun b => ⟨b, rfl⟩))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_VaryingUnitaryLifts
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.tracialQuotientLinear_map _root_.OAI.KadisonKastler.tracialSequenceContinuous_apply _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.tracialSequenceValue_one _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Unitary lifts in a varying finite product

Coordinate unitary polar decompositions produce an exact unitary lift
through any surjective star quotient of the bounded product.
-/

namespace KadisonKastler

noncomputable section

variable {B : ℕ → Type*} [∀ j, CStarAlgebra (B j)] [∀ j, Nontrivial (B j)]

local instance varyingProductNontrivial_rd1bbbc_1 : Nontrivial (VaryingBoundedSequence B) := by
  refine ⟨⟨0, 1, ?_⟩⟩
  intro h
  have he := congrArg (fun x : VaryingBoundedSequence B => x 0) h
  exact zero_ne_one he
local instance varyingLiftOrder_rd1bbbc_1 (j : ℕ) : PartialOrder (B j) := CStarAlgebra.spectralOrder _
local instance varyingLiftStarOrder_rd1bbbc_1 (j : ℕ) : StarOrderedRing (B j) := CStarAlgebra.spectralOrderedRing _
local instance varyingProductLiftOrder_rd1bbbc_1 : PartialOrder (VaryingBoundedSequence B) :=
  CStarAlgebra.spectralOrder _
local instance varyingProductLiftPreorder_rd1bbbc_1 : Preorder (VaryingBoundedSequence B) :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance varyingProductLiftLE_rd1bbbc_1 : LE (VaryingBoundedSequence B) :=
  (CStarAlgebra.spectralOrder _).toLE
local instance varyingProductLiftStarOrder_rd1bbbc_1 : StarOrderedRing (VaryingBoundedSequence B) :=
  CStarAlgebra.spectralOrderedRing _
local instance varyingProductLiftCFC_rd1bbbc_1 :
    NonUnitalContinuousFunctionalCalculus ℝ (VaryingBoundedSequence B) IsSelfAdjoint :=
  IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus
local instance varyingProductLiftSpectrum_rd1bbbc_1 : NonnegSpectrumClass ℝ (VaryingBoundedSequence B) :=
  CStarAlgebra.instNonnegSpectrumClass
/-- A family of coordinate unitaries is bounded in the actual product. -/
def varyingUnitarySequence (v : ∀ j, unitary (B j)) :
    unitary (VaryingBoundedSequence B) := by
  let x : VaryingBoundedSequence B := ⟨fun j => (v j : B j),
    memℓp_infty ⟨1, by
      rintro _ ⟨j, rfl⟩
      exact (CStarRing.norm_coe_unitary (v j)).le⟩⟩
  refine ⟨x, ?_, ?_⟩ <;> apply lp.ext <;> funext j
  · exact (v j).property.1
  · exact (v j).property.2

@[simp]
theorem varyingUnitarySequence_apply (v : ∀ j, unitary (B j)) (j : ℕ) :
    (varyingUnitarySequence v : VaryingBoundedSequence B) j = (v j : B j) := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteMatrixFreeModel
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.tracialQuotientLinear_map _root_.OAI.KadisonKastler.tracialSequenceContinuous_apply _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.tracialSequenceValue_one _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A free Haar unitary with finite-matrix representatives

This is the first stage of the controlled-lift construction. The scalar
matrix base is embedded in the varying product, the published independence
identity produces the free unitary, and finite polar decomposition gives
actual unitary representatives at every coordinate.
-/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A]
variable {B : ℕ → Type*} [∀ j, CStarAlgebra (B j)] [∀ j, Nontrivial (B j)]

/-- A uniformly contractive family of star homomorphisms defines a homomorphism
into the bounded varying product. -/
def varyingSequenceHom (φ : ∀ j, A →⋆ₐ[ℂ] B j) : A →⋆ₐ[ℂ] VaryingBoundedSequence B where
  toFun x := ⟨fun j => φ j x, memℓp_infty ⟨‖x‖, by
    rintro _ ⟨j, rfl⟩
    exact NonUnitalStarAlgHom.norm_apply_le (φ j) x⟩⟩
  map_one' := by apply lp.ext; funext j; exact map_one (φ j)
  map_mul' x y := by apply lp.ext; funext j; exact map_mul (φ j) x y
  map_zero' := by apply lp.ext; funext j; exact map_zero (φ j)
  map_add' x y := by apply lp.ext; funext j; exact map_add (φ j) x y
  commutes' z := by apply lp.ext; funext j; exact (φ j).commutes z
  map_star' x := by apply lp.ext; funext j; exact map_star (φ j) x

@[simp]
theorem varyingSequenceHom_apply (φ : ∀ j, A →⋆ₐ[ℂ] B j) (x : A) (j : ℕ) :
    varyingSequenceHom φ x j = φ j x := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_HardyKernelShift
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Character shifts of the reproducing kernel

A backward shift followed by the positive-frequency projection is scalar on
an exponential kernel. Forward shifts preserve the positive-frequency space.
-/

namespace KadisonKastler

open MeasureTheory FourierTransform

noncomputable section

theorem positiveLaplace_shift_cut (z : ℂ) (hz : 0 < z.re) {b : ℝ} (hb : 0 ≤ b) :
    regularIndicatorProjection (Set.Ioi 0) measurableSet_Ioi
      (regularTranslateApply b (hardyFrequencyKernel z hz)) =
        Complex.exp (-z * b) • hardyFrequencyKernel z hz := by
  apply Lp.ext
  filter_upwards [regularIndicatorProjection_apply_ae (Set.Ioi 0) measurableSet_Ioi
      (regularTranslateApply b (hardyFrequencyKernel z hz)),
    regularTranslateApply_ae b (hardyFrequencyKernel z hz),
    (measurePreserving_add_right volume b).quasiMeasurePreserving.ae_eq_comp
      (positiveLaplaceKernel_memLp hz).coeFn_toLp,
    (positiveLaplaceKernel_memLp hz).coeFn_toLp,
    Lp.coeFn_smul (Complex.exp (-z * b)) (hardyFrequencyKernel z hz)]
    with s hp ht hshift hs hsmul
  rw [hp, hsmul, Pi.smul_apply]
  by_cases hpos : 0 < s
  · simp only [Set.indicator, Set.mem_Ioi, ite_eq_left hpos]
    rw [ht]
    change (hardyFrequencyKernel z hz) (s + b) =
      Complex.exp (-z * b) • (hardyFrequencyKernel z hz) s
    change hardyFrequencyKernel z hz (s + b) = positiveLaplaceKernel z (s + b) at hshift
    rw [hshift, show (hardyFrequencyKernel z hz) s = positiveLaplaceKernel z s from hs]
    have hsb : 0 < s + b := by linarith
    simp only [positiveLaplaceKernel, Set.indicator, Set.mem_Ioi, ite_eq_left hpos,
      ite_eq_left hsb, smul_eq_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  · simp only [Set.indicator, Set.mem_Ioi, ite_eq_right hpos]
    change 0 = Complex.exp (-z * b) • (hardyFrequencyKernel z hz) s
    rw [show (hardyFrequencyKernel z hz) s = positiveLaplaceKernel z s from hs]
    simp [positiveLaplaceKernel, hpos]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem fourier_frequencyProjection_zero (f : RegularCoreHilbert H) :
    𝓕 (regularFrequencyProjection 0 f) =
      regularIndicatorProjection (Set.Ioi 0) measurableSet_Ioi (𝓕 f) := by
  change (Lp.fourierTransformₗᵢ ℝ H)
    ((Lp.fourierTransformₗᵢ ℝ H).symm.conjStarAlgEquiv
      (regularIndicatorProjection (Set.Ioi (0 / (2 * Real.pi))) measurableSet_Ioi) f) = _
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.symm_symm, LinearIsometryEquiv.apply_symm_apply]
  simp only [zero_div]
  rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularActionSpectral
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Bounded spectral multipliers of the common regular action

These operators lie in the core commutant. They are used to recover
frequency packets from the bounded-frequency trace vector.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))

def regularActionMultiplier (φ : ℝ → ℂ) (hφ : Measurable φ)
    (C : ℝ) (hC : ∀ t, ‖φ t‖ ≤ C) :
    RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H :=
  unitaryConj (star (regularGauge U hU))
    ((Lp.fourierTransformₗᵢ ℝ H).symm.conjStarAlgEquiv
      (regularScalarMultiplier φ hφ C hC))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularActionPackets
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Spectral action on the packets of an invariant vector -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem fourier_regularTensorVector (φ : Lp ℂ 2 (volume : Measure ℝ)) (x : H) :
    (Lp.fourierTransformₗᵢ ℝ H) (regularTensorVector φ x) =
      regularTensorVector ((Lp.fourierTransformₗᵢ ℝ ℂ) φ) x :=
  fourier_scalarLpTensor φ x

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_HardyEvaluationConstruction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Constructed evaluation of positive-frequency multipliers

The normalized Cauchy kernel gives the Poisson compression. Its character
shifts and Fourier uniqueness prove invariance of the evaluation kernel.
Thus the compression is an algebra homomorphism on the multiplier algebra.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem positiveFrequencyAlgebra_preserves
    (T : positiveFrequencyAlgebra (H := H)) (f : RegularCoreHilbert H)
    (hf : regularFrequencyProjection 0 f = f) :
    regularFrequencyProjection 0 (T.val f) = T.val f := by
  have h := congrArg (fun A : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H => A f) T.property.2
  change regularFrequencyProjection 0 (T.val (regularFrequencyProjection 0 f)) =
    T.val (regularFrequencyProjection 0 f) at h
  simpa only [hf] using h

universe u

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixOrbitSampleLaw
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.concrete_finiteDimensional _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSignedGroup_finite _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Finite laws of the actual matrix-orbit samples

This converts the complex four-variable matrix-average identities to
real moment identities for a single product-valued sample. It supplies
the diagonal and the two off-diagonal inputs to the independent-sample
fourth-moment estimate.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- An operator sampled from the finite two-sided matrix orbit. -/
def matrixOrbitSample {d : ℕ}
    (E : Generator.MatrixUnitSystem (Fin d) (H →L[ℂ] H))
    (x : H →L[ℂ] H) (g : MatrixOrbitIndex d) : H →L[ℂ] H :=
  unitaryDoubleOrbit x (matrixUnitSignedRepresentation E g.1)
    (matrixUnitSignedRepresentation E g.2)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_NestedScalarMeans
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.NonsingularAction.leftOnProduct_apply _root_.OAI.KadisonKastler.ScalarOperatorKernel.toContinuous_apply _root_.OAI.KadisonKastler.UniformMeasurableOperators.coefficientFamily_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.randomWalkPathAction_apply _root_.OAI.KadisonKastler.shiftBoundaryAction_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Composing scalar means over two group coordinates

The row and outer means are bounded linear maps on actual L-infinity classes.
Here we establish the algebraic and norm properties of their composition;
the action identity is supplied by the commuting-coordinate construction.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory
open scoped BoundedContinuousFunction

variable {G D : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace D] {μ : Measure D} [IsProbabilityMeasure μ]
  {α β : NonsingularAction G D μ}

def nestedMeanRowsL (m : ScalarBoundaryMean β) :
    ((G × G) →ᵇ ScalarLInfinity μ) →L[ℂ] (G →ᵇ ScalarLInfinity μ) :=
  (m.toCLM.compLeftContinuousBounded G).comp boundedFamilyCurryL

@[simp]
theorem nestedMeanRowsL_apply (m : ScalarBoundaryMean β)
    (F : (G × G) →ᵇ ScalarLInfinity μ) (g : G) :
    nestedMeanRowsL m F g = m.toCLM (boundedFamilyRow F g) := rfl

def nestedScalarMeanL (m₁ : ScalarBoundaryMean α) (m₂ : ScalarBoundaryMean β) :
    ((G × G) →ᵇ ScalarLInfinity μ) →L[ℂ] ScalarLInfinity μ :=
  m₁.toCLM.comp (nestedMeanRowsL m₂)

theorem nestedMeanRowsL_norm_le (m : ScalarBoundaryMean β)
    (F : (G × G) →ᵇ ScalarLInfinity μ) : ‖nestedMeanRowsL m F‖ ≤ ‖F‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg F)).mpr
  intro g
  exact (m.norm_le _).trans (boundedFamilyRow_norm_le F g)

theorem nestedScalarMeanL_norm_le (m₁ : ScalarBoundaryMean α) (m₂ : ScalarBoundaryMean β)
    (F : (G × G) →ᵇ ScalarLInfinity μ) : ‖nestedScalarMeanL m₁ m₂ F‖ ≤ ‖F‖ :=
  (m₁.norm_le _).trans (nestedMeanRowsL_norm_le m₂ F)

theorem nestedScalarMeanL_positive (m₁ : ScalarBoundaryMean α) (m₂ : ScalarBoundaryMean β)
    (F : (G × G) →ᵇ ScalarLInfinity μ)
    (hF : ∀ g, ∀ᵐ x ∂μ, (F g x).im = 0 ∧ 0 ≤ (F g x).re) :
    ∀ᵐ x ∂μ, (nestedScalarMeanL m₁ m₂ F x).im = 0 ∧
      0 ≤ (nestedScalarMeanL m₁ m₂ F x).re := by
  apply m₁.positive
  intro g
  exact m₂.positive (boundedFamilyRow F g) (fun h => hF (g, h))

theorem nestedMeanRowsL_module (m : ScalarBoundaryMean β) (b : ScalarLInfinity μ)
    (F : (G × G) →ᵇ ScalarLInfinity μ) :
    nestedMeanRowsL m (scalarBoundaryModule b F) = scalarBoundaryModule b (nestedMeanRowsL m F) := by
  apply BoundedContinuousFunction.ext
  intro g
  have hr : boundedFamilyRow (scalarBoundaryModule b F) g =
      scalarBoundaryModule b (boundedFamilyRow F g) := by
    apply BoundedContinuousFunction.ext
    intro h
    rfl
  change m.toCLM (boundedFamilyRow (scalarBoundaryModule b F) g) = _
  rw [hr, m.module_map]
  rfl

theorem nestedScalarMeanL_module (m₁ : ScalarBoundaryMean α) (m₂ : ScalarBoundaryMean β)
    (b : ScalarLInfinity μ) (F : (G × G) →ᵇ ScalarLInfinity μ) :
    nestedScalarMeanL m₁ m₂ (scalarBoundaryModule b F) =
      scalarInfinityMul b (nestedScalarMeanL m₁ m₂ F) := by
  change m₁.toCLM (nestedMeanRowsL m₂ (scalarBoundaryModule b F)) = _
  rw [nestedMeanRowsL_module, m₁.module_map]
  rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_NestedMeanEquivariance
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Equivariance of nested means for separate group actions -/

namespace KadisonKastler

noncomputable section

open MeasureTheory
open scoped BoundedContinuousFunction

variable {G D : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace D] {μ : Measure D} [IsProbabilityMeasure μ]
  (α₁ α₂ : NonsingularAction G D μ) (β : NonsingularAction (G × G) D μ)
  (hβ : ∀ g z, β.toPerm g z = α₁.toPerm g.1 (α₂.toPerm g.2 z))

include hβ in
omit [TopologicalSpace G] [DiscreteTopology G] [IsProbabilityMeasure μ] in
theorem scalarSeparatePullback (g : G × G) (f : ScalarLInfinity μ) :
    scalarInfinityPullback (β.toPerm g) (β.quasi g) f =
      scalarInfinityPullback (α₂.toPerm g.2) (α₂.quasi g.2)
        (scalarInfinityPullback (α₁.toPerm g.1) (α₁.quasi g.1) f) := by
  apply Lp.ext
  filter_upwards [scalarInfinityPullback_ae (β.toPerm g) (β.quasi g) f,
    scalarInfinityPullback_ae (α₂.toPerm g.2) (α₂.quasi g.2)
      (scalarInfinityPullback (α₁.toPerm g.1) (α₁.quasi g.1) f),
    (α₂.quasi g.2).ae (scalarInfinityPullback_ae (α₁.toPerm g.1) (α₁.quasi g.1) f)]
    with z ha hb hc
  rw [ha, hb, hc, hβ]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_NormalTwoStateSupports
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 0

namespace OAI

/-! # The right supports of the two summands in the two-state representation -/

namespace KadisonKastler

open Generator

noncomputable section

universe u

variable {H K : Type u}
  [NormedAddCommGroup H]
  [InnerProductSpace ℂ H]
  [CompleteSpace H]
  [NormedAddCommGroup K]
  [InnerProductSpace ℂ K]
  [CompleteSpace K]
  {M : VonNeumannAlgebra H}
  {N : VonNeumannAlgebra K}
  (θ : Algebra M ≃⋆ₐ[ℂ] Algebra N)

/-- The projection onto one of the two original representation summands. -/
def twoStateSummandProjection (i : Fin 2) :
    TwoStateMatrixHilbert H K →L[ℂ] TwoStateMatrixHilbert H K :=
  hilbertPairOperator (if i = 0 then 1 else 0) (if i = 0 then 0 else 1)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_NormalTwoStateGeometry
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.finiteDiagonalMap_apply _root_.OAI.KadisonKastler.finiteL2Basis_apply _root_.OAI.KadisonKastler.finiteLocalAmplificationValue_apply _root_.OAI.KadisonKastler.finiteLocalAmplification_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.pointedPowerFibreEquiv_basis _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 0

namespace OAI

/-! # Concrete corners of the two-representation Hilbert space -/

namespace KadisonKastler

open Generator

noncomputable section

universe u

variable {H K : Type u}
  [NormedAddCommGroup H]
  [InnerProductSpace ℂ H]
  [CompleteSpace H]
  [NormedAddCommGroup K]
  [InnerProductSpace ℂ K]
  [CompleteSpace K]
  {M : VonNeumannAlgebra H}
  {N : VonNeumannAlgebra K}
  (θ : Algebra M ≃⋆ₐ[ℂ] Algebra N)

def twoStateSourceEmbedding : H →ₗᵢ[ℂ] TwoStateMatrixHilbert H K where
  toFun x := WithLp.toLp 2 (tupleSingle 0 x, 0)
  map_add' x y := by simp [map_add, ← WithLp.toLp_add]
  map_smul' z x := by simp [map_smul, ← WithLp.toLp_smul]
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp

def twoStateTargetEmbedding : K →ₗᵢ[ℂ] TwoStateMatrixHilbert H K where
  toFun x := WithLp.toLp 2 (0, tupleSingle 1 x)
  map_add' x y := by simp [map_add, ← WithLp.toLp_add]
  map_smul' z x := by simp [map_smul, ← WithLp.toLp_smul]
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp

@[simp] theorem twoStateSourceEmbedding_adjoint (x : TwoStateMatrixHilbert H K) :
    (twoStateSourceEmbedding (H := H) (K := K)).toContinuousLinearMap.adjoint x = x.fst 0 := by
  apply ext_inner_left ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_right]
  simp [twoStateSourceEmbedding, WithLp.prod_inner_apply, PiLp.inner_apply,
    tupleSingle_apply, Fin.sum_univ_two]

@[simp] theorem twoStateTargetEmbedding_adjoint (x : TwoStateMatrixHilbert H K) :
    (twoStateTargetEmbedding (H := H) (K := K)).toContinuousLinearMap.adjoint x = x.snd 1 := by
  apply ext_inner_left ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_right]
  simp [twoStateTargetEmbedding, WithLp.prod_inner_apply, PiLp.inner_apply,
    tupleSingle_apply, Fin.sum_univ_two]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_NormalizerTopology
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The closed group of unitary normalizers

Uniform limits of normalizing unitary families remain normalizing. This
provides the complete space in which the normalizer correction is iterated.
-/

namespace KadisonKastler

open scoped BoundedContinuousFunction

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]

instance normalizingFamilyMetricSpace (P : VonNeumannAlgebra H) :
    MetricSpace (NormalizingFamily (G := G) P) := inferInstanceAs (MetricSpace (Subtype _))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_OperatorCochainColumn
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A completely bounded cochain contraction on the full operator algebra

The rank-one last column realizes the usual Hochschild contraction while
retaining its norm at every matrix level.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] OAI.KadisonKastler.cochainColumnOperatorOrder
attribute [local instance] OAI.KadisonKastler.cochainColumnOperatorStarOrder
def operatorCochainContraction
    {f : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H)} {c : ℝ}
    (hf : HaagerupBound f c) (hc : 0 ≤ c) (φ : H →L[ℂ] ℂ) (ξ : H) :
    (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H) :=
  (cochainColumnEvaluation φ ξ).comp (hf.toContinuousBilinear hc)

@[simp] theorem operatorCochainContraction_apply
    {f : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H)} {c : ℝ}
    (hf : HaagerupBound f c) (hc : 0 ≤ c) (φ : H →L[ℂ] ℂ) (ξ : H)
    (a : H →L[ℂ] H) (y : H) :
    operatorCochainContraction hf hc φ ξ a y = f a (cochainColumn φ y) ξ := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProperInfiniteProjectionCopies
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Countable copies of a full projection

A maximal orthogonal family with sources under a full projection gives a
countable partition of the identity.  Two orthogonal isometries provide
room for countably many copies of the full projection.  The partition
embeds into their sum, and concrete projection Schroeder--Bernstein moves
that sum onto the identity.
-/

namespace KadisonKastler

open Generator.Tracial Filter
open scoped BigOperators Topology

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

def fullSourceFamily (p : AlgebraProjection M)
    (s : Set (PartialIsometry M)) : Prop :=
  (∀ v ∈ s, v.support ≤ p ∧ v.support.val ≠ 0) ∧
    s.Pairwise (fun v w => v.target.val * w.target.val = 0)

def finiteProjectionSum (p : ℕ → AlgebraProjection M)
    (ho : Pairwise (fun i j => (p i).val * (p j).val = 0))
    (s : Finset ℕ) : AlgebraProjection M :=
  AlgebraProjection.finsetSum p s (fun _ _ _ _ hij => ho hij)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RandomWalkPathAction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The nonsingular action on rooted random-walk paths

The root is separated from the sequence of increments. Left translation
changes only the root, and commutes with advancing the random walk.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory

variable (G : Type*) [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]

theorem randomWalkAdvance_measurable : Measurable (randomWalkAdvance G) := by
  apply Measurable.prodMk
  · exact (measurable_of_countable (fun p : G × G => p.1 * p.2)).comp
      (measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd))
  · exact Measurable.of_eval (fun n => (measurable_pi_apply (n + 1)).comp measurable_snd)

theorem randomWalkAdvance_action (g : G) (x : RandomWalkPath G) :
    randomWalkAdvance G ((randomWalkPathAction G).toPerm g x) =
      (randomWalkPathAction G).toPerm g (randomWalkAdvance G x) := by
  apply Prod.ext
  · exact mul_assoc g x.1 (x.2 0)
  · rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RandomWalkShiftLaw
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instIsProbabilityMeasureBilateralWalkPathBilateralWalkLaw _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Independence of the first increment and the remaining random walk -/

namespace KadisonKastler

noncomputable section

open MeasureTheory ProbabilityTheory

variable {G : Type*} [MeasurableSpace G]

variable [Group G] [Countable G] [MeasurableSingletonClass G]

def randomWalkSplit (x : RandomWalkPath G) : (G × G) × (ℕ → G) :=
  ((x.1, x.2 0), fun n => x.2 (n + 1))

omit [Group G] [Countable G] [MeasurableSingletonClass G] in
theorem randomWalkSplit_measurable : Measurable (randomWalkSplit (G := G)) := by
  exact (measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd)).prodMk
    (Measurable.of_eval (fun n => (measurable_pi_apply (n + 1)).comp measurable_snd))

theorem randomWalkSplit_law :
    (randomWalkPathLaw G).map randomWalkSplit =
      ((symmetricRandomWalkLaw G).prod (symmetricRandomWalkLaw G)).prod
        (Measure.infinitePi (fun _ : ℕ => symmetricRandomWalkLaw G)) := by
  let μ := symmetricRandomWalkLaw G
  let ν := Measure.infinitePi (fun _ : ℕ => μ)
  let h : (ℕ → G) → G × (ℕ → G) := fun x => (x 0, fun n => x (n + 1))
  have hh : Measurable h := by fun_prop
  have he : (μ.prod ν).map (Prod.map id h) = μ.prod (μ.prod ν) := by
    rw [← Measure.map_prod_map μ ν measurable_id hh, Measure.map_id]
    exact congrArg (Measure.prod μ) (iid_first_increment_tail_law μ)
  have ha : (μ.prod (μ.prod ν)).map MeasurableEquiv.prodAssoc.symm = (μ.prod μ).prod ν := by
    rw [← Measure.prodAssoc_prod, Measure.map_map (by fun_prop) (by fun_prop)]
    simp only [MeasurableEquiv.symm_comp_self, Measure.map_id]
  change (μ.prod ν).map (MeasurableEquiv.prodAssoc.symm ∘ Prod.map id h) = _
  rw [← Measure.map_map (by fun_prop) (measurable_id.prodMap hh), he]
  exact ha

theorem randomWalkAdvance_law :
    (randomWalkPathLaw G).map (randomWalkAdvance G) =
      (randomWalkConvolution G).prod
        (Measure.infinitePi (fun _ : ℕ => symmetricRandomWalkLaw G)) := by
  let μ := symmetricRandomWalkLaw G
  let ν := Measure.infinitePi (fun _ : ℕ => μ)
  let m : G × G → G := fun p => p.1 * p.2
  have hm : Measurable m := measurable_of_countable _
  change (randomWalkPathLaw G).map (Prod.map m id ∘ randomWalkSplit) = _
  rw [← Measure.map_map (hm.prodMap measurable_id) randomWalkSplit_measurable,
    randomWalkSplit_law, ← Measure.map_prod_map (μ.prod μ) ν hm measurable_id, Measure.map_id]
  rfl

theorem randomWalkAdvance_quasi :
    Measure.QuasiMeasurePreserving (randomWalkAdvance G) (randomWalkPathLaw G)
      (randomWalkPathLaw G) := by
  refine ⟨randomWalkAdvance_measurable G, ?_⟩
  rw [randomWalkAdvance_law]
  exact Measure.AbsolutelyContinuous.prod (randomWalkConvolution_absolutelyContinuous_law (G := G))
    (Measure.AbsolutelyContinuous.refl _)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCoreConjugation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The antiunitary of the regular modular representation

In concrete coordinates this sends `f(t)` to `U(-t) J(f(-t))`.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
  (J : H ≃ₗᵢ⋆[ℂ] H)

def regularCoreConjugation : RegularCoreHilbert H ≃ₗᵢ⋆[ℂ] RegularCoreHilbert H :=
  (regularReflectedConjugation J).trans
    (Unitary.linearIsometryEquiv (star (regularGauge U hU)))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCoreCovariance
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Covariance of the concrete regular generators -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))

def regularCoreMonomial (a : H →L[ℂ] H) (s : Multiplicative ℝ) :
    RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H :=
  regularCoreEmbedding U hU a * (regularRightTranslation (H := H) s :
    RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RowVectorEstimate
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! Vector estimates for truncating the countable rows in module averaging. -/

namespace KadisonKastler

noncomputable section

open Generator
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance rowVectorAlgebraOrder_rd1bbbc_1 (M : VonNeumannAlgebra H) : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance rowVectorAlgebraStarOrder_rd1bbbc_1 (M : VonNeumannAlgebra H) : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _
local instance rowVectorOperatorOrder_rd1bbbc_1 : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
local instance rowVectorOperatorStarOrder_rd1bbbc_1 : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _
def rowAdjointVector {M : VonNeumannAlgebra H} {ι : Type*} [Fintype ι]
    (r : ι → Algebra M) (ξ : H) : FiniteHilbert ι H :=
  WithLp.toLp 2 fun i => (star (r i) : H →L[ℂ] H) ξ

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ScalarPacketMeasure
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The probability measure and action average of a scalar packet -/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

theorem scalarPacketMeasure_univ (φ : Lp ℂ 2 (volume : Measure ℝ)) :
    scalarPacketMeasure φ Set.univ=ENNReal.ofReal (‖φ‖^2) := by
  rw [scalarPacketMeasure,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal
      ((Lp.memLp φ).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0))
      (Eventually.of_forall fun t => sq_nonneg ‖φ t‖),regular_integral_norm_sq]

theorem scalarPacketMeasure_probability (φ : Lp ℂ 2 (volume : Measure ℝ)) (hφ : ‖φ‖=1) :
    IsProbabilityMeasure (scalarPacketMeasure φ) := by
  constructor
  rw [scalarPacketMeasure_univ,hφ]
  norm_num

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ShiftInvariantFunctions
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Scalar functions on the invariant sigma algebra

The invariant measurable structure has exactly the essentially bounded
scalar functions fixed by the shift. The countable rational cuts below
turn invariance of measurable sets into simultaneous pointwise equality.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {S : X → X}

theorem scalarInfinity_fixed_iff_measurable_shiftInvariantSigma
    (hS : Measure.QuasiMeasurePreserving S μ μ) (f : ScalarLInfinity μ) :
    scalarInfinityPullback S hS f = f ↔ Measurable[shiftInvariantSigma μ S] f := by
  constructor
  · intro he
    apply measurable_shiftInvariantSigma_of_fixed μ S (Lp.stronglyMeasurable f).measurable
    have ha := scalarInfinityPullback_ae S hS f
    rw [he] at ha
    exact ha.symm
  · intro hf
    apply Lp.ext
    exact (scalarInfinityPullback_ae S hS f).trans
      (complex_fixed_of_measurable_shiftInvariantSigma hf)

theorem scalarInfinity_fixed_mem_lpMeas
    (hS : Measure.QuasiMeasurePreserving S μ μ) (f : ScalarLInfinity μ)
    (hf : scalarInfinityPullback S hS f = f) :
    f ∈ lpMeas ℂ ℂ (shiftInvariantSigma μ S) ⊤ μ := by
  rw [mem_lpMeas_iff_aestronglyMeasurable]
  exact ((scalarInfinity_fixed_iff_measurable_shiftInvariantSigma hS f).mp hf).stronglyMeasurable.aestronglyMeasurable

theorem scalarInfinity_fixed_of_aestronglyMeasurable
    (hS : Measure.QuasiMeasurePreserving S μ μ) (f : ScalarLInfinity μ)
    (hf : AEStronglyMeasurable[shiftInvariantSigma μ S] f μ) :
    scalarInfinityPullback S hS f = f := by
  have hm := complex_fixed_of_measurable_shiftInvariantSigma hf.stronglyMeasurable_mk.measurable
  apply Lp.ext
  filter_upwards [scalarInfinityPullback_ae S hS f, hf.ae_eq_mk,
    hS.ae hf.ae_eq_mk, hm] with x hp hx hs hmk
  exact hp.trans (hs.trans (hmk.trans hx.symm))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SpatialMatrix
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSignedGroup_finite _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Finite matrix amplification in a spatial tensor product

An actual matrix-unit system in the second tensor factor gives a star
representation of operator-valued matrices. Its norm is the C-star matrix
norm: multiplying on both sides by matrix units recovers each coefficient,
so the representation is faithful whenever the second Hilbert space is
nonzero. No assertion about amplification of an ordinary algebra gap is
used here.
-/

namespace KadisonKastler

open UnitalTomsWinter Generator
open scoped BigOperators TensorProduct InnerProductSpace

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

attribute [local instance] OAI.KadisonKastler.spatialMatrixStarOrder
def spatialMatrixCoefficient (E : MatrixUnitSystem ι (K →L[ℂ] K)) :
    (H →L[ℂ] H) →⋆ₐ[ℂ] (spatialMatrixUnits (H := H) E).commutant :=
  (spatialLeft (K := K)).codRestrict _ (by
    intro a i j
    exact (Pureness.spatialLeftRight_commute
      (StarAlgHom.id ℂ (H →L[ℂ] H)) (StarAlgHom.id ℂ (K →L[ℂ] K))
      a (E.entry i j)).symm)

/-- The actual finite spatial matrix representation. -/
def spatialMatrixHom (E : MatrixUnitSystem ι (K →L[ℂ] K)) :
    CStarMatrix ι ι (H →L[ℂ] H) →⋆ₐ[ℂ]
      (SpatialHilbert H K →L[ℂ] SpatialHilbert H K) :=
  (spatialMatrixUnits (H := H) E).coefficientHom.comp
    ((matrixEntryStarHom (spatialMatrixCoefficient (H := H) E)).comp
      CStarMatrix.ofMatrixStarAlgEquiv.symm.toStarAlgHom)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TracialSequenceQuotient
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.algebraCStarAlgebra _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The faithful trace on the tracial sequence quotient -/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {B : ℕ → Type*} [∀ j, CStarAlgebra (B j)] [∀ j, Nontrivial (B j)]
  (τ : ∀ j, FaithfulTracialState (B j)) (ω : Ultrafilter ℕ)

attribute [local instance] OAI.KadisonKastler.tracialSequenceProductOrder
attribute [local instance] OAI.KadisonKastler.tracialSequenceProductStarOrder
instance tracialSequenceQuotientNontrivial : Nontrivial (TracialSequenceQuotient τ ω) := by
  have hn : (1 : TracialSequenceQuotient τ ω) ≠ 0 := by
    intro h
    have he := (tracialQuotientTrace τ ω).map_one
    rw [h, map_zero] at he
    exact zero_ne_one he
  exact ⟨⟨1, 0, hn⟩⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_WeakFieldProjectionDensity
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Spectral step approximation of measurable fields

A common dyadic mesh is used for every point of the measure space.
Measurability of its finitely many projection fields follows inductively
from the constructed spectral support. The existing concrete spectral
interval estimate gives a uniform operator-norm error.
-/

namespace KadisonKastler

open MeasureTheory Generator.Tracial
open scoped Topology CStarAlgebra BigOperators

noncomputable section

variable {D H : Type*} [MeasurableSpace D] {μ : Measure D}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace WeakOperatorRepresentative

attribute [local instance] OAI.KadisonKastler.WeakOperatorRepresentative.densityFieldOrder
local instance densityFieldPreorder_rd1bbbc_1 : Preorder (WeakOperatorRepresentative (H := H) μ) :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance densityFieldLE_rd1bbbc_1 : LE (WeakOperatorRepresentative (H := H) μ) :=
  (CStarAlgebra.spectralOrder _).toLE
local instance densityFieldStarOrder_rd1bbbc_1 : StarOrderedRing (WeakOperatorRepresentative (H := H) μ) :=
  CStarAlgebra.spectralOrderedRing _
local instance densityTopOrder_rd1bbbc_1 : PartialOrder ((fullOperatorAlgebra (H := H)).toStarSubalgebra) :=
  CStarAlgebra.spectralOrder _
local instance densityTopPreorder_rd1bbbc_1 : Preorder ((fullOperatorAlgebra (H := H)).toStarSubalgebra) :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance densityTopLE_rd1bbbc_1 : LE ((fullOperatorAlgebra (H := H)).toStarSubalgebra) :=
  (CStarAlgebra.spectralOrder _).toLE
local instance densityTopStarOrder_rd1bbbc_1 : StarOrderedRing ((fullOperatorAlgebra (H := H)).toStarSubalgebra) :=
  CStarAlgebra.spectralOrderedRing _
def projectionField (p : D → H →L[ℂ] H) (hp : ∀ x, IsStarProjection (p x))
    (hm : ∀ ξ, AEStronglyMeasurable (fun x => p x ξ) μ) :
    WeakOperatorRepresentative (H := H) μ :=
  mk p 1 (fun x => IsStarProjection.norm_le _ (hp x)) hm
    (fun ξ => by simpa only [(hp _).isSelfAdjoint.star_eq] using hm ξ)

theorem topElement_isSelfAdjoint (F : WeakOperatorRepresentative (H := H) μ)
    (hF : IsSelfAdjoint F) (x : D) : IsSelfAdjoint (topElement F x) := by
  apply isSelfAdjointOfMapCompat_p0 (fullOperatorAlgebra (H := H)).toStarSubalgebra.subtype
    Subtype.val_injective
  exact hF.map (evalHom x)

end WeakOperatorRepresentative

end

end KadisonKastler

end OAI
end


