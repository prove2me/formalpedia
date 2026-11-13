-- Prove2me | Definitions.Def_Q260K018
-- name    : Q260K018
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T04:48:41.020879+00:00
-- url     : https://prove2.me/theorems/9b34f417-ba5b-438b-b57e-4f1959ae2153
-- title:
--   Definitions bundle Q260K018 of the split of OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 64 declarations of OpenAI's Lean: 29 definitions, 2 instances and 33 theorems. The definitions and types are `OAI.KadisonKastler.PublishedCentralPairDecomposition`, `OAI.KadisonKastler.ScalarInvariantMean.algebraBimoduleMean`, `OAI.KadisonKastler.ScalarInvariantMean.averageConjugation`, `OAI.KadisonKastler.ScalarInvariantMean.averagedState`, `OAI.KadisonKastler.ScalarInvariantMean.bimoduleMean`, `OAI.KadisonKastler.ScalarInvariantMean.conjugationFamilyHom`, `OAI.KadisonKastler.ScalarInvariantMean.operatorMeanCP`, `OAI.KadisonKastler.ScalarInvariantMean.stateOrbitMap`, `OAI.KadisonKastler.ScalarInvariantMean.stateOrbitScalar`, `OAI.KadisonKastler.SeparableStrongStability`, `OAI.KadisonKastler.SmallNormalizerFactorization`, `OAI.KadisonKastler.UniformFactorStability`, `OAI.KadisonKastler.abelianScalarInvariantMean`, `OAI.KadisonKastler.adjustedCornerVector`, `OAI.KadisonKastler.algebraCocycleRepresentative`, `OAI.KadisonKastler.bilateralBoundaryPair`, `OAI.KadisonKastler.bilateralNegativeBoundary`, `OAI.KadisonKastler.bilateralPositiveBoundary`, `OAI.KadisonKastler.bilateralTransportPair`, `OAI.KadisonKastler.bilateralTransportPairAt`, `OAI.KadisonKastler.boundaryPairLift`, `OAI.KadisonKastler.boundedWeakAlgebraCoefficients`, `OAI.KadisonKastler.boundedWeakRowOrbit`, `OAI.KadisonKastler.characterAverage`, `OAI.KadisonKastler.characterCommutant`, `OAI.KadisonKastler.randomWalkFromIdentity`, `OAI.KadisonKastler.randomWalkIdentityBoundary`, `OAI.KadisonKastler.regularCharacterRepresentation`, `OAI.KadisonKastler.scalarBoundaryStar`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `KadisonKastler_AbelianInvariantMean`, `KadisonKastler_AdjustedCornerState`, `KadisonKastler_AlgebraCocycleRepresentatives`, `KadisonKastler_Basic`, `KadisonKastler_BilateralBoundaryPair`, `KadisonKastler_BilateralBoundaryTransport`, `KadisonKastler_BoundaryPairInvariance`, `KadisonKastler_CharacterAverageDescent`, `KadisonKastler_CharacterContinuity`, `KadisonKastler_CommonCenterFromFactors`, `KadisonKastler_ConjugationAveragedState`, `KadisonKastler_CyclicGaugeKernel`, `KadisonKastler_FourierModulation`, `KadisonKastler_FrequencyNest`, `KadisonKastler_HardyCauchyBoundary`, `KadisonKastler_InvariantOperatorMean`, `KadisonKastler_L2MeasurableExtension`, `KadisonKastler_PublishedCentralDecomposition`, `KadisonKastler_RandomWalkIdentityBoundary`, `KadisonKastler_RegularCoreCharacters`, `KadisonKastler_RegularCoreDensePeriods`, `KadisonKastler_RegularCoreOperators`, `KadisonKastler_ScalarMeanStar`, `KadisonKastler_SeparableReduction`, `KadisonKastler_ShiftedFrequencyFields`, `KadisonKastler_SpatialProductSeparating`, `KadisonKastler_SpatialRightSlice`, `KadisonKastler_SpatialStrong`, `KadisonKastler_SpectralCommutant`, `KadisonKastler_SubalgebraInvariantMean`, `KadisonKastler_TypeIIISmallNormalizer`, `KadisonKastler_WeakMapCompact`, `KadisonKastler_WeakRowOrbit`.
--
--   **Imports.** It imports the published bundle `Def_StrongKadisonKastler`; the bundles `Q260K007`, `Q260K010`, `Q260K012` and `Q260K013` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q260K022`, `Q260K023`, `Q260K024` and `Q260K025`; the statements `OAI.KadisonKastler.commonCenterSeparableStability_of_factors`, `OAI.KadisonKastler.constructed_exists_normalizer_near_mean`, `OAI.KadisonKastler.constructed_exists_normalizing_representation`, `OAI.KadisonKastler.minimal_row_family_right_module_of_factorization`, `OAI.KadisonKastler.publishedCentralPairDecomposition` and `OAI.KadisonKastler.uniform_factor_strong_stability`; the proofs of `OAI.KadisonKastler.FrequencySmoothing.norm_product_sub_one_le`, `OAI.KadisonKastler.ScalarInvariantMean.algebraMean_translate`, `OAI.KadisonKastler.concrete_ucp_starEquiv_of_published`, `OAI.KadisonKastler.exists_invariant_state_preserving_values` and `OAI_KadisonKastler_spatialField_constant_of_two_shifts`.
-- source:
--   OpenAI, Universal strong Kadison–Kastler stability (result family 289), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 289; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-strong-Kadison-Kastler-stability-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Rat
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Analysis.CStarAlgebra.Exponential
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.Spectrum
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.LinearPMap
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
import Mathlib.Analysis.Normed.Algebra.Exponential
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
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Isometric
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
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
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Countable
import Mathlib.LinearAlgebra.Dual.Lemmas
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
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Function.ConditionalExpectation.AEMeasurable
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Unique
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Measure.Trim
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.VectorMeasure.WithDensity
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.Probability.Distributions.Cauchy
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Moments.ComplexMGF
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
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.ThickenedIndicator
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_StrongKadisonKastler
import Definitions.Def_Q260K007
import Definitions.Def_Q260K010
import Definitions.Def_Q260K012
import Definitions.Def_Q260K013

section
-- module Solutions.OAIQ075_KS.KadisonKastler_Basic
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# The concrete Kadison–Kastler distance

The distance is the operator-norm Hausdorff distance between the closed unit
balls of two concrete, unital von Neumann algebras.  All Hilbert spaces are
allowed, including the zero space. The elementary estimates belong to §2 of
*Universal strong Kadison–Kastler stability* (2026).
-/

namespace KadisonKastler

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem kkDistance_comm (M N : VonNeumannAlgebra H) : kkDistance M N = kkDistance N M :=
  Metric.hausdorffDist_comm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_InvariantOperatorMean
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.matrixAlgebraEquiv_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.operatorEntry_hilbertMatrix _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Operator averaging from an actual scalar invariant mean

The scalar mean is data on bounded scalar functions. Riesz representation
constructs the operator average from its coefficients. No operator-valued
mean, fixed-point projection, or amenability conclusion is assumed.
-/

namespace KadisonKastler

open scoped BoundedContinuousFunction BigOperators Topology CStarAlgebra

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]

namespace ScalarInvariantMean

variable (m : ScalarInvariantMean G)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem operatorMean_const (T : H →L[ℂ] H) :
    m.operatorMean (BoundedContinuousFunction.const G T) = T := by
  ext x
  apply ext_inner_left ℂ
  intro y
  rw [m.inner_operatorMean]
  have hc : coefficient (BoundedContinuousFunction.const G T) x y =
      BoundedContinuousFunction.const G (inner ℂ y (T x)) := by ext g; rfl
  rw [hc, m.fixed]

attribute [local instance] OAI.KadisonKastler.ScalarInvariantMean.invariantMeanFamilyCStar
attribute [local instance] OAI.KadisonKastler.ScalarInvariantMean.invariantMeanFamilyOrder
attribute [local instance] OAI.KadisonKastler.ScalarInvariantMean.invariantMeanFamilyStarOrder
/-- Complete positivity follows by applying scalar positivity to the finite
sum of all the matrix coefficients of a positive amplified family. -/
def operatorMeanCP : (G →ᵇ (H →L[ℂ] H)) →CP (H →L[ℂ] H) where
  toLinearMap := m.operatorMean.toLinearMap
  map_cstarMatrix_nonneg' k X hX := by
    let T := hilbertMatrix (X.map m.operatorMean.toLinearMap)
    have hp : T.IsPositive := by
      rw [ContinuousLinearMap.isPositive_iff_complex]
      intro x
      let f : G →ᵇ ℂ := ∑ i, ∑ j, coefficient (X i j) (x j) (x i)
      have heval (g : G) : f g = inner ℂ x
          (hilbertMatrix (X.map (evaluationHom (H := H) g)) x) := by
        simp only [f, BoundedContinuousFunction.sum_apply, coefficient_apply,
          PiLp.inner_apply, hilbertMatrix_apply, CStarMatrix.map_apply,
          inner_sum]
        rfl
      have hpos : (m.toCLM f).im = 0 ∧ 0 ≤ (m.toCLM f).re :=
        m.positive f (fun g => by
          have hmat := map_nonneg
            (CStarMatrix.mapₙₐ (n := Fin k)
              (evaluationHom (H := H) g).toNonUnitalStarAlgHom) hX
          have hT := map_nonneg (hilbertMatrixHom (H := H) (n := Fin k)) hmat
          change (hilbertMatrix (X.map (evaluationHom (H := H) g)) - 0).IsPositive at hT
          rw [sub_zero] at hT
          have hs := (ContinuousLinearMap.isPositive_iff_complex _).mp hT x
          rw [heval]
          have hi : inner ℂ x (hilbertMatrix (X.map (evaluationHom (H := H) g)) x) =
              star (inner ℂ (hilbertMatrix (X.map (evaluationHom (H := H) g)) x) x) :=
            (inner_conj_symm _ _).symm
          rw [hi, ← hs.1]
          simpa using (show (0 : ℝ) = 0 ∧ 0 ≤
            (inner ℂ (hilbertMatrix (X.map (evaluationHom (H := H) g)) x) x).re
            from ⟨rfl, hs.2⟩))
      have hmean : inner ℂ x (T x) = m.toCLM f := by
        simp only [T, PiLp.inner_apply, hilbertMatrix_apply,
          CStarMatrix.map_apply, inner_sum]
        change (∑ i, ∑ j, inner ℂ (x i) (m.operatorMean (X i j) (x j))) = _
        simp_rw [m.inner_operatorMean]
        simp only [f, map_sum]
      have hi : inner ℂ (T x) x = m.toCLM f := by
        rw [← inner_conj_symm, hmean]
        apply Complex.ext <;> simp [hpos.1]
      rw [hi]
      exact ⟨by apply Complex.ext <;> simp [hpos.1], hpos.2⟩
    apply (NonUnitalStarAlgHom.map_le_map_iff
      (hilbertMatrixHom (H := H) (n := Fin k)) hilbertMatrixHom_injective).mp
    rw [map_zero]
    change (T - 0).IsPositive
    simpa only [sub_zero] using hp

theorem operatorMeanCP_one : m.operatorMeanCP (1 : G →ᵇ (H →L[ℂ] H)) = 1 :=
  m.operatorMean_const 1

def conjugationFamilyHom (U : G →* unitary (H →L[ℂ] H)) :
    (H →L[ℂ] H) →⋆ₐ[ℂ] (G →ᵇ (H →L[ℂ] H)) where
  toFun := conjugationFamily U
  map_one' := by
    apply BoundedContinuousFunction.ext
    intro g
    exact (Unitary.conjStarAlgAut ℂ _ (U g)).toStarAlgHom.map_one
  map_mul' S T := by
    apply BoundedContinuousFunction.ext
    intro g
    exact (Unitary.conjStarAlgAut ℂ _ (U g)).toStarAlgHom.map_mul S T
  map_zero' := by
    apply BoundedContinuousFunction.ext
    intro g
    exact (Unitary.conjStarAlgAut ℂ _ (U g)).toStarAlgHom.map_zero
  map_add' S T := by
    apply BoundedContinuousFunction.ext
    intro g
    exact (Unitary.conjStarAlgAut ℂ _ (U g)).toStarAlgHom.map_add S T
  commutes' c := by
    apply BoundedContinuousFunction.ext
    intro g
    exact (Unitary.conjStarAlgAut ℂ _ (U g)).toStarAlgHom.commutes c
  map_star' S := by
    apply BoundedContinuousFunction.ext
    intro g
    exact StarHomClass.map_star (Unitary.conjStarAlgAut ℂ _ (U g)).toStarAlgHom S

/-- The unital completely positive invariant average of conjugates. -/
def averageConjugation (U : G →* unitary (H →L[ℂ] H)) :
    (H →L[ℂ] H) →CP (H →L[ℂ] H) where
  toLinearMap := m.operatorMean.toLinearMap.comp (conjugationFamilyHom U).toAlgHom.toLinearMap
  map_cstarMatrix_nonneg' k X hX := by
    have h := m.operatorMeanCP.map_cstarMatrix_nonneg
      (X.map (conjugationFamilyHom U))
      (CompletelyPositiveMapClass.map_cstarMatrix_nonneg' (conjugationFamilyHom U) k X hX)
    exact h

/-- The scalar construction supplies the precise bimodule mean used by
the already proved boundary correction. -/
def bimoduleMean : BimoduleMean (boundaryConstant (G := G) (B := H →L[ℂ] H)) where
  toCLM := m.operatorMean
  map_one := m.operatorMeanCP_one
  map_star F := completelyPositive_map_star m.operatorMeanCP F
  norm_le := m.norm_operator_le
  map_left := m.operatorMean_left
  map_right F T := m.operatorMean_right T F

end ScalarInvariantMean

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_AbelianInvariantMean
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A scalar invariant mean for every discrete abelian group

Finite iterated Cesaro averages give a positive, unital, contractive
family of scalar functionals. An ultrafilter extending the directed
finite-set/length filter gives a simultaneous scalar limit. The explicit
telescoping bound proves invariance. This constructs the mean used for
the real modular and character groups without an amenability premise.
-/

namespace KadisonKastler

open Filter
open scoped Topology BigOperators BoundedContinuousFunction

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [DiscreteTopology G]

/-- An actual invariant scalar mean on every discrete abelian group. -/
def abelianScalarInvariantMean (G : Type*) [CommGroup G]
    [TopologicalSpace G] [DiscreteTopology G] : ScalarInvariantMean G where
  toCLM := LinearMap.mkContinuous
    { toFun := abelianMeanValue
      map_add' := abelianMeanValue_add
      map_smul' := abelianMeanValue_smul }
    1 (fun f => by
      change ‖abelianMeanValue f‖ ≤ 1 * ‖f‖
      simpa only [one_mul] using norm_abelianMeanValue f)
  map_const_one := abelianMeanValue_const 1
  norm_le := norm_abelianMeanValue
  positive := abelianMeanValue_positive
  invariant := abelianMeanValue_invariant

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCoreOperators
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Operators on the actual regular Hilbert space

The regular core acts on `L²(ℝ,H)`, with a constant operator
representation and multiplication by a measurable unitary
field. The latter gives the gauge transformation used to write the core
embedding as a faithful conjugate of the constant representation.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section

variable {D H : Type*} [MeasurableSpace D]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem regularUnitaryField_apply_ae (μ : Measure D)
    (U : D → unitary (H →L[ℂ] H))
    (hU : ∀ x, AEStronglyMeasurable (fun t => (U t : H →L[ℂ] H) x) μ)
    (hUs : ∀ x, AEStronglyMeasurable (fun t => (star (U t) : H →L[ℂ] H) x) μ)
    (f : Lp H 2 μ) :
    (regularUnitaryField μ U hU hUs : Lp H 2 μ →L[ℂ] Lp H 2 μ) f =ᵐ[μ]
      fun t => (U t : H →L[ℂ] H) (f t) :=
  regularUnitaryFieldApply_ae μ U hU f

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PublishedCentralDecomposition
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The published common central decomposition input

Blackadar, *Operator Algebras* (Springer, 2006), III.1.6.2--4 and
III.5.1.10--14: central decomposition on separable Hilbert space,
simultaneous decomposition of norm-separable C-star subalgebras, and
reconstruction of bounded measurable fields. The common C-star algebra is
required to commute with the common center so that it is decomposable. The dimension strata are
trivialized over standard Borel spaces with finite measures.

Only this structural input is retained. In particular, the proposition
below contains no distance estimate, implementer or stability conclusion.
-/

namespace KadisonKastler

open MeasureTheory TopologicalSpace

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The central case of the cited decomposition and reconstruction results,
for one pair and one chosen norm-separable common C-star algebra. -/
def PublishedCentralPairDecomposition : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [SeparableSpace H], ∀ (M N : VonNeumannAlgebra H), concreteCenter M = concreteCenter N →
    ∀ (A B C : StarSubalgebra ℂ (H →L[ℂ] H)),
      IsClosed (A : Set (H →L[ℂ] H)) → IsClosed (B : Set (H →L[ℂ] H)) →
      IsClosed (C : Set (H →L[ℂ] H)) →
      IsSeparable (A : Set (H →L[ℂ] H)) → IsSeparable (B : Set (H →L[ℂ] H)) →
      IsSeparable (C : Set (H →L[ℂ] H)) →
      generatedVonNeumannAlgebra A = M → generatedVonNeumannAlgebra B = N →
      ∀ (hAC : A ≤ C) (hBC : B ≤ C),
      C ≤ (concreteCenter M).commutant.toStarSubalgebra →
      Nonempty (CentralPairDecomposition M N A B C hAC hBC)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCoreCharacters
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instOne _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Character multiplication in the regular core representation

The operators `Q_a` are actual multiplication unitaries on `L²(ℝ,H)`.
Their covariance with translations and their commutation with `π(B(H))`
are proved on representatives. These are the generator identities in
the dual-character argument of Section 8.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem regularCharacterUnitary_apply_ae (a : ℝ) (f : RegularCoreHilbert H) :
    (regularCharacterUnitary (H := H) a : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f =ᵐ[volume]
      fun t : ℝ => regularCharacterScalar a t • f t := by
  exact regularUnitaryField_apply_ae volume _ _ _ f

theorem regularCharacterUnitary_zero :
    regularCharacterUnitary (H := H) 0 = 1 := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [regularCharacterUnitary_apply_ae 0 f] with t ht
  change (regularCharacterUnitary (H := H) 0 :
    RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f t = f t
  simpa only [regularCharacterScalar, zero_mul, Circle.exp_zero, Circle.coe_one,
    one_smul, one_apply_eq_self] using ht

theorem regularCharacterUnitary_add (a b : ℝ) :
    regularCharacterUnitary (H := H) (a + b) =
      regularCharacterUnitary (H := H) a * regularCharacterUnitary (H := H) b := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [regularCharacterUnitary_apply_ae (a + b) f,
    regularCharacterUnitary_apply_ae a
      ((regularCharacterUnitary (H := H) b : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f),
    regularCharacterUnitary_apply_ae b f] with t hab ha hb
  change (regularCharacterUnitary (H := H) (a + b) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f t =
    (regularCharacterUnitary (H := H) a : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      ((regularCharacterUnitary (H := H) b : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f) t
  rw [hab, ha, hb, regularCharacterScalar_add_left, mul_smul]

/-- The actual unitary representation defining the dual-character action. -/
def regularCharacterRepresentation : Multiplicative ℝ →* unitary
    (RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) where
  toFun a := regularCharacterUnitary (H := H) a.toAdd
  map_one' := regularCharacterUnitary_zero
  map_mul' a b := regularCharacterUnitary_add a.toAdd b.toAdd

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CharacterAverageDescent
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Descent by the character-action average

The concrete crossed-product representation identifies the joint fixed
algebra with the embedded original algebra. Once that actual identity is
available, the scalar character mean supplies the UCP map required for
descent. No statement that its entire ambient range is embedded is used.
-/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

section Descent

universe u v w s

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {G : Type w} [Group G] {L : Type s} [Group L]
  [TopologicalSpace L] [DiscreteTopology L]
  {M N : VonNeumannAlgebra H}

attribute [local instance] OAI.KadisonKastler.characterDescentOperatorOrder
attribute [local instance] OAI.KadisonKastler.characterDescentOperatorStarOrder
local instance characterDescentFactorOrder_r660896_1 (P : VonNeumannAlgebra H) :
    PartialOrder (Algebra P) := CStarAlgebra.spectralOrder _
local instance characterDescentFactorStarOrder_r660896_1 (P : VonNeumannAlgebra H) :
    StarOrderedRing (Algebra P) := CStarAlgebra.spectralOrderedRing _
/-- The same proved average, expressed with the spectral-order instances
used by the descent criterion. Its matrix positivity is unchanged. -/
def characterAverage (m : ScalarInvariantMean L) (V : L →* unitary (K →L[ℂ] K)) :
    (K →L[ℂ] K) →CP (K →L[ℂ] K) where
  toLinearMap := by
    letI : PartialOrder (K →L[ℂ] K) := ContinuousLinearMap.instLoewnerPartialOrder
    letI : StarOrderedRing (K →L[ℂ] K) := ContinuousLinearMap.instStarOrderedRing
    exact (m.averageConjugation V).toLinearMap
  map_cstarMatrix_nonneg' n X hX := by
    let : PartialOrder (K →L[ℂ] K) := ContinuousLinearMap.instLoewnerPartialOrder
    let : StarOrderedRing (K →L[ℂ] K) := ContinuousLinearMap.instStarOrderedRing
    exact (m.averageConjugation V).map_cstarMatrix_nonneg X hX

end Descent

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCoreDensePeriods
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Dense periods of bounded regular coefficient fields

Strong continuity of translations on the actual `L²` space extends
commutation from any dense family of translations to all translations.
Consequently a bounded measurable field with dense periods is constant
almost everywhere. In particular, two incommensurable scalar periods
suffice, as required by the two-frequency modular-core argument.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Topology ENNReal

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
/-- Real translations are strongly continuous on the actual regular
Hilbert space. -/
theorem continuous_regularTranslateApply (f : RegularCoreHilbert H) :
    Continuous (fun s : ℝ => regularTranslateApply s f) := by
  let g : ℝ → C(ℝ, ℝ) := fun s => ⟨fun t => t + s, continuous_id.add continuous_const⟩
  have hg : Continuous g :=
    ContinuousMap.continuous_of_continuous_uncurry g (continuous_snd.add continuous_fst)
  have hc := (continuous_const : Continuous (fun _ : ℝ => f)).compMeasurePreservingLp
    hg (fun s => measurePreserving_add_right (volume : Measure ℝ) s) (by norm_num : (2 : ENNReal) ≠ ⊤)
  exact hc

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FrequencyNest
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The concrete Fourier frequency projections

The Fourier transform uses mathlib's `exp(-2*pi*i*t*ξ)` convention.
Thus the cut of the generator `-i d/dt` at `a` is the Fourier multiplier
of `Ioi (a/(2*pi))`. The upper frequency cuts decrease with `a`; negating
the index gives the increasing chain used by the nest distance theorem.
-/

namespace KadisonKastler

open MeasureTheory
open scoped FourierTransform

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem regularFrequencyProjection_apply_fourier (a : ℝ) (f : RegularCoreHilbert H) :
    (𝓕 (regularFrequencyProjection a f) : RegularCoreHilbert H) =ᵐ[volume]
      (Set.Ioi (a / (2 * Real.pi))).indicator (𝓕 f : RegularCoreHilbert H) := by
  change (Lp.fourierTransformₗᵢ ℝ H)
    ((Lp.fourierTransformₗᵢ ℝ H).symm
      (regularIndicatorProjection (Set.Ioi (a / (2 * Real.pi))) measurableSet_Ioi
        ((Lp.fourierTransformₗᵢ ℝ H) f))) =ᵐ[volume] _
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact regularIndicatorProjection_apply_ae _ _ _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FourierModulation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
attribute [local instance] OAI.circleMeasurableSpace OAI.circleBorelSpace

namespace OAI

/-! # Fourier transforms of scalar character multipliers

The identity is established on Schwartz functions by the integral
formula, then on the actual `L²` space by density.
-/

namespace KadisonKastler

open MeasureTheory
open scoped FourierTransform

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem modulatedSchwartz_toLp (s : ℝ) (f : SchwartzMap ℝ H) :
    (modulatedSchwartz s f).toLp 2 =
      (regularCharacterUnitary (H := H) (2 * Real.pi * s) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (f.toLp 2) := by
  apply Lp.ext
  filter_upwards [(modulatedSchwartz s f).coeFn_toLp 2, f.coeFn_toLp 2,
    regularCharacterUnitary_apply_ae (2 * Real.pi * s) (f.toLp 2)] with t h₁ h₂ h₃
  rw [h₁, h₃, h₂, modulatedSchwartz_apply]

theorem fourier_modulate_schwartz (s : ℝ) (f : SchwartzMap ℝ H) :
    (𝓕 ((regularCharacterUnitary (H := H) (2 * Real.pi * s) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (f.toLp 2)) : RegularCoreHilbert H) =
    regularTranslateApply (-s) (𝓕 (f.toLp 2)) := by
  rw [← modulatedSchwartz_toLp, SchwartzMap.toLp_fourier_eq,
    SchwartzMap.toLp_fourier_eq]
  apply Lp.ext
  filter_upwards [(𝓕 (modulatedSchwartz s f)).coeFn_toLp 2,
    regularTranslateApply_ae (-s) ((𝓕 f).toLp 2),
    (measurePreserving_add_right volume (-s)).quasiMeasurePreserving.ae_eq_comp
      ((𝓕 f).coeFn_toLp 2)] with t h₁ h₂ h₃
  simp only [Function.comp_def] at h₃
  rw [h₁, h₂, h₃]
  rw [SchwartzMap.fourier_coe]
  have he : (modulatedSchwartz s f : ℝ → H) =
      fun t => regularCharacterScalar (2 * Real.pi * s) t • f t :=
    funext fun t => modulatedSchwartz_apply s t f
  rw [he]
  simpa only [sub_eq_add_neg, SchwartzMap.fourier_coe] using fourier_modulate_function s f t

/-- Multiplication by the scalar character translates Fourier frequency. -/
theorem fourier_regularCharacterUnitary (s : ℝ) (f : RegularCoreHilbert H) :
    (𝓕 ((regularCharacterUnitary (H := H) (2 * Real.pi * s) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f) : RegularCoreHilbert H) =
    regularTranslateApply (-s) (𝓕 f) := by
  let F : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H := Lp.fourierTransformₗᵢ ℝ H
  let T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H := (regularTranslationEquiv (H := H) (-s) :
    RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
  let C : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H :=
    regularCharacterUnitary (H := H) (2 * Real.pi * s)
  have he : F.comp C = T.comp F := by
    apply DFunLike.coe_injective
    apply (SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := H)
      (p := 2) ENNReal.ofNat_ne_top).equalizer
      (F.comp C).continuous (T.comp F).continuous
    funext g
    exact fourier_modulate_schwartz s g
  exact congrArg (fun A : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H => A f) he

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CharacterContinuity
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Continuous character fields in the scalar spectral variable -/

namespace KadisonKastler

open MeasureTheory
open scoped FourierTransform

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem regularCharacter_apply_eq_fourier_translate (a : ℝ) (f : RegularCoreHilbert H) :
    (regularCharacterUnitary (H := H) a : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f =
      (Lp.fourierTransformₗᵢ ℝ H).symm (regularTranslateApply (-(a / (2 * Real.pi))) (𝓕 f)) := by
  apply (Lp.fourierTransformₗᵢ ℝ H).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  have ha : 2 * Real.pi * (a / (2 * Real.pi)) = a := by field_simp
  have h := fourier_regularCharacterUnitary (a / (2 * Real.pi)) f
  change (Lp.fourierTransformₗᵢ ℝ H) ((regularCharacterUnitary (H := H)
    (2 * Real.pi * (a / (2 * Real.pi))) : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f) = _ at h
  rwa [ha] at h

theorem continuous_regularCharacterUnitary (f : RegularCoreHilbert H) :
    Continuous (fun a : ℝ => (regularCharacterUnitary (H := H) a :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f) := by
  simp_rw [regularCharacter_apply_eq_fourier_translate]
  exact (Lp.fourierTransformₗᵢ ℝ H).symm.continuous.comp
    ((continuous_regularTranslateApply (𝓕 f)).comp (by fun_prop))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SpectralCommutant
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Spectral commutation for real character multipliers

Character commutation passes to every unitary of their commutant.
Finite vector measures then give scalar-multiplier commutation, and
the linear span of unitaries gives the assertion for every operator.
-/

namespace KadisonKastler

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The closed C-star algebra commuting with all real character multipliers. -/
def characterCommutant :
    StarSubalgebra ℂ (RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) :=
  StarSubalgebra.centralizer ℂ (Set.range fun a : ℝ =>
    (regularCharacterUnitary (H := H) a :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H))

instance characterCommutantCStarAlgebra : CStarAlgebra (characterCommutant (H := H)) :=
  StarSubalgebra.cstarAlgebra _ (h_closed := Set.isClosed_centralizer _)

theorem characterCommutant_unitary_commutes
    (u : unitary (characterCommutant (H := H))) (a : ℝ) :
    Commute (((characterCommutant (H := H)).subtype u) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      (regularCharacterUnitary (H := H) a :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) :=
  (((StarSubalgebra.mem_centralizer_iff ℂ).mp u.val.property) _ ⟨a, rfl⟩).1.symm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ShiftedFrequencyFields
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Measurable fields of shifted Fourier cuts -/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem star_regularCharacterUnitary (a : ℝ) :
    star (regularCharacterUnitary (H := H) a) = regularCharacterUnitary (H := H) (-a) :=
  regularGroup_star_eq (regularCharacterRepresentation (H := H)) a

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CyclicGaugeKernel
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The cyclic gauge as a field of scalar characters

Interchanging the time and spectral variables turns the cyclic modular
gauge into ordinary character multiplication in each spectral fiber.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

section CharacterField

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) (l : X → ℝ) (hl : Measurable l)

include hl

theorem characterField_measurable (f : RegularCoreHilbert ℂ) :
    AEStronglyMeasurable (fun s => (regularCharacterUnitary (H := ℂ) (l s) :
      RegularCoreHilbert ℂ →L[ℂ] RegularCoreHilbert ℂ) f) μ :=
  ((continuous_regularCharacterUnitary f).stronglyMeasurable.comp_measurable hl).aestronglyMeasurable

theorem characterField_star_measurable (f : RegularCoreHilbert ℂ) :
    AEStronglyMeasurable (fun s => (star (regularCharacterUnitary (H := ℂ) (l s)) :
      RegularCoreHilbert ℂ →L[ℂ] RegularCoreHilbert ℂ) f) μ := by
  have he (s : X) : star (regularCharacterUnitary (H := ℂ) (l s)) =
      regularCharacterUnitary (H := ℂ) (-(l s)) :=
    regularGroup_star_eq (regularCharacterRepresentation (H := ℂ)) (l s)
  have he' : (fun s => (star (regularCharacterUnitary (H := ℂ) (l s)) :
      RegularCoreHilbert ℂ →L[ℂ] RegularCoreHilbert ℂ) f) =
      (fun s => (regularCharacterUnitary (H := ℂ) (-(l s)) :
        RegularCoreHilbert ℂ →L[ℂ] RegularCoreHilbert ℂ) f) := by
    funext s
    exact congrArg (fun u : unitary (RegularCoreHilbert ℂ →L[ℂ] RegularCoreHilbert ℂ) =>
      (u : RegularCoreHilbert ℂ →L[ℂ] RegularCoreHilbert ℂ) f) (he s)
  rw [he']
  exact ((continuous_regularCharacterUnitary f).stronglyMeasurable.comp_measurable hl.neg).aestronglyMeasurable

end CharacterField

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_AdjustedCornerState
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A faithful normal state with a prescribed tracial corner vector -/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

def adjustedCornerVector (p : AlgebraProjection M) (Ω η : H) : WithLp 2 (H × H) :=
  WithLp.toLp 2 (η, (1 - p.val.val) Ω)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_AlgebraCocycleRepresentatives
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Algebra-valued representatives of an almost-everywhere cocycle

An ambient unitary lying in a von Neumann algebra is a unitary of that
algebra. Replacing exceptional values by one therefore makes the entire
family algebra-valued without changing any measurable or cocycle data.
-/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {G D : Type*}

/-- Replace the exceptional values of an ambient unitary family by one. -/
def algebraCocycleRepresentative (M : VonNeumannAlgebra H)
    (W : G → D → unitary (H →L[ℂ] H)) (g : G) (x : D) : unitary (Algebra M) := by
  classical
  exact if hx : (W g x : H →L[ℂ] H) ∈ M then unitaryInAlgebra M (W g x) hx else 1

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RandomWalkIdentityBoundary
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The boundary law of a walk starting at the identity

The initial root law was chosen with full support. Starting at the identity
is absolutely continuous before taking the invariant factor; after one
increment its boundary law is exactly the chosen boundary probability.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory

variable (G : Type*) [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]

def randomWalkFromIdentity (ω : ℕ → G) : RandomWalkPath G := (1, ω)

def randomWalkIdentityBoundary (ω : ℕ → G) : RandomWalkBoundary G :=
  shiftBoundaryMap (randomWalkPathLaw G) (randomWalkAdvance G) (randomWalkFromIdentity G ω)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BilateralBoundaryPair
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The two boundary endpoints of a bilateral random walk

The forward and reflected backward halves have the exact boundary product
law. Every integer shift preserves the bilateral path probability.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory ProbabilityTheory

variable (G : Type*) [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]

def bilateralPositiveBoundary (ω : BilateralWalkPath G) : RandomWalkBoundary G :=
  randomWalkIdentityBoundary G (bilateralFuture G ω)

def bilateralNegativeBoundary (ω : BilateralWalkPath G) : RandomWalkBoundary G :=
  randomWalkIdentityBoundary G (bilateralReflectedPast G ω)

def bilateralBoundaryPair (ω : BilateralWalkPath G) : RandomWalkBoundary G × RandomWalkBoundary G :=
  (bilateralPositiveBoundary G ω, bilateralNegativeBoundary G ω)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BoundaryPairInvariance
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! Hilbert-valued boundary functions are invariant under advancing either path. -/

namespace KadisonKastler

noncomputable section

open MeasureTheory

variable {X Y K : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {S : X → X} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [TopologicalSpace.SeparableSpace K]

variable {f : ShiftBoundarySpace μ S × ShiftBoundarySpace μ S → K}

def boundaryPairLift (f : ShiftBoundarySpace μ S × ShiftBoundarySpace μ S → K)
    (z : X × X) : K := f (shiftBoundaryMap μ S z.1, shiftBoundaryMap μ S z.2)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BilateralBoundaryTransport
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! The boundary pair transforms by the inverse increment under a bilateral shift.

The boundary uses an invariant sigma algebra, not a point quotient. Its endpoint
identities are therefore proved on measurable Hilbert-valued functions.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory ProbabilityTheory

variable (G : Type*) [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]

def bilateralTransportPairAt (g : G) (ω : BilateralWalkPath G) :
    RandomWalkPath G × RandomWalkPath G :=
  ((g⁻¹, bilateralFuture G ω), (1, randomWalkPrepend G g⁻¹ (bilateralReflectedPast G ω)))

def bilateralTransportPair (ω : BilateralWalkPath G) : RandomWalkPath G × RandomWalkPath G :=
  bilateralTransportPairAt G (ω 0) ω

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SubalgebraInvariantMean
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.varyingSequenceCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Restricting an invariant operator mean to a von Neumann algebra

The coefficient construction preserves every von Neumann algebra. Restricting
its domain and codomain therefore gives the exact mean for internal unitary
correction, without a normality or injectivity assumption on the target.
-/

namespace KadisonKastler

open scoped BoundedContinuousFunction

noncomputable section

variable {G H : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace ScalarInvariantMean

variable (m : ScalarInvariantMean G) (N : VonNeumannAlgebra H)

attribute [local instance] OAI.KadisonKastler.subalgebraFamilyCStar
theorem algebraMean_norm_le (F : G →ᵇ Algebra N) : ‖m.algebraMean N F‖ ≤ ‖F‖ :=
  (m.norm_operator_le _).trans (norm_ambientAlgebraFamily_le N F)

theorem algebraMean_const (b : Algebra N) :
    m.algebraMean N (boundaryConstant b) = b := by
  apply Subtype.ext
  exact m.operatorMean_const b.val

theorem algebraMean_star (F : G →ᵇ Algebra N) :
    m.algebraMean N (star F) = star (m.algebraMean N F) := by
  apply Subtype.ext
  change m.operatorMean (ambientAlgebraFamily N (star F)) =
    star (m.operatorMean (ambientAlgebraFamily N F))
  rw [map_star]
  exact m.bimoduleMean.map_star _

theorem algebraMean_left (b : Algebra N) (F : G →ᵇ Algebra N) :
    m.algebraMean N (boundaryConstant b * F) = b * m.algebraMean N F := by
  apply Subtype.ext
  exact m.operatorMean_left b.val (ambientAlgebraFamily N F)

theorem algebraMean_right (F : G →ᵇ Algebra N) (b : Algebra N) :
    m.algebraMean N (F * boundaryConstant b) = m.algebraMean N F * b := by
  apply Subtype.ext
  exact m.operatorMean_right b.val (ambientAlgebraFamily N F)

/-- The algebra-valued mean satisfies the two module identities. -/
def algebraBimoduleMean : BimoduleMean (boundaryConstant (G := G) (B := Algebra N)) where
  toCLM := m.algebraMean N
  map_one := m.algebraMean_const N 1
  map_star := m.algebraMean_star N
  norm_le := m.algebraMean_norm_le N
  map_left := m.algebraMean_left N
  map_right := m.algebraMean_right N

end ScalarInvariantMean

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SeparableReduction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Reduction of the universal theorem to separable Hilbert spaces

Local restrictions to separable reducing spaces give finite coefficient
approximants and then a conjugacy on the original Hilbert space.
The tolerance precedes every ambient space.
-/

namespace KadisonKastler

open TopologicalSpace

noncomputable section

universe u

local instance reductionFactorOrder_r660896_1 {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (M : VonNeumannAlgebra H) :
    PartialOrder (Algebra M) := CStarAlgebra.spectralOrder _
local instance reductionFactorStarOrder_r660896_1 {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (M : VonNeumannAlgebra H) :
    StarOrderedRing (Algebra M) := CStarAlgebra.spectralOrderedRing _
/-- The separable-Hilbert-space intermediate conclusion of §9. -/
def SeparableStrongStability : Prop :=
  ∀ a : ℝ, 0 < a → ∃ δ : ℝ, 0 < δ ∧
    ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] [SeparableSpace H], ∀ M N : VonNeumannAlgebra H,
        kkDistance M N < δ → NearConjugacy M N a

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CommonCenterFromFactors
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The common-center reduction to the uniform factor theorem

Uniform stability of factors passes to algebras with a common center
by constructing nearby separable test algebras, bounding their fibers,
and assembling the factor implementers.
-/

namespace KadisonKastler

open MeasureTheory TopologicalSpace

noncomputable section

universe u

local instance instPartialOrderSubtypeContinuousLinearMapComplexIdMemStarSubalgebraAlgebra_3_r660896_1 {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (M : VonNeumannAlgebra H) : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance instStarOrderedRingSubtypeContinuousLinearMapComplexIdMemStarSubalgebraAlgebra_3_r660896_1 {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (M : VonNeumannAlgebra H) : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _
/-- Factor stability with a tolerance independent of the
represented factors. Zero-dimensional representations are allowed. -/
def UniformFactorStability : Prop :=
  ∀ a : ℝ, 0 < a → ∃ δ : ℝ, 0 < δ ∧
    ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] [SeparableSpace H], ∀ M N : VonNeumannAlgebra H,
        ScalarCenter M → ScalarCenter N → kkDistance M N < δ → NearConjugacy M N a

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ConjugationAveragedState
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Invariant states obtained by the constructed scalar mean

The scalar orbit of the state is averaged, so every invariant restriction
is preserved even when the state is not normal. Strong invariance under
probability-measure averages is a separate step.
-/

namespace KadisonKastler

open NaimarkZFC
open scoped ComplexOrder BoundedContinuousFunction

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [DiscreteTopology G]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace ScalarInvariantMean

variable (m : ScalarInvariantMean G) (U : G →* unitary (H →L[ℂ] H))

def stateOrbitScalar (φ : (H →L[ℂ] H) →L[ℂ] ℂ) (T : H →L[ℂ] H) : G →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun g => φ (unitaryConj (U g) T)) (‖φ‖*‖T‖) (fun g =>
      (φ.le_opNorm _).trans_eq (by rw [norm_unitaryConj]))

@[simp] theorem stateOrbitScalar_apply (φ : (H →L[ℂ] H) →L[ℂ] ℂ)
    (T : H →L[ℂ] H) (g : G) : stateOrbitScalar U φ T g=φ (unitaryConj (U g) T) := rfl

def stateOrbitMap (φ : (H →L[ℂ] H) →L[ℂ] ℂ) :
    (H →L[ℂ] H) →L[ℂ] (G →ᵇ ℂ) :=
  LinearMap.mkContinuous
    { toFun := stateOrbitScalar U φ
      map_add' S T := by
        ext g
        change φ ((Unitary.conjStarAlgAut ℂ _ (U g)) (S+T)) =
          φ ((Unitary.conjStarAlgAut ℂ _ (U g)) S)+φ ((Unitary.conjStarAlgAut ℂ _ (U g)) T)
        rw [map_add,map_add]
      map_smul' c T := by
        ext g
        change φ ((Unitary.conjStarAlgAut ℂ _ (U g)) (c • T)) = c • φ _
        rw [map_smul,map_smul]
        rfl }
    ‖φ‖ (fun T => (BoundedContinuousFunction.norm_le (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
      (fun g => (φ.le_opNorm _).trans_eq (by rw [norm_unitaryConj])))

def averagedState (φ : (H →L[ℂ] H) →L[ℂ] ℂ) : (H →L[ℂ] H) →L[ℂ] ℂ :=
  m.toCLM.comp (stateOrbitMap U φ)

@[simp] theorem averagedState_apply (φ : (H →L[ℂ] H) →L[ℂ] ℂ)
    (T : H →L[ℂ] H) : m.averagedState U φ T = m.toCLM (stateOrbitScalar U φ T) := rfl

end ScalarInvariantMean

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_HardyCauchyBoundary
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Boundary formula for the Hardy reproducing kernel -/

namespace KadisonKastler

open MeasureTheory FourierTransform

noncomputable section

theorem hardyCauchyFunction_memLp {z : ℂ} (hz : 0 < z.re) :
    MemLp (hardyCauchyFunction z) 2 := by
  have h := (cauchyResolvent_memLp hz).comp_measurePreserving
    (Measure.measurePreserving_neg (volume : Measure ℝ))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext s
  dsimp [hardyCauchyFunction, Function.comp_def]
  congr 1
  push_cast
  ring

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_L2MeasurableExtension
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Extension by zero from a measurable L² stratum -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H]
  (μ : Measure X) (s : Set X) (hs : MeasurableSet s)

variable [NormedSpace ℂ H]

omit [NormedSpace ℂ H] in
theorem l2Extend_add (f g : Lp H 2 (Measure.comap ((↑) : s → X) μ)) :
    l2Extend μ s hs (f + g) = l2Extend μ s hs f + l2Extend μ s hs g := by
  apply Lp.ext
  filter_upwards [l2Extend_apply_ae μ s hs (f + g), l2Extend_apply_ae μ s hs f,
    l2Extend_apply_ae μ s hs g,
    Lp.coeFn_add (l2Extend μ s hs f) (l2Extend μ s hs g),
    l2ExtensionFunction_add_ae μ s hs f g] with x hfg hf hg ha he
  simp only [Pi.add_apply] at ha
  rw [hfg, ha, hf, hg]
  exact he

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ScalarMeanStar
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.ScalarOperatorKernel.toContinuous_apply _root_.OAI.KadisonKastler.UniformMeasurableOperators.coefficientFamily_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Conjugation preservation of the scalar boundary mean

Positivity preserves real sections after adding a sufficiently large
constant. Applying this to the real and imaginary parts proves that the
complex-linear scalar mean commutes with conjugation.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped BoundedContinuousFunction

noncomputable section

variable {D G : Type*} [MeasurableSpace D] {μ : Measure D}
  [TopologicalSpace G] [DiscreteTopology G] [IsFiniteMeasure μ]

/-- Conjugating a scalar L-infinity class does not enlarge its norm. -/
theorem scalarInfinity_norm_star_le (f : ScalarLInfinity μ) : ‖star f‖ ≤ ‖f‖ := by
  have hb : ∀ᵐ x ∂μ, ‖(star f : ScalarLInfinity μ) x‖ ≤ ‖f‖ := by
    filter_upwards [Lp.coeFn_star f, scalarInfinity_ae_norm_le f] with x hx hf
    simpa only [Pi.star_apply, hx, norm_star] using hf
  simpa using Lp.norm_le_of_ae_bound (norm_nonneg f) hb

/-- Coordinatewise conjugation on the bounded family of scalar sections. -/
def scalarBoundaryStar (F : G →ᵇ ScalarLInfinity μ) : G →ᵇ ScalarLInfinity μ :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun g => star (F g)) ‖F‖ (fun g =>
      (scalarInfinity_norm_star_le (F g)).trans (F.norm_coe_le_norm g))

@[simp]
theorem scalarBoundaryStar_apply (F : G →ᵇ ScalarLInfinity μ) (g : G) :
    scalarBoundaryStar F g = star (F g) := rfl

theorem scalarBoundaryStar_ae (F : G →ᵇ ScalarLInfinity μ) (g : G) :
    scalarBoundaryStar F g =ᵐ[μ] fun x => star (F g x) := by
  exact (Lp.coeFn_star (F g)).mono fun x hx => by
    change (star (F g) : ScalarLInfinity μ) x = star (F g x)
    exact hx

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SpatialRightSlice
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Right-leg slices and the relative commutant of a product centralizer -/

namespace KadisonKastler

open UnitalTomsWinter
open scoped TensorProduct InnerProductSpace

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- A second-leg commutant element commutes with the entire spatial product. -/
theorem spatialRight_commutes_product (M : VonNeumannAlgebra H) (D : VonNeumannAlgebra K)
    (b : K →L[ℂ] K) (hb : b ∈ D.commutant)
    (T : SpatialHilbert H K →L[ℂ] SpatialHilbert H K) (hT : T ∈ spatialProductAlgebra M D) :
    spatialRight b * T = T * spatialRight b := by
  let A : StarSubalgebra ℂ (SpatialHilbert H K →L[ℂ] SpatialHilbert H K) :=
    (M.toStarSubalgebra.map (spatialLeft (H := H) (K := K))) ⊔
      (D.toStarSubalgebra.map (spatialRight (H := H) (K := K)))
  have hA : A ≤ StarSubalgebra.centralizer ℂ {spatialRight (H := H) b} := by
    apply sup_le
    · rintro _ ⟨x, hx, rfl⟩
      rw [StarSubalgebra.mem_centralizer_iff]
      intro g hg
      have hg' : g = spatialRight (H := H) b := Set.mem_singleton_iff.mp hg
      subst g
      constructor
      · exact (Pureness.spatialLeftRight_commute (StarAlgHom.id ℂ (H →L[ℂ] H))
          (StarAlgHom.id ℂ (K →L[ℂ] K)) x b).eq.symm
      · rw [← map_star]
        exact (Pureness.spatialLeftRight_commute (StarAlgHom.id ℂ (H →L[ℂ] H))
          (StarAlgHom.id ℂ (K →L[ℂ] K)) x (star b)).eq.symm
    · rintro _ ⟨x, hx, rfl⟩
      rw [StarSubalgebra.mem_centralizer_iff]
      intro g hg
      have hg' : g = spatialRight (H := H) b := Set.mem_singleton_iff.mp hg
      subst g
      constructor
      · change spatialRight (H := H) b * spatialRight (H := H) x =
          spatialRight (H := H) x * spatialRight (H := H) b
        simpa only [map_mul] using (congrArg (spatialRight (H := H))
          (VonNeumannAlgebra.mem_commutant_iff.mp hb x hx)).symm
      · change star (spatialRight (H := H) b) * spatialRight (H := H) x =
          spatialRight (H := H) x * star (spatialRight (H := H) b)
        rw [← map_star]
        have hs := VonNeumannAlgebra.mem_commutant_iff.mp
          (D.commutant.toStarSubalgebra.star_mem' hb) x hx
        simpa only [map_mul] using (congrArg (spatialRight (H := H)) hs).symm
  have hRb : spatialRight (H := H) b ∈ Set.centralizer (A : Set _) := by
    intro x hx
    have hx' := hA hx
    rw [StarSubalgebra.mem_centralizer_iff] at hx'
    exact (hx' _ (Set.mem_singleton _)).1.symm
  change T ∈ generatedVonNeumannAlgebra A at hT
  change T ∈ (generatedVonNeumannAlgebra A : Set _) at hT
  rw [generatedVonNeumannAlgebra_coe] at hT
  exact hT _ hRb

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SpatialProductSeparating
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Separating product vectors

The modular conjugations on the two original spaces supply dense
commutant orbits. Their tensor product commutes with the generated
spatial algebra, so its cyclic product vector separates that algebra.
-/

namespace KadisonKastler

open UnitalTomsWinter

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem spatialProduct_commutants_le (M : VonNeumannAlgebra H) (D : VonNeumannAlgebra K) :
    spatialProductAlgebra M.commutant D.commutant ≤ (spatialProductAlgebra M D).commutant := by
  apply generatedVonNeumannAlgebra_le_of_le
  apply sup_le
  · rintro _ ⟨a, ha, rfl⟩
    apply VonNeumannAlgebra.mem_commutant_iff.mpr
    intro T hT
    exact (spatialLeft_commutes_product M D a ha T hT).symm
  · rintro _ ⟨b, hb, rfl⟩
    apply VonNeumannAlgebra.mem_commutant_iff.mpr
    intro T hT
    exact (spatialRight_commutes_product M D b hb T hT).symm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SpatialStrong
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Bounded strong continuity of the spatial right representation -/

namespace KadisonKastler

open UnitalTomsWinter Filter
open scoped TensorProduct Topology

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- A uniformly bounded strongly convergent family remains strongly
convergent after amplification in the right tensor leg. -/
theorem spatialRight_tendsto_strong
    {ι : Type*} {l : Filter ι} (T : ι → K →L[ℂ] K) (a : K →L[ℂ] K)
    {C : ℝ} (hT : ∀ i, ‖T i‖ ≤ C)
    (ha : ∀ y, Tendsto (fun i => T i y) l (𝓝 (a y)))
    (z : SpatialHilbert H K) :
    Tendsto (fun i => spatialRight (H := H) (T i) z) l
      (𝓝 (spatialRight (H := H) a z)) := by
  have hequi : Equicontinuous
      (fun i : ι => (spatialRight (H := H) (T i) : SpatialHilbert H K → SpatialHilbert H K)) := by
    apply Metric.equicontinuous_of_continuity_modulus (fun t : ℝ => C * t)
      (by simpa only [mul_zero] using
        (tendsto_const_nhds.mul tendsto_id :
          Tendsto (fun t : ℝ => C * t) (𝓝 0) (𝓝 (C * 0))))
    intro x y i
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    have hn : ‖spatialRight (H := H) (T i)‖ ≤ C := by
      calc
        _ ≤ ‖(1 : H →L[ℂ] H)‖ * ‖T i‖ := spatialTensorOp_norm_le _ _
        _ ≤ 1 * ‖T i‖ := mul_le_mul_of_nonneg_right
          (ContinuousLinearMap.norm_id_le : ‖(1 : H →L[ℂ] H)‖ ≤ 1) (norm_nonneg _)
        _ ≤ C := by simpa only [one_mul] using hT i
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right hn (norm_nonneg _))
  induction z using UniformSpace.Completion.induction_on with
  | hp => exact hequi.isClosed_setOfPred_tendsto (spatialRight (H := H) a).continuous
  | ih z =>
    induction z using OAI.tensorInductionOn with
    | tmul x y =>
      let L : K →L[ℂ] SpatialHilbert H K :=
        UniformSpace.Completion.toComplL.comp (TensorProduct.mkL ℂ H K x)
      have h := L.continuous.continuousAt.tendsto.comp (ha y)
      change Tendsto (fun i => ((x ⊗ₜ[ℂ] (T i y) : H ⊗[ℂ] K) : SpatialHilbert H K))
        l (𝓝 ((x ⊗ₜ[ℂ] (a y) : H ⊗[ℂ] K) : SpatialHilbert H K)) at h
      change Tendsto (fun i => spatialTensorOp (1 : H →L[ℂ] H) (T i) _) l
        (𝓝 (spatialTensorOp (1 : H →L[ℂ] H) a _))
      simpa only [spatialTensorOp_coe, TensorProduct.mapL_tmul, one_apply_eq_self] using h
    | add x y hx hy =>
      simpa only [map_add, UniformSpace.Completion.coe_add] using hx.add hy

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TypeIIISmallNormalizer
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Small exact normalizers of the type III factors used by stability

Sakai innerness, logarithms, simplicity, finite spectral centering, and
exponential factorization give small exact normalizers.
-/

namespace KadisonKastler

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

local instance smallNormalizerOrder_r660896_1 (P : VonNeumannAlgebra H) :
    PartialOrder (Algebra P) := CStarAlgebra.spectralOrder _
local instance smallNormalizerStarOrder_r660896_1 (P : VonNeumannAlgebra H) :
    StarOrderedRing (Algebra P) := CStarAlgebra.spectralOrderedRing _
/-- The local statement consumed by normalizer averaging. -/
def SmallNormalizerFactorization (P : VonNeumannAlgebra H) : Prop :=
  ∀ v : unitary (H →L[ℂ] H), Conjugates (H := H) v P P →
    ‖(v : H →L[ℂ] H) - 1‖ < 1 / 64 →
    ∃ a b : unitary (H →L[ℂ] H),
      (a : H →L[ℂ] H) ∈ P ∧ (b : H →L[ℂ] H) ∈ P.commutant ∧
      v = a * b ∧ ‖(a : H →L[ℂ] H) - 1‖ + ‖(b : H →L[ℂ] H) - 1‖ ≤
        10 * ‖(v : H →L[ℂ] H) - 1‖

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_WeakMapCompact
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! The completely bounded ball is compact in the pointwise weak operator topology. -/

namespace KadisonKastler

noncomputable section

open Filter
open scoped Topology InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] OAI.KadisonKastler.weakMapCompactOrder
attribute [local instance] OAI.KadisonKastler.weakMapCompactStarOrder
def boundedWeakAlgebraCoefficients {M : VonNeumannAlgebra H} {c : ℝ}
    (F : BoundedWeakAlgebraMap M c) (t : Algebra M × H × H) : ℂ :=
  inner ℂ t.2.2 ((F.map t.1 : H →L[ℂ] H) t.2.1)

instance boundedWeakAlgebraMapTopology (M : VonNeumannAlgebra H) (c : ℝ) :
    TopologicalSpace (BoundedWeakAlgebraMap M c) :=
  TopologicalSpace.induced boundedWeakAlgebraCoefficients inferInstance

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_WeakRowOrbit
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.varyingSequenceCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! Compact invariant weak closures of normalized finite-row orbits. -/

namespace KadisonKastler

noncomputable section

open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance weakRowOrbitOrder_r660896_1 (M : VonNeumannAlgebra H) : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance weakRowOrbitStarOrder_r660896_1 (M : VonNeumannAlgebra H) : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _
def boundedWeakRowOrbit {M : VonNeumannAlgebra H} {c : ℝ}
    (F : BoundedWeakAlgebraMap M c) : Set (BoundedWeakAlgebraMap M c) :=
  {G | G.map ∈ finiteRowOrbit F.map}

end

end KadisonKastler

end OAI
end


