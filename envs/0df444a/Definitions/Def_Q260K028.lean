-- Prove2me | Definitions.Def_Q260K028
-- name    : Q260K028
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T06:14:08.260713+00:00
-- url     : https://prove2.me/theorems/6a0da796-99f7-44ac-a05a-5f4b833ccd08
-- title:
--   Definitions bundle Q260K028 of the split of OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 53 declarations of OpenAI's Lean: 15 definitions, 3 instances and 35 theorems. The definitions and types are `OAI.KadisonKastler.SeparableSeeds.next`, `OAI.KadisonKastler.SeparableSeeds.stages`, `OAI.KadisonKastler.constantFieldRepresentation`, `OAI.KadisonKastler.firstBoundaryProjection`, `OAI.KadisonKastler.fourierShiftedField`, `OAI.KadisonKastler.hardyEvaluationAt`, `OAI.KadisonKastler.liftedRankCoordinates`, `OAI.KadisonKastler.measurableUnitaryRepresentative`, `OAI.KadisonKastler.normUltraproductInducedMap`, `OAI.KadisonKastler.randomWalkParameterizedScalarMean`, `OAI.KadisonKastler.randomWalkScalarBoundaryMean`, `OAI.KadisonKastler.randomWalkSecondScalarMean`, `OAI.KadisonKastler.regularCoreMonomials`, `OAI.KadisonKastler.scalarInvariantProjection`, `OAI.KadisonKastler.unitCoreFrequencyProjection`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `KadisonKastler_ConcreteTraceUniqueness`, `KadisonKastler_CoreFrequencyCuts`, `KadisonKastler_CoreFrequencyFinite`, `KadisonKastler_CyclicCutSwap`, `KadisonKastler_FourierShiftedFields`, `KadisonKastler_HardyEvaluationConstruction`, `KadisonKastler_HardyKernelRow`, `KadisonKastler_HardyKernelVectors`, `KadisonKastler_HardyUnitKernel`, `KadisonKastler_LiftedRankStrata`, `KadisonKastler_MatrixChainEmbedding`, `KadisonKastler_MeasurableBoundaryIntertwiner`, `KadisonKastler_MeasurableProductCocycle`, `KadisonKastler_NormUltraproduct`, `KadisonKastler_NormUltraproductMaps`, `KadisonKastler_ParameterizedBoundaryMean`, `KadisonKastler_ProductBoundaryLifts`, `KadisonKastler_PublishedFieldTomiyama`, `KadisonKastler_RegularCoreConjugation`, `KadisonKastler_RegularCoreCovariance`, `KadisonKastler_RegularCoreMonomials`, `KadisonKastler_RootBoundaryMeanConstruction`, `KadisonKastler_ScalarInvariantProjection`, `KadisonKastler_ScalarPositiveLimit`, `KadisonKastler_SeparableAlgebraPair`, `KadisonKastler_SpectralCommutant`, `KadisonKastler_SpectralVectorMeasure`, `KadisonKastler_StarEquivTraceTransport`, `KadisonKastler_SwappedBoundaryMean`.
--
--   **Imports.** It imports the published bundle `Def_StrongKadisonKastler`; the bundles `Q260K021`, `Q260K022`, `Q260K023`, `Q260K024` and `Q260K025` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q260K032` and `Q260K065`; the statement `OAI.KadisonKastler.typeIII_normUltraproduct_simple`; the proofs of `OAI.KadisonKastler.commonCenterSeparableStability_of_factors`, `OAI.KadisonKastler.core_kills_window_of_kills_trace_packet`, `OAI.KadisonKastler.exists_typeIII_uniform_commutator_correction`, `OAI.KadisonKastler.finiteCoefficientConjugations_of_separable_bound`, `OAI.KadisonKastler.publishedCentralPairDecomposition`, `OAI_KadisonKastler_publishedFieldTomiyama`, `OAI.KadisonKastler.regularCore_fixed_corner_commute_translations`, `OAI.KadisonKastler.regularCore_not_factor_of_trivial`, `OAI.KadisonKastler.typeIII_normUltraproduct_simple` and `OAI.KadisonKastler.uniform_typeIII_infinitesimal_bound`.
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
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Semiconj.Basic
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.LinearMap.Rat
import Mathlib.Algebra.Module.Rat
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Star.Module
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Star.Unitary
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.RealImaginaryPart
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Exponential
import Mathlib.Analysis.CStarAlgebra.GelfandDuality
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.CStarAlgebra.Unitization
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Convex
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
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Induction
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.Sublists
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Composition
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Set.Pairwise.Chain
import Mathlib.Data.Sym.Card
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.NoncommPiCoprod
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.Perm.Option
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Countable
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.LinearAlgebra.Multilinear.Curry
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Option
import Mathlib.Logic.Equiv.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.ConditionalExpectation.AEMeasurable
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Unique
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Function.SpecialFunctions.RCLike
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Trim
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.WithDensityFinite
import Mathlib.MeasureTheory.VectorMeasure.WithDensity
import Mathlib.Order.Bounds.OrderIso
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.Probability.Distributions.Cauchy
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ProductMeasure
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.RingTheory.Congruence.Hom
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.TwoSidedIdeal.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Lattice
import Mathlib.SetTheory.Cardinal.Free
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
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Topology.Algebra.UniformRing
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.ProperSpace.Real
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_StrongKadisonKastler
import Definitions.Def_Q260K021
import Definitions.Def_Q260K022
import Definitions.Def_Q260K023
import Definitions.Def_Q260K024
import Definitions.Def_Q260K025

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ConcreteTraceUniqueness
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealPartialOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonKastler.varyingSequenceCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Uniqueness of the normalized faithful factor trace

Projection dimension identifies any positive normalized tracial
functional on a finite diffuse factor. In particular, the explicit
matrix trace agrees with the canonical ultrapower trace.
-/

namespace KadisonKastler

noncomputable section

variable {B : Type*} [CStarAlgebra B]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

attribute [local instance] OAI.KadisonKastler.uniquenessOrder
local instance uniquenessPreorder_ra0088c_1 : Preorder (Algebra M) := (CStarAlgebra.spectralOrder _).toPreorder
local instance uniquenessLE_ra0088c_1 : LE (Algebra M) := (CStarAlgebra.spectralOrder _).toLE
attribute [local instance] OAI.KadisonKastler.uniquenessStarOrder
theorem trace_on_selfAdjoint
    (hM : Generator.IsII1Factor M.toStarSubalgebra) (τ : FaithfulTracialState (Algebra M))
    (x : Algebra M) (hx : IsSelfAdjoint x) :
    τ.toLinearMap x = Generator.Tracial.dimensionSpectralValue
      (scalarCenter hM) hM.diffuse hM.finite (one_ne_zero hM) x hx := by
  apply Generator.Tracial.functional_eq_dimensionSpectralValue
    (scalarCenter hM) hM.diffuse hM.finite (one_ne_zero hM)
    τ.toContinuousLinearMap τ.norm_toContinuousLinearMap_le
  intro p
  exact Generator.Tracial.tracialFunctional_projection_dimension
    (scalarCenter hM) hM.diffuse hM.finite (one_ne_zero hM)
    τ.toContinuousLinearMap τ.map_one (fun _ hx => τ.nonneg hx) τ.map_star τ.tracial p

/-- Any two normalized faithful tracial states on a concrete II1 factor
agree. Normality is not an extra premise. -/
theorem faithfulTracialState_unique
    (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (τ σ : FaithfulTracialState (Algebra M)) (x : Algebra M) :
    τ.toLinearMap x = σ.toLinearMap x := by
  have hsa (y : Algebra M) (hy : IsSelfAdjoint y) : τ.toLinearMap y = σ.toLinearMap y :=
    (trace_on_selfAdjoint hM τ y hy).trans (trace_on_selfAdjoint hM σ y hy).symm
  rw [← realPart_add_I_smul_imaginaryPart x, map_add, map_add, map_smul, map_smul,
    hsa _ (selfAdjoint.mem_iff.mp (realPart x).property),
    hsa _ (selfAdjoint.mem_iff.mp (imaginaryPart x).property)]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SeparableAlgebraPair
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Nearby separable test algebras

Countably many generators are enlarged alternately by nearby contractions.
The increasing norm closures give the two separable C*-algebras in §9.
All choices and closure estimates are constructed here; there is no
separable-reduction hypothesis.
-/

namespace KadisonKastler

open TopologicalSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Add a countable family of near approximants to the second seed set. -/
theorem exists_separable_seed_extension (M N : VonNeumannAlgebra H)
    {s t : Set (H →L[ℂ] H)} (hs : s.Countable) (ht : t.Countable)
    (hsM : s ⊆ M) (htN : t ⊆ N) {r : ℝ} (hr : kkDistance M N < r) :
    ∃ t' : Set (H →L[ℂ] H), t'.Countable ∧ t ⊆ t' ∧ t' ⊆ N ∧
      ∀ x ∈ starAlgebraBall (cstarHull s),
        Metric.infDist x (starAlgebraBall (cstarHull t')) ≤ r := by
  obtain ⟨D, hDsub, hDc, hDdense⟩ :=
    ((isSeparable_cstarHull hs).mono
      (show starAlgebraBall (cstarHull s) ⊆ (cstarHull s : Set (H →L[ℂ] H)) from
        fun _ hx => hx.1)).exists_countable_dense_subset
  have happrox : ∀ x : D, ∃ y ∈ unitBall N, ‖(x : H →L[ℂ] H) - y‖ < r := by
    intro x
    have hx := hDsub x.property
    exact exists_unitBall_approx ⟨cstarHull_le M hsM hx.1, hx.2⟩ hr
  choose f hf hdist using happrox
  let t' := t ∪ Set.range f
  have htc : t'.Countable := by
    let : Countable D := hDc.to_subtype
    exact ht.union (Set.countable_range f)
  refine ⟨t', htc, Set.subset_union_left, ?_, ?_⟩
  · rintro y (hy | ⟨x, rfl⟩)
    · exact htN hy
    · exact (hf x).1
  · intro x hx
    apply infDist_le_of_mem_closure (s := D) ?_ (hDdense hx)
    intro y hy
    have hy' : f ⟨y, hy⟩ ∈ starAlgebraBall (cstarHull t') :=
      ⟨subset_cstarHull t' (Or.inr ⟨⟨y, hy⟩, rfl⟩), (hf ⟨y, hy⟩).2⟩
    exact (Metric.infDist_le_dist_of_mem hy').trans
      (by simpa only [dist_eq_norm] using (hdist ⟨y, hy⟩).le)

theorem SeparableSeeds.exists_extension {M N : VonNeumannAlgebra H}
    (p : SeparableSeeds M N) {r : ℝ} (hr : kkDistance M N < r) :
    ∃ q : SeparableSeeds M N, p.Extends q r := by
  obtain ⟨t, htc, hpt, htN, hnear₁⟩ := exists_separable_seed_extension M N
    p.left_countable p.right_countable p.left_mem p.right_mem hr
  obtain ⟨s, hsc, hps, hsM, hnear₂⟩ := exists_separable_seed_extension N M
    p.right_countable p.left_countable p.right_mem p.left_mem
    (by simpa only [kkDistance_comm N M] using hr)
  exact ⟨⟨s, t, hsc, htc, hsM, htN⟩, hps, hpt, hnear₁, hnear₂⟩

def SeparableSeeds.next {M N : VonNeumannAlgebra H}
    (p : SeparableSeeds M N) {r : ℝ} (hr : kkDistance M N < r) : SeparableSeeds M N :=
  Classical.choose (p.exists_extension hr)

def SeparableSeeds.stages {M N : VonNeumannAlgebra H}
    (p : SeparableSeeds M N) {r : ℝ} (hr : kkDistance M N < r) : ℕ → SeparableSeeds M N
  | 0 => p
  | n + 1 => (p.stages hr n).next hr

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SpectralVectorMeasure
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Finite vector measures for real scalar multipliers

The squared pointwise norm of an L2 vector defines a finite measure.
Character commutation preserves its characteristic function and hence
the measure itself. This yields commutation with every scalar multiplier.
-/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Invariance of all vector measures implies commutation with every
bounded Borel multiplier, by polarization of its quadratic form. -/
theorem unitary_commute_scalarMultiplier_of_characters
    (U : unitary (RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H))
    (hU : ∀ a : ℝ, Commute (U : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      (regularCharacterUnitary (H := H) a : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H))
    (φ : ℝ → ℂ) (hφ : Measurable φ) (C : ℝ) (hC : ∀ t, ‖φ t‖ ≤ C) :
    Commute (U : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      (regularScalarMultiplier φ hφ C hC) := by
  let A := regularScalarMultiplier (H := H) φ hφ C hC
  let B := star (U : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) * A *
    (U : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
  have hquad (f : RegularCoreHilbert H) : inner ℂ f (B f) = inner ℂ f (A f) := by
    change inner ℂ f (star (U : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      (A ((U : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f))) = _
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
    change inner ℂ ((U : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f)
      (regularScalarMultiplier φ hφ C hC
        ((U : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f)) = _
    rw [regularVectorMeasure_multiplier, regularVectorMeasure_unitary_eq U hU,
      regularVectorMeasure_multiplier]
  have hlin : B.toLinearMap = A.toLinearMap := by
    apply (ext_inner_map _ _).mp
    intro f
    calc
      inner ℂ (B f) f = star (inner ℂ f (B f)) := (inner_conj_symm (B f) f).symm
      _ = star (inner ℂ f (A f)) := congrArg star (hquad f)
      _ = inner ℂ (A f) f := inner_conj_symm (A f) f
  apply (commute_unitary_iff_star_left_conjugate U.property).mpr
  apply ContinuousLinearMap.ext
  intro f
  exact LinearMap.congr_fun hlin f

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SpectralCommutant
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

theorem commute_scalarMultiplier_of_characters
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (hT : ∀ a : ℝ, Commute T (regularCharacterUnitary (H := H) a :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H))
    (φ : ℝ → ℂ) (hφ : Measurable φ) (C : ℝ) (hC : ∀ t, ‖φ t‖ ≤ C) :
    Commute T (regularScalarMultiplier φ hφ C hC) := by
  apply commute_map_of_unitaries (characterCommutant (H := H)).subtype
    (regularScalarMultiplier φ hφ C hC) ?_ ⟨T, mem_characterCommutant T hT⟩
  intro u
  let v := Unitary.map (StarMonoidHom.ofClass (characterCommutant (H := H)).subtype) u
  exact unitary_commute_scalarMultiplier_of_characters v
    (characterCommutant_unitary_commutes u) φ hφ C hC

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CoreFrequencyCuts
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Frequency windows in the concrete modular core

The translation generators and the proved real spectral commutant theorem
put the Fourier interval projections inside the actual generated core.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
  (M : VonNeumannAlgebra H)

theorem regularFourierIndicator_mem_core (s : Set ℝ) (hs : MeasurableSet s) :
    (Lp.fourierTransformₗᵢ ℝ H).symm.conjStarAlgEquiv (regularIndicatorProjection s hs) ∈
      regularCoreAlgebra U hU M := by
  rw [← VonNeumannAlgebra.commutant_commutant (regularCoreAlgebra U hU M)]
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro T hT
  have htrans (t : Multiplicative ℝ) : Commute T
      (regularRightTranslation (H := H) t : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) :=
    (VonNeumannAlgebra.mem_commutant_iff.mp hT _ (regularTranslation_mem_core U hU M t)).symm
  have hc := commute_scalarMultiplier_of_characters
    ((Lp.fourierTransformₗᵢ ℝ H).conjStarAlgEquiv T)
    (fourier_commute_characters_of_translations T htrans)
    (s.indicator fun _ => (1 : ℂ)) (measurable_const.indicator hs) 1
    (fun t => by by_cases ht : t ∈ s <;> simp [ht])
  change _ = _
  apply (Lp.fourierTransformₗᵢ ℝ H).conjStarAlgEquiv.injective
  have he : (Lp.fourierTransformₗᵢ ℝ H).conjStarAlgEquiv
      ((Lp.fourierTransformₗᵢ ℝ H).symm.conjStarAlgEquiv (regularIndicatorProjection s hs)) =
        regularIndicatorProjection s hs := by
    apply ContinuousLinearMap.ext
    intro f
    simp only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
      LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.symm_apply_apply]
  rw [map_mul, map_mul]
  change (Lp.fourierTransformₗᵢ ℝ H).conjStarAlgEquiv T *
      (Lp.fourierTransformₗᵢ ℝ H).conjStarAlgEquiv
        ((Lp.fourierTransformₗᵢ ℝ H).symm.conjStarAlgEquiv (regularIndicatorProjection s hs)) =
    (Lp.fourierTransformₗᵢ ℝ H).conjStarAlgEquiv
        ((Lp.fourierTransformₗᵢ ℝ H).symm.conjStarAlgEquiv (regularIndicatorProjection s hs)) *
      (Lp.fourierTransformₗᵢ ℝ H).conjStarAlgEquiv T
  rw [he]
  exact hc.eq

theorem regularFrequencyWindow_mem_core (a b : ℝ) :
    regularFrequencyWindow (H := H) a b ∈ regularCoreAlgebra U hU M :=
  regularFourierIndicator_mem_core U hU M _ measurableSet_Ioc

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CoreFrequencyFinite
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The finite-window reduction for the modular core

The frequency window is nonzero, and the weighted packet gives a
faithful vector on its corner. Equality of the vector norms for an
operator and its adjoint makes this corner finite.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
  (M : VonNeumannAlgebra H)

def unitCoreFrequencyProjection : AlgebraProjection (regularCoreAlgebra U hU M) :=
  ⟨⟨regularFrequencyWindow 0 1, regularFrequencyWindow_mem_core U hU M 0 1⟩, by
    constructor
    · apply Subtype.ext
      exact (regularFrequencyWindow_isStarProjection (H := H) 0 1).isIdempotentElem.eq
    · apply Subtype.ext
      exact (regularFrequencyWindow_isStarProjection (H := H) 0 1).isSelfAdjoint.star_eq⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FourierShiftedFields
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Fourier coordinates of the shifted frequency field -/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) (l : X → ℝ) (hl : Measurable l)

include hl in
theorem fourierShiftedField_measurable (a : ℝ) (f : RegularCoreHilbert ℂ) :
    AEStronglyMeasurable (fun s => scalarFourierCut (a - l s) f) μ := by
  exact (Lp.fourierTransformₗᵢ ℝ ℂ).continuous.comp_aestronglyMeasurable
    (shiftedFrequencyField_measurable μ l hl a ((Lp.fourierTransformₗᵢ ℝ ℂ).symm f))

def fourierShiftedField (a : ℝ) :
    Lp (RegularCoreHilbert ℂ) 2 μ →L[ℂ] Lp (RegularCoreHilbert ℂ) 2 μ :=
  regularFieldOperator μ (fun s => scalarFourierCut (a - l s))
    (fourierShiftedField_measurable μ l hl a) 1
    (Eventually.of_forall fun _ => scalarFourierCut_norm _)

theorem fourierShiftedField_apply_ae (a : ℝ) (F : Lp (RegularCoreHilbert ℂ) 2 μ) :
    fourierShiftedField μ l hl a F =ᵐ[μ] fun s => scalarFourierCut (a - l s) (F s) :=
  regularFieldOperator_represents μ _ _ _ _ F

theorem fourierShiftedField_intertwines (a : ℝ) (F : Lp (RegularCoreHilbert ℂ) 2 μ) :
    (Lp.fourierTransformₗᵢ ℝ ℂ).toContinuousLinearEquiv.toContinuousLinearMap.compLp
      (shiftedFrequencyField μ l hl a F) =
    fourierShiftedField μ l hl a
      ((Lp.fourierTransformₗᵢ ℝ ℂ).toContinuousLinearEquiv.toContinuousLinearMap.compLp F) := by
  apply compLp_regularFieldOperator μ
    (Lp.fourierTransformₗᵢ ℝ ℂ).toContinuousLinearEquiv.toContinuousLinearMap
    (fun s => regularFrequencyProjection (a - l s)) (fun s => scalarFourierCut (a - l s))
    (shiftedFrequencyField_measurable μ l hl a) (fourierShiftedField_measurable μ l hl a) 1 1
    (Eventually.of_forall fun _ => (regularFrequencyProjection_isStarProjection _).norm_le _)
    (Eventually.of_forall fun _ => scalarFourierCut_norm _)
  intro s f
  change (Lp.fourierTransformₗᵢ ℝ ℂ) (regularFrequencyProjection (a - l s) f) =
    (Lp.fourierTransformₗᵢ ℝ ℂ) (regularFrequencyProjection (a - l s)
      ((Lp.fourierTransformₗᵢ ℝ ℂ).symm ((Lp.fourierTransformₗᵢ ℝ ℂ) f)))
  rw [LinearIsometryEquiv.symm_apply_apply]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CyclicCutSwap
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Interchanging the variables of the modular cut field -/

namespace KadisonKastler

open MeasureTheory Filter
open scoped TensorProduct

noncomputable section

section Scalar

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) (l : X → ℝ) (hl : Measurable l)

theorem fourierShiftedField_tensor_rows (a : ℝ)
    (f : Lp ℂ 2 (volume : Measure ℝ)) (v : Lp ℂ 2 μ) :
    ∀ᵐ s ∂μ, ∀ᵐ ξ ∂(volume : Measure ℝ),
      (fourierShiftedField μ l hl a (scalarLpTensor μ v f)) s ξ =
        (if a < l s + 2 * Real.pi * ξ then (1 : ℂ) else 0) * f ξ * v s := by
  filter_upwards [fourierShiftedField_apply_ae μ l hl a (scalarLpTensor μ v f),
    scalarLpTensor_apply_ae μ v f] with s hF hv
  have he := hF.trans (congrArg (scalarFourierCut (a - l s)) hv)
  filter_upwards [scalarFourierCut_apply_ae (a - l s) (v s • f), Lp.coeFn_smul (v s) f]
    with ξ hc hf
  have hcond : ξ ∈ Set.Ioi ((a - l s) / (2 * Real.pi)) ↔ a < l s + 2 * Real.pi * ξ := by
    change (a - l s) / (2 * Real.pi) < ξ ↔ _
    rw [div_lt_iff₀ (by positivity : 0 < 2 * Real.pi)]
    constructor <;> intro h <;> nlinarith
  have hind : (Set.Ioi ((a - l s) / (2 * Real.pi))).indicator (v s • f) ξ =
      (if a < l s + 2 * Real.pi * ξ then (1 : ℂ) else 0) * f ξ * v s := by
    by_cases h : a < l s + 2 * Real.pi * ξ
    · rw [Set.indicator_of_mem (hcond.mpr h), hf, ite_eq_left h]
      change v s * f ξ = _
      ring
    · rw [Set.indicator_of_notMem (mt hcond.mp h), ite_eq_right h]
      simp
  calc
    _ = (scalarFourierCut (a - l s) (v s • f)) ξ :=
      congrArg (fun w : RegularCoreHilbert ℂ => w ξ) he
    _ = _ := hc.trans hind

end Scalar

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_HardyUnitKernel
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Unit Hardy kernels and their Poisson compression -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

theorem hardyUnitKernel_density {z : ℂ} (hz : 0 < z.re) :
    (fun s => ‖hardyUnitKernel z hz s‖ ^ 2) =ᵐ[volume]
      realPoissonKernel (z.im / (2 * Real.pi)) (z.re / (2 * Real.pi)) := by
  filter_upwards [Lp.coeFn_smul (Real.sqrt (2 * z.re) : ℂ)
    (hardyReproducingKernel z hz), hardyReproducingKernel_apply_ae hz] with s hs hk
  change ‖((Real.sqrt (2 * z.re) : ℂ) • hardyReproducingKernel z hz) s‖ ^ 2 = _
  rw [hs, Pi.smul_apply, hk, norm_smul, mul_pow, Complex.norm_real,
    Real.norm_eq_abs, sq_abs, Real.sq_sqrt (by positivity), hardyCauchyFunction_norm_sq hz]
  field_simp

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_HardyKernelVectors
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Reproducing-kernel vectors and their character tests -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem hardyUnitKernel_ne_zero_ae (z : ℂ) (hz : 0 < z.re) :
    ∀ᵐ s : ℝ, hardyUnitKernel z hz s ≠ 0 := by
  filter_upwards [hardyUnitKernel_density hz] with s hs
  have hp : 0 < realPoissonKernel (z.im / (2 * Real.pi)) (z.re / (2 * Real.pi)) s := by
    unfold realPoissonKernel
    positivity
  intro hzero
  rw [hzero, norm_zero, zero_pow (by decide)] at hs
  linarith

/-- Character-kernel vectors determine continuous operators on the regular space. -/
theorem hardyKernelInclusion_ext (z : ℂ) (hz : 0 < z.re)
    {A B : RegularCoreHilbert H →L[ℂ] H}
    (he : ∀ s : ℝ, ∀ x : H,
      A ((regularCharacterUnitary (H := H) (2 * Real.pi * s) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (hardyKernelInclusion z hz x)) =
      B ((regularCharacterUnitary (H := H) (2 * Real.pi * s) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (hardyKernelInclusion z hz x))) :
    A = B := by
  have ha : A.adjoint = B.adjoint := by
    apply ContinuousLinearMap.ext
    intro y
    apply sub_eq_zero.mp
    apply eq_zero_of_inner_character_packets (hardyUnitKernel z hz) (hardyUnitKernel_ne_zero_ae z hz)
    intro s x
    rw [inner_sub_right, ContinuousLinearMap.adjoint_inner_right,
      ContinuousLinearMap.adjoint_inner_right]
    change inner ℂ (A ((regularCharacterUnitary (H := H) (2 * Real.pi * s) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (hardyKernelInclusion z hz x))) y -
      inner ℂ (B ((regularCharacterUnitary (H := H) (2 * Real.pi * s) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (hardyKernelInclusion z hz x))) y = 0
    rw [he, sub_self]
  have h := congrArg ContinuousLinearMap.adjoint ha
  simpa only [ContinuousLinearMap.adjoint_adjoint] using h

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_HardyKernelRow
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The reproducing row on the positive-frequency space -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem regularCharacter_adjoint_neg (b : ℝ) :
    (regularCharacterUnitary (H := H) (2 * Real.pi * b) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H).adjoint =
    (regularCharacterUnitary (H := H) (2 * Real.pi * (-b)) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) := by
  rw [← ContinuousLinearMap.star_eq_adjoint]
  have h := congrArg (fun u : unitary (RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) =>
    (u : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H))
    (regularCharacterUnitary_neg (H := H) (2 * Real.pi * b))
  simpa only [Unitary.coe_star, mul_neg] using h.symm

/-- Positive character shifts have the expected scalar action under evaluation. -/
theorem hardyKernelRow_forward (z : ℂ) (hz : 0 < z.re) {b : ℝ} (hb : 0 ≤ b)
    (f : RegularCoreHilbert H) (hf : regularFrequencyProjection 0 f = f) :
    hardyKernelRow z hz ((regularCharacterUnitary (H := H) (2 * Real.pi * b) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f) =
      star (Complex.exp (-z * b)) • hardyKernelRow z hz f := by
  apply ext_inner_left ℂ
  intro x
  change inner ℂ x ((hardyKernelInclusion z hz).toContinuousLinearMap.adjoint _) = _
  rw [ContinuousLinearMap.adjoint_inner_right,
    ← ContinuousLinearMap.adjoint_inner_left, regularCharacter_adjoint_neg]
  let g := (regularCharacterUnitary (H := H) (2 * Real.pi * (-b)) :
    RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (hardyKernelInclusion z hz x)
  have hs : inner ℂ (regularFrequencyProjection 0 g) f =
      inner ℂ g (regularFrequencyProjection 0 f) :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (regularFrequencyProjection_isStarProjection (H := H) 0).isSelfAdjoint) g f
  dsimp [g] at hs
  rw [hf, hardyKernelInclusion_backward_shift z hz hb] at hs
  change inner ℂ ((regularCharacterUnitary (H := H) (2 * Real.pi * (-b)) :
    RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (hardyKernelInclusion z hz x)) f = _
  rw [← hs, inner_smul_left, inner_smul_right]
  change star (Complex.exp (-z * b)) *
    inner ℂ (hardyKernelInclusion z hz x) f =
      star (Complex.exp (-z * b)) * inner ℂ x
        ((hardyKernelInclusion z hz).toContinuousLinearMap.adjoint f)
  rw [ContinuousLinearMap.adjoint_inner_right]
  rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_HardyEvaluationConstruction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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

theorem hardyKernelRow_factor (z : ℂ) (hz : 0 < z.re)
    (T : positiveFrequencyAlgebra (H := H)) :
    ((hardyKernelRow z hz).comp T.val).comp (regularFrequencyProjection 0) =
      (((hardyKernelRow z hz).comp T.val).comp
        (hardyKernelInclusion z hz).toContinuousLinearMap).comp (hardyKernelRow z hz) := by
  apply hardyKernelInclusion_ext z hz
  intro s x
  change hardyKernelRow z hz (T.val (regularFrequencyProjection 0
      ((regularCharacterUnitary (H := H) (2 * Real.pi * s) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (hardyKernelInclusion z hz x)))) =
    hardyKernelRow z hz (T.val (hardyKernelInclusion z hz
      (hardyKernelRow z hz ((regularCharacterUnitary (H := H) (2 * Real.pi * s) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (hardyKernelInclusion z hz x)))))
  rcases le_total 0 s with hs | hs
  · have hp := regularCharacter_preserves_positive hs (hardyKernelInclusion z hz x)
      (hardyKernelInclusion_positive z hz x)
    have hc := congrArg (fun A : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H =>
      A (hardyKernelInclusion z hz x)) (T.property.1 (2 * Real.pi * s)).eq
    change T.val ((regularCharacterUnitary (H := H) (2 * Real.pi * s) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (hardyKernelInclusion z hz x)) =
      (regularCharacterUnitary (H := H) (2 * Real.pi * s) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (T.val (hardyKernelInclusion z hz x)) at hc
    have hTx := positiveFrequencyAlgebra_preserves T (hardyKernelInclusion z hz x)
      (hardyKernelInclusion_positive z hz x)
    have hr := hardyKernelRow_forward z hz hs (hardyKernelInclusion z hz x)
      (hardyKernelInclusion_positive z hz x)
    rw [hardyKernelRow_inclusion] at hr
    rw [hp, hc, hardyKernelRow_forward z hz hs _ hTx, hr]
    simp only [map_smul]
  · have hp := hardyKernelInclusion_backward_shift z hz (neg_nonneg.mpr hs) x
    simp only [neg_neg, Complex.ofReal_neg] at hp
    have hr : hardyKernelRow z hz ((regularCharacterUnitary (H := H) (2 * Real.pi * s) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (hardyKernelInclusion z hz x)) =
        Complex.exp (-z * (-s)) • x := by
      rw [← hardyKernelRow_projection z hz, hp, map_smul, hardyKernelRow_inclusion]
    rw [hp, hr]
    simp only [map_smul]

/-- Point evaluation constructed from the invariant Cauchy-kernel quotient. -/
def hardyEvaluationAt (z : ℂ) (hz : 0 < z.re) :
    positiveFrequencyAlgebra (H := H) →ₐ[ℂ] (H →L[ℂ] H) :=
  hardyCompressionAlgHom (positiveFrequencyAlgebra (H := H))
    (hardyKernelInclusion z hz).toContinuousLinearMap (hardyKernelRow z hz)
    (regularFrequencyProjection 0) (hardyKernelInclusion_adjoint_self z hz)
    (fun T => by
      apply ContinuousLinearMap.ext
      intro x
      exact positiveFrequencyAlgebra_preserves T (hardyKernelInclusion z hz x)
        (hardyKernelInclusion_positive z hz x))
    (hardyKernelRow_factor z hz)

@[simp] theorem hardyEvaluationAt_apply (z : ℂ) (hz : 0 < z.re)
    (T : positiveFrequencyAlgebra (H := H)) :
    hardyEvaluationAt z hz T = hardyKernelCompression z hz T.val := rfl

universe u

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_LiftedRankStrata
attribute [-instance] _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # Rank strata in the universe of the original Hilbert space -/

namespace KadisonKastler

open MeasureTheory KadisonSimilarity
open scoped lp

noncomputable section

universe u

variable {A B H : Type u} [CommCStarAlgebra A] [TopologicalSpace.SeparableSpace A]
  [CStarAlgebra B] [TopologicalSpace.SeparableSpace B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  {π : A →⋆ₐ[ℂ] (H →L[ℂ] H)} {D : CyclicDecompositionData π.range}
  {σ : B →⋆ₐ[ℂ] (H →L[ℂ] H)} (M : BorelCommonModel π D σ)

attribute [local instance] commonCyclicMeasurable commonCyclicBorel commonCyclicCountable

def liftedRankCoordinates : H ≃ₗᵢ[ℂ] lp (fun n => (commonRankStratum M n).space) 2 :=
  (commonRankCoordinates M).trans (hilbertSumCoordinateEquiv (commonRankStratumEquiv M))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixChainEmbedding
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Embedding an increasing full-matrix closure

Compatible frames give an increasing sequence of finite unitary groups.
Their union generates the original von Neumann algebra, so its invariant
mean provides a single simultaneous embedding of the entire closure.
-/

namespace KadisonKastler

noncomputable section

variable {U : Type*} [Group U]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [Nontrivial H] {A : ℕ → StarSubalgebra ℂ (H →L[ℂ] H)}

/-- Every element of the finite-group union belongs to the original matrix closure. -/
theorem matrixChainGroup_mem (F : ∀ n, FullMatrixFrame (A n)) (hA : Monotone A)
    (u : increasingSubgroupUnion
      (fun n => (compatibleMatrixFrames F hA n).group)
      (compatibleMatrixFrames_group_monotone F hA)) :
    (u : H →L[ℂ] H) ∈ generatedVonNeumannAlgebra (⨆ n, A n) := by
  obtain ⟨n, hn⟩ := u.property
  apply subset_generatedVonNeumannAlgebra
  exact (le_iSup A n) ((compatibleMatrixFrames F hA n).group_mem ⟨u.val, hn⟩)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PublishedFieldTomiyama
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 800000

namespace OAI

/-! # The precise Tomiyama input for the operator-field mean

Tomiyama, *On the projection of norm one in W*-algebras*, Proceedings of
 the Japan Academy 33 (1957), 608–612, Theorem 1(2), pp. 608–609,
 DOI 10.3792/pja/1195524885.

Only the bimodule conclusion for the constant-field inclusion is retained.
The contractive retraction and its adjoint preservation are constructed in
`OperatorCoefficientMean` and `OperatorMeanStar`, not assumed here.
-/

namespace KadisonKastler

open scoped BoundedContinuousFunction

noncomputable section

variable {G D H : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace D] {μ : MeasureTheory.Measure D} [MeasureTheory.IsFiniteMeasure μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

instance operatorFieldFamilyCStar : CStarAlgebra (G →ᵇ WeakOperatorField (H := H) μ) where

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MeasurableBoundaryIntertwiner
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.NonsingularAction.restrictedOperatorAction_coe _root_.OAI.KadisonKastler.WeakOperatorRepresentative.evalHom_apply _root_.OAI.KadisonKastler.WeakOperatorRepresentative.eval_kernelProjection _root_.OAI.KadisonKastler.WeakOperatorRepresentative.eval_positiveKernelProjection _root_.OAI.KadisonKastler.WeakOperatorRepresentative.topElement_val _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.tracialQuotientLinear_map _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Measurable representatives of the averaged boundary intertwiner

The operator-field mean and polar normalization construct the intertwiner
in the quotient algebra. The null ideal then gives the exact measurable
operator identity needed by the finite-factor argument.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped BoundedContinuousFunction

noncomputable section

variable {G D H : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace D] {μ : Measure D} [IsFiniteMeasure μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

/-- A constant operator representation in the actual field quotient. -/
def constantFieldRepresentation (U : G →* unitary (H →L[ℂ] H)) :
    G →* unitary (WeakOperatorField (H := H) μ) :=
  (Unitary.map (StarMonoidHom.ofClass (operatorFieldConst (H := H) μ))).toMonoidHom.comp U

omit [TopologicalSpace G] [DiscreteTopology G] [IsFiniteMeasure μ]
  [TopologicalSpace.SeparableSpace H] in
@[simp]
theorem constantFieldRepresentation_coe (U : G →* unitary (H →L[ℂ] H)) (g : G) :
    (constantFieldRepresentation (μ := μ) U g : WeakOperatorField (H := H) μ) =
      operatorFieldConst μ (U g) := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MeasurableProductCocycle
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The product cocycle as a measurable operator class

The pointwise two-sided field is measurable and uniformly unitary. Its
class satisfies the separate-action cocycle law even when the original
cocycle and algebra-membership statements hold only almost everywhere.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped BoundedContinuousFunction

noncomputable section

variable {G D H : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace D] {μ : Measure D} [SFinite μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

/-- Bundle an everywhere unitary field from measurable evaluations. -/
def measurableUnitaryRepresentative {X : Type*} [MeasurableSpace X] {ν : Measure X}
    (f : X → unitary (H →L[ℂ] H))
    (hf : ∀ ξ, AEStronglyMeasurable (fun x => (f x : H →L[ℂ] H) ξ) ν) :
    unitary (WeakOperatorRepresentative (H := H) ν) := by
  let F : WeakOperatorRepresentative (H := H) ν :=
    WeakOperatorRepresentative.mk (fun x => (f x : H →L[ℂ] H)) 1
      (fun x => norm_unitary_le_one (f x)) hf
      (operator_adjoint_eval_aestronglyMeasurable (fun x => (f x : H →L[ℂ] H)) hf)
  refine ⟨F, ?_, ?_⟩
  · apply WeakOperatorRepresentative.eq_of_eval
    intro x
    change star (f x : H →L[ℂ] H) * (f x : H →L[ℂ] H) = 1
    exact Unitary.star_mul_self_of_mem (f x).property
  · apply WeakOperatorRepresentative.eq_of_eval
    intro x
    change (f x : H →L[ℂ] H) * star (f x : H →L[ℂ] H) = 1
    exact Unitary.mul_star_self_of_mem (f x).property

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_NormUltraproduct
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.algebraCStarAlgebra _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.operatorFieldFamilyCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The actual norm ultraproduct for the infinitesimal normalizer argument

The null sequences form a closed star ideal in the bounded product. Its
C-star quotient is the norm ultraproduct used in the infinitesimal
normalizer argument.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable (B : ℕ → Type*) [∀ j, CStarAlgebra (B j)] [∀ j, Nontrivial (B j)]

attribute [local instance] OAI.KadisonKastler.instPartialOrderSubtypePreLpNatMemAddSubgroupVaryingBoundedSequence
attribute [local instance] OAI.KadisonKastler.instStarOrderedRingSubtypePreLpNatMemAddSubgroupVaryingBoundedSequence
instance normUltraproductCStarAlgebra (ω : Ultrafilter ℕ) : CStarAlgebra (NormUltraproduct B ω) :=
  inferInstanceAs (CStarAlgebra (normNullClosedIdeal B ω).Quotient)

theorem normUltraproductMap_surjective (ω : Ultrafilter ℕ) :
    Function.Surjective (normUltraproductMap B ω) :=
  (normNullClosedIdeal B ω).quotientMap_surjective

theorem normUltraproductMap_eq_zero_iff (ω : Ultrafilter ℕ) (x : VaryingBoundedSequence B) :
    normUltraproductMap B ω x = 0 ↔ NormNullSequence B ω x := by
  change (normNullClosedIdeal B ω).quotientMap x =
    (normNullClosedIdeal B ω).quotientMap 0 ↔ _
  constructor
  · intro h
    have hr := Quotient.exact h
    change NormNullSequence B ω (x - 0) at hr
    simpa only [sub_zero] using hr
  · intro h
    apply Quotient.sound
    change NormNullSequence B ω (x - 0)
    simpa only [sub_zero] using h

instance normUltraproductNontrivial (ω : Ultrafilter ℕ) : Nontrivial (NormUltraproduct B ω) := by
  have h : (1 : NormUltraproduct B ω) ≠ 0 := by
    intro heq
    have hn := (normUltraproductMap_eq_zero_iff B ω 1).mp
      (by simpa only [map_one] using heq)
    have hlim : Tendsto (fun _ : ℕ => (1 : ℝ)) (ω : Filter ℕ) (𝓝 0) := by
      change Tendsto (fun j => ‖(1 : B j)‖) (ω : Filter ℕ) (𝓝 0) at hn
      simpa only [norm_one] using hn
    exact _root_.one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hlim)
  exact ⟨⟨1, 0, h⟩⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_NormUltraproductMaps
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.NonsingularAction.operatorAction_constant _root_.OAI.KadisonKastler.NonsingularAction.operatorEquiv_apply _root_.OAI.KadisonKastler.NonsingularAction.restrictedOperatorAction_coe _root_.OAI.KadisonKastler.ScalarBoundaryMean.operatorMean_apply _root_.OAI.KadisonKastler.WeakOperatorField.pullback_constant _root_.OAI.KadisonKastler.WeakOperatorField.pullback_id _root_.OAI.KadisonKastler.constantFieldRepresentation_coe _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.tracialQuotientLinear_map _root_.OAI.KadisonKastler.tracialSequenceContinuous_apply _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.tracialSequenceValue_one _root_.OAI.KadisonKastler.varyingSequenceHom_apply _root_.OAI.KadisonKastler.varyingUnitarySequence_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Coordinate embeddings induce faithful norm-ultraproduct embeddings -/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {B C : ℕ → Type*} [∀ j, CStarAlgebra (B j)] [∀ j, Nontrivial (B j)]
  [∀ j, CStarAlgebra (C j)] [∀ j, Nontrivial (C j)]

def normUltraproductInducedMap (φ : ∀ j, B j →⋆ₐ[ℂ] C j) (ω : Ultrafilter ℕ) :
    NormUltraproduct B ω →⋆ₐ[ℂ] NormUltraproduct C ω :=
  starAlgHomDescend (normUltraproductMap B ω) (normUltraproductMap_surjective B ω)
    ((normUltraproductMap C ω).comp (normProductMap φ))
    (fun x hx => (normUltraproductMap_eq_zero_iff C ω _).mpr
      (((normUltraproductMap_eq_zero_iff B ω x).mp hx).map φ))

@[simp] theorem normUltraproductInducedMap_apply_map (φ : ∀ j, B j →⋆ₐ[ℂ] C j)
    (ω : Ultrafilter ℕ) (x : VaryingBoundedSequence B) :
    normUltraproductInducedMap φ ω (normUltraproductMap B ω x) =
      normUltraproductMap C ω (normProductMap φ x) :=
  starAlgHomDescend_apply_map _ _ _ _ x

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ScalarPositiveLimit
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.ScalarOperatorKernel.toContinuous_apply _root_.OAI.KadisonKastler.UniformMeasurableOperators.coefficientFamily_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.nestedMeanRowsL_apply _root_.OAI.KadisonKastler.scalarBoundaryStar_apply _root_.OAI.KadisonKastler.scalarInfinityMulL_apply _root_.OAI.KadisonKastler.scalarL2MulL_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Positivity of scalar averages and their weak limit -/

namespace KadisonKastler

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem scalarNonnegative_pullback_power (S : X → X)
    (hS : Measure.QuasiMeasurePreserving S μ μ) [IsFiniteMeasure μ]
    {f : ScalarLInfinity μ} (hf : ScalarNonnegative f) (i : ℕ) :
    ScalarNonnegative (((scalarInfinityPullbackL S hS) ^ i) f) := by
  induction i with
  | zero => simpa using hf
  | succ i hi =>
    rw [pow_succ', mul_apply_eq_comp]
    exact scalarNonnegative_pullback S hS hi

theorem scalarNonnegative_shiftCesaro (S : X → X)
    (hS : Measure.QuasiMeasurePreserving S μ μ) [IsFiniteMeasure μ]
    {f : ScalarLInfinity μ} (hf : ScalarNonnegative f) (n : ℕ) :
    ScalarNonnegative (scalarShiftCesaro S hS n f) := by
  let U : ScalarLInfinity μ →L[ℂ] ScalarLInfinity μ := scalarInfinityPullbackL S hS
  have hp : ∀ i : ℕ, ScalarNonnegative ((U ^ i) f) := by
    intro i
    exact scalarNonnegative_pullback_power S hS (f := f) hf i
  have hh := scalarNonnegative_weighted_sum (μ := μ) (fun i => (U ^ i) f) hp
    (Finset.range (n + 1)) (((n + 1 : ℕ) : ℝ)⁻¹)
    (inv_nonneg.mpr (Nat.cast_nonneg (n + 1)))
  rw [scalarShiftCesaro_apply]
  simpa only [U, Complex.ofReal_inv] using hh

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ScalarInvariantProjection
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A natural positive projection onto shift-invariant scalar functions

The concrete Cesaro construction supplies the limit, its positivity and
contractivity. Weak closure of pullback and bounded multiplication then
proves naturality and the module identity needed by the boundary mean.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
  (S : X → X) (hS : Measure.QuasiMeasurePreserving S μ μ)

theorem exists_scalarInvariantProjection : Nonempty (ScalarInvariantProjection S hS) := by
  obtain ⟨B, hB, hi, ht⟩ := exists_scalar_shift_limit S hS
    (ContinuousLinearMap.id ℂ (ScalarLInfinity μ)) (fun _ => le_rfl)
  refine ⟨⟨B, hB, ?_, hi, ?_, ht⟩⟩
  · intro f hf
    exact scalarNonnegative_of_weak_limit (fun n => scalarShiftCesaro S hS n f) (B f)
      (scalarNonnegative_shiftCesaro S hS hf) (ht f)
  · intro f hf
    apply scalarInfinityToL2_injective
    apply ext_inner_left ℂ
    intro y
    apply tendsto_nhds_unique (ht f y)
    simpa only [ContinuousLinearMap.id_apply, scalarShiftCesaro_fixed S hS _ f hf] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => inner ℂ y (scalarInfinityToL2 f))
        (Ultrafilter.of (atTop : Filter ℕ) : Filter ℕ) (𝓝 _))

def scalarInvariantProjection : ScalarInvariantProjection S hS :=
  Classical.choice (exists_scalarInvariantProjection S hS)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProductBoundaryLifts
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instIsProbabilityMeasureBilateralWalkPathBilateralWalkLaw _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.ScalarOperatorKernel.toContinuous_apply _root_.OAI.KadisonKastler.UniformMeasurableOperators.coefficientFamily_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.nestedMeanRowsL_apply _root_.OAI.KadisonKastler.scalarBoundaryStar_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Descent to the first boundary coordinate

The product invariant-range theorem supplies an actual L-infinity function
on the product boundary, with unchanged norm. Thus the first-coordinate
invariant projection descends as a bounded linear map.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  (μ : Measure X) (S : X → X) {ν : Measure Y}
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

variable {μ S}

theorem exists_firstBoundaryProjection
    (hS : Measure.QuasiMeasurePreserving S μ μ)
    (P : ScalarInvariantProjection (firstCoordinateShift (Y := Y) S)
      (firstCoordinateShift_quasi (ν := ν) hS)) : Nonempty (FirstBoundaryProjection hS P) := by
  choose E hE using fun f : ScalarLInfinity (μ.prod ν) =>
    exists_firstBoundaryLift_of_measurable μ S (P.toCLM f)
      (scalarInfinity_mem_firstInvariantSigma_of_fixed hS (P.toCLM f) (P.invariant f))
  have hn (f) : ‖E f‖ ≤ ‖f‖ := by
    rw [← firstBoundaryLiftL_norm μ S, hE]
    exact P.norm_le f
  let L : ScalarLInfinity (μ.prod ν) →ₗ[ℂ] ScalarLInfinity ((shiftBoundaryMeasure μ S).prod ν) :=
    { toFun := E
      map_add' f g := by
        apply firstBoundaryLiftL_injective μ S
        rw [map_add, hE, hE, hE, map_add]
      map_smul' c f := by
        simp only [RingHom.id_apply]
        apply firstBoundaryLiftL_injective μ S
        rw [map_smul, hE, hE, map_smul] }
  refine ⟨⟨L.mkContinuous 1 (fun f => ?_), hE⟩⟩
  change ‖E f‖ ≤ 1 * ‖f‖
  simpa using hn f

def firstBoundaryProjection
    (hS : Measure.QuasiMeasurePreserving S μ μ)
    (P : ScalarInvariantProjection (firstCoordinateShift (Y := Y) S)
      (firstCoordinateShift_quasi (ν := ν) hS)) : FirstBoundaryProjection hS P :=
  Classical.choice (exists_firstBoundaryProjection hS P)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ParameterizedBoundaryMean
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instIsProbabilityMeasureBilateralWalkPathBilateralWalkLaw _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_separable _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The random-walk mean with an arbitrary probability parameter

The extra coordinate is left unchanged by the group. The construction is
natural for every nonsingular map of that coordinate, which is the property
needed when combining the two separate boundary means.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory
open scoped BoundedContinuousFunction

variable (G : Type*) [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [TopologicalSpace G] [DiscreteTopology G]
  {Y : Type*} [MeasurableSpace Y] (ν : Measure Y) [IsProbabilityMeasure ν]

def randomWalkParameterizedScalarMean :
    ScalarBoundaryMean ((randomWalkBoundaryAction G).leftOnProduct (ν := ν)) :=
  let P := scalarInvariantProjection (firstCoordinateShift (Y := Y) (randomWalkAdvance G))
    (firstCoordinateShift_quasi (ν := ν) randomWalkAdvance_quasi)
  let E := firstBoundaryProjection randomWalkAdvance_quasi P
  firstBoundaryScalarMean Prod.fst measurable_fst randomWalkAdvance_quasi P E
    ((randomWalkPathAction G).leftOnProduct (ν := ν))
    ((randomWalkBoundaryAction G).leftOnProduct (ν := ν))
    (fun _ _ => rfl) (fun _ _ => rfl)
    (fun g z => Prod.ext (randomWalkAdvance_action G g z.1) rfl)

theorem randomWalkParameterizedScalarMean_natural
    (T : Y → Y) (hT : Measure.QuasiMeasurePreserving T ν ν)
    (F : G →ᵇ ScalarLInfinity ((randomWalkBoundaryMeasure G).prod ν)) :
    (randomWalkParameterizedScalarMean G ν).toCLM
      ((scalarInfinityPullbackL (Prod.map id T)
        (MeasureTheory.QuasiMeasurePreserving.prodMap
          (Measure.QuasiMeasurePreserving.id (randomWalkBoundaryMeasure G)) hT)).compLeftContinuousBounded G F) =
      scalarInfinityPullback (Prod.map id T)
        (MeasureTheory.QuasiMeasurePreserving.prodMap
          (Measure.QuasiMeasurePreserving.id (randomWalkBoundaryMeasure G)) hT)
        ((randomWalkParameterizedScalarMean G ν).toCLM F) := by
  let P := scalarInvariantProjection (firstCoordinateShift (Y := Y) (randomWalkAdvance G))
    (firstCoordinateShift_quasi (ν := ν) randomWalkAdvance_quasi)
  let E := firstBoundaryProjection randomWalkAdvance_quasi P
  let TA : RandomWalkPath G × Y → RandomWalkPath G × Y := Prod.map id T
  let TB : RandomWalkBoundary G × Y → RandomWalkBoundary G × Y := Prod.map id T
  have hTA : Measure.QuasiMeasurePreserving TA ((randomWalkPathLaw G).prod ν)
      ((randomWalkPathLaw G).prod ν) :=
    MeasureTheory.QuasiMeasurePreserving.prodMap (Measure.QuasiMeasurePreserving.id _) hT
  have hTB : Measure.QuasiMeasurePreserving TB ((randomWalkBoundaryMeasure G).prod ν)
      ((randomWalkBoundaryMeasure G).prod ν) :=
    MeasureTheory.QuasiMeasurePreserving.prodMap (Measure.QuasiMeasurePreserving.id _) hT
  let J := firstBoundaryRootL (μ := randomWalkPathLaw G) (ν := ν)
    (S := randomWalkAdvance G) (Prod.fst : RandomWalkPath G → G) measurable_fst
  change E.toCLM (J
    ((scalarInfinityPullbackL TB hTB).compLeftContinuousBounded G F)) =
    scalarInfinityPullback TB hTB (E.toCLM (J F))
  calc
    _ = E.toCLM (scalarInfinityPullback TA hTA (J F)) := congrArg E.toCLM
      (firstBoundaryRootL_natural (μ := randomWalkPathLaw G) (ν := ν)
        (S := randomWalkAdvance G) Prod.fst measurable_fst TA TB hTA hTB
        (fun _ => rfl) (fun _ => rfl) F)
    _ = _ := E.natural TA TB hTA hTB (fun _ => rfl) (fun _ => rfl) (J F)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCoreConjugation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.spatialHilbert_separable _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

theorem regularCoreConjugation_apply_ae (f : RegularCoreHilbert H) :
    regularCoreConjugation U hU J f =ᵐ[volume] fun t =>
      (star (U (Multiplicative.ofAdd t)) : H →L[ℂ] H) (J (f (-t))) := by
  filter_upwards [regularGauge_star_apply_ae U hU (regularReflectedConjugation J f),
    regularReflectedConjugation_apply_ae J f] with t hg hr
  exact hg.trans (congrArg (star (U (Multiplicative.ofAdd t)) : H →L[ℂ] H) hr)

theorem regularCoreConjugation_involutive (hJ : Function.Involutive J)
    (hJU : ∀ t x, J ((U t : H →L[ℂ] H) x) = (U t : H →L[ℂ] H) (J x)) :
    Function.Involutive (regularCoreConjugation U hU J) := by
  intro f
  apply Lp.ext
  filter_upwards [regularCoreConjugation_apply_ae U hU J (regularCoreConjugation U hU J f),
    (Measure.measurePreserving_neg volume).quasiMeasurePreserving.ae_eq_comp
      (regularCoreConjugation_apply_ae U hU J f)] with t ho hi
  simp only [Function.comp_def, neg_neg] at hi
  rw [ho, hi]
  simp only [← Unitary.coe_star, regularGroup_star_eq U (-t), neg_neg]
  rw [hJU, hJ]
  exact congrArg (fun A : H →L[ℂ] H => A (f t))
    (Unitary.star_mul_self_of_mem (U (Multiplicative.ofAdd t)).property)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCoreCovariance
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

theorem regularTranslation_embedding (s : Multiplicative ℝ) (a : H →L[ℂ] H) :
    (regularRightTranslation (H := H) s : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) *
        regularCoreEmbedding U hU a =
      regularCoreEmbedding U hU (unitaryConj (star (U s)) a) *
        (regularRightTranslation (H := H) s : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [regularRightTranslation_apply_ae s (regularCoreEmbedding U hU a f),
    (measurePreserving_add_right (volume : Measure ℝ) s.toAdd).quasiMeasurePreserving.ae_eq_comp
      (regularCoreEmbedding_apply_ae U hU a f),
    regularCoreEmbedding_apply_ae U hU (unitaryConj (star (U s)) a)
      ((regularRightTranslation (H := H) s :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f),
    regularRightTranslation_apply_ae s f] with t hρ hπ hright hf
  simp only [Function.comp_def] at hπ
  change (regularRightTranslation (H := H) s :
    RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (regularCoreEmbedding U hU a f) t =
      regularCoreEmbedding U hU (unitaryConj (star (U s)) a)
        ((regularRightTranslation (H := H) s :
          RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f) t
  rw [hρ, hπ, hright, hf]
  have he : U (Multiplicative.ofAdd (t + s.toAdd)) = U s * U (Multiplicative.ofAdd t) := by
    rw [add_comm]
    exact map_mul U s (Multiplicative.ofAdd t)
  rw [he, Submonoid.coe_mul, star_mul]
  simp only [unitaryConj, Unitary.coe_star, star_star, mul_apply_eq_comp]

theorem regularCoreMonomial_mul (a b : H →L[ℂ] H) (s t : Multiplicative ℝ) :
    regularCoreMonomial U hU a s * regularCoreMonomial U hU b t =
      regularCoreMonomial U hU (a * unitaryConj (star (U s)) b) (s * t) := by
  unfold regularCoreMonomial
  calc
    _ = regularCoreEmbedding U hU a *
        (((regularRightTranslation (H := H) s :
          RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) * regularCoreEmbedding U hU b) *
            (regularRightTranslation (H := H) t :
              RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)) := by simp only [mul_assoc]
    _ = regularCoreEmbedding U hU a *
        ((regularCoreEmbedding U hU (unitaryConj (star (U s)) b) *
          (regularRightTranslation (H := H) s :
            RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)) *
              (regularRightTranslation (H := H) t :
                RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)) := by
      rw [regularTranslation_embedding U hU]
    _ = (regularCoreEmbedding U hU a *
        regularCoreEmbedding U hU (unitaryConj (star (U s)) b)) *
          ((regularRightTranslation (H := H) s :
            RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) *
              (regularRightTranslation (H := H) t :
                RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)) := by simp only [mul_assoc]
    _ = _ := by
      rw [← map_mul]
      congr 1
      exact congrArg Subtype.val (map_mul (regularRightTranslation (H := H)) s t).symm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCoreMonomials
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instOne _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.ScalarInvariantMean.stateOrbitScalar_apply _root_.OAI.KadisonKastler.hardyEvaluationAt_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Algebraic generation by regular monomials

The core's algebraic generators reduce to finite linear combinations of
one original-algebra coefficient followed by one translation. This is
the dense algebra used to compute the frequency-window trace.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
  (M : VonNeumannAlgebra H)

def regularCoreMonomials
    (hM : ∀ s a, a ∈ M → unitaryConj (U s) a ∈ M) :
    Submonoid (RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) where
  carrier := {T | ∃ a ∈ M, ∃ s, regularCoreMonomial U hU a s = T}
  one_mem' := ⟨1, M.one_mem, 1, by simp [regularCoreMonomial]⟩
  mul_mem' := by
    rintro _ _ ⟨a, ha, s, rfl⟩ ⟨b, hb, t, rfl⟩
    refine ⟨a * unitaryConj (star (U s)) b, M.mul_mem ha ?_, s * t,
      (regularCoreMonomial_mul U hU a b s t).symm⟩
    rw [Unitary.star_eq_inv, ← map_inv]
    exact hM _ b hb

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RootBoundaryMeanConstruction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instIsProbabilityMeasureBilateralWalkPathBilateralWalkLaw _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The scalar boundary mean from rooted shift averages

Selection at the root is equivariant because the root translates by left
multiplication. The positive invariant projection then descends the
averages to the invariant boundary, with the exact module and action
identities required by `ScalarBoundaryMean`.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory
open scoped BoundedContinuousFunction

variable {X G : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
  {S : X → X} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [TopologicalSpace G] [DiscreteTopology G]
  (r : X → G) (hr : Measurable r)

variable (G)

/-- The original action of the countable group on its random-walk boundary
has the exact scalar mean needed by the stability argument. -/
def randomWalkScalarBoundaryMean : ScalarBoundaryMean (randomWalkBoundaryAction G) :=
  rootedScalarBoundaryMean (μ := randomWalkPathLaw G) (S := randomWalkAdvance G)
    Prod.fst measurable_fst randomWalkAdvance_quasi
    (scalarInvariantProjection (randomWalkAdvance G) randomWalkAdvance_quasi)
    (randomWalkPathAction G) (randomWalkAdvance_action G) (fun _ _ => rfl)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_StarEquivTraceTransport
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.varyingSequenceCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Tracial and bounded strong transport by a factor isomorphism

Uniqueness of the normalized finite-factor trace makes an algebraic
star-isomorphism preserve the tracial two-norm. The concrete finite-vector
trace formulas then give strong-operator continuity on every bounded ball,
in both directions. No continuity of the isomorphism is assumed.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}

/-- An algebraic star-isomorphism out of a II₁ factor preserves normalized
faithful tracial states. -/
theorem trace_starAlgEquiv
    (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (τM : FaithfulTracialState (Algebra M)) (τN : FaithfulTracialState (Algebra N))
    (e : Algebra M ≃⋆ₐ[ℂ] Algebra N) (x : Algebra M) :
    τN.toLinearMap (e x) = τM.toLinearMap x := by
  exact faithfulTracialState_unique hM (τN.comapStarAlgEquiv e) τM x

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SwappedBoundaryMean
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instIsProbabilityMeasureBilateralWalkPathBilateralWalkLaw _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Transporting the scalar mean to the second coordinate -/

namespace KadisonKastler

noncomputable section

open MeasureTheory
open scoped BoundedContinuousFunction

variable {G D : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace D] {μ : Measure D} [IsProbabilityMeasure μ]

variable (G) [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]

def randomWalkSecondScalarMean :
    ScalarBoundaryMean ((randomWalkBoundaryAction G).rightOnProduct) :=
  swappedScalarBoundaryMean
    (randomWalkParameterizedScalarMean G (randomWalkBoundaryMeasure G))
    ((randomWalkBoundaryAction G).rightOnProduct) (fun _ _ => rfl)

theorem randomWalkSecondScalarMean_natural (g : G)
    (F : G →ᵇ ScalarLInfinity ((randomWalkBoundaryMeasure G).prod (randomWalkBoundaryMeasure G))) :
    (randomWalkSecondScalarMean G).toCLM
      ((scalarInfinityPullbackL
        (((randomWalkBoundaryAction G).leftOnProduct (ν := randomWalkBoundaryMeasure G)).toPerm g)
        (((randomWalkBoundaryAction G).leftOnProduct (ν := randomWalkBoundaryMeasure G)).quasi g)).compLeftContinuousBounded G F) =
      scalarInfinityPullback
        (((randomWalkBoundaryAction G).leftOnProduct (ν := randomWalkBoundaryMeasure G)).toPerm g)
        (((randomWalkBoundaryAction G).leftOnProduct (ν := randomWalkBoundaryMeasure G)).quasi g)
        ((randomWalkSecondScalarMean G).toCLM F) := by
  let a := randomWalkBoundaryAction G
  let L := a.leftOnProduct (ν := randomWalkBoundaryMeasure G)
  let R := a.rightOnProduct
  let m := randomWalkParameterizedScalarMean G (randomWalkBoundaryMeasure G)
  have hF : scalarSwapFamilyL ((scalarInfinityPullbackL (L.toPerm g) (L.quasi g)).compLeftContinuousBounded G F) =
      (scalarInfinityPullbackL (R.toPerm g) (R.quasi g)).compLeftContinuousBounded G (scalarSwapFamilyL F) := by
    apply BoundedContinuousFunction.ext
    intro t
    exact scalarProductSwapL_intertwine (L.toPerm g) (R.toPerm g) (L.quasi g) (R.quasi g)
      (fun _ => rfl) (F t)
  change scalarProductSwapL (m.toCLM (scalarSwapFamilyL
    ((scalarInfinityPullbackL (L.toPerm g) (L.quasi g)).compLeftContinuousBounded G F))) =
    scalarInfinityPullback (L.toPerm g) (L.quasi g)
      (scalarProductSwapL (m.toCLM (scalarSwapFamilyL F)))
  rw [hF]
  have hm := randomWalkParameterizedScalarMean_natural G (randomWalkBoundaryMeasure G)
    (a.toPerm g) (a.quasi g) (scalarSwapFamilyL F)
  change m.toCLM ((scalarInfinityPullbackL (R.toPerm g) (R.quasi g)).compLeftContinuousBounded G
    (scalarSwapFamilyL F)) = scalarInfinityPullback (R.toPerm g) (R.quasi g)
      (m.toCLM (scalarSwapFamilyL F)) at hm
  rw [hm]
  exact scalarProductSwapL_intertwine (R.toPerm g) (L.toPerm g) (R.quasi g) (L.quasi g)
    (fun _ => rfl) _

end

end KadisonKastler

end OAI
end


