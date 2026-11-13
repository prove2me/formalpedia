-- Prove2me | Definitions.Def_Q260K005
-- name    : Q260K005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T04:35:10.874352+00:00
-- url     : https://prove2.me/theorems/71928b06-fd9b-4876-a317-0a6580429faf
-- title:
--   Definitions bundle Q260K005 of the split of OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 317 declarations of OpenAI's Lean: 116 definitions, 3 inductive types or structures, 5 instances and 193 theorems. The definitions and types are `OAI.KadisonKastler.HaagerupBound`, `OAI.KadisonKastler.HasCountableProjectionFamilies`, `OAI.KadisonKastler.HasHilbertSumFields`, `OAI.KadisonKastler.IsCentralSupportFamily`, `OAI.KadisonKastler.IsInjective`, `OAI.KadisonKastler.IsPrimeAlgebra`, `OAI.KadisonKastler.MatrixNearInclusion`, `OAI.KadisonKastler.MatrixNearInclusion.matrixNearOrder`, `OAI.KadisonKastler.MatrixSiteBlockIndex`, `OAI.KadisonKastler.MatrixSiteLetter`, `OAI.KadisonKastler.MatrixSiteWord`, `OAI.KadisonKastler.MatrixSiteWord.eval`, `OAI.KadisonKastler.MatrixSiteWord.evalOption`, `OAI.KadisonKastler.MatrixSiteWord.indices`, `OAI.KadisonKastler.MatrixSiteWord.insert`, `OAI.KadisonKastler.MatrixSiteWord.reduce`, `OAI.KadisonKastler.MatrixSiteWord.reindex`, `OAI.KadisonKastler.MatrixSiteWord.star`, `OAI.KadisonKastler.NonunitalFiberScalarCenter`, `OAI.KadisonKastler.NormGeneratedExtension`, `OAI.KadisonKastler.PointedLocalHilbert`, `OAI.KadisonKastler.PointedPowerConfiguration`, `OAI.KadisonKastler.PointedPowerHilbert`, `OAI.KadisonKastler.PointedPowerTail`, `OAI.KadisonKastler.PointedPowerTailHilbert`, `OAI.KadisonKastler.PointedRawHilbert`, `OAI.KadisonKastler.PrefixStrongTests`, `OAI.KadisonKastler.PreservesJordan`, `OAI.KadisonKastler.ProductStateCentralizes`, `OAI.KadisonKastler.PublishedUnitaryBorelSelection`, `OAI.KadisonKastler.RationalConvexExpr`, `OAI.KadisonKastler.RationalConvexExpr.eval`, `OAI.KadisonKastler.ResolventCyclicL2`, `OAI.KadisonKastler.ScalarInvariantMean.evaluationHom`, `OAI.KadisonKastler.ScalarInvariantMean.invariantMeanFamilyCStar`, `OAI.KadisonKastler.ScalarInvariantMean.invariantMeanFamilyOrder`, `OAI.KadisonKastler.ScalarInvariantMean.translateFamily`, `OAI.KadisonKastler.SeparableSeeds`, `OAI.KadisonKastler.SeparableSeeds.Extends`, `OAI.KadisonKastler.SmallAssociativeProduct` and 79 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `KadisonKastler_AbelianCesaro`, `KadisonKastler_AbelianInvariantMean`, `KadisonKastler_Amenable`, `KadisonKastler_AnalyticAlgebraBounds`, `KadisonKastler_AveragedRangeDescent`, `KadisonKastler_BaireMeasurableBranch`, `KadisonKastler_BilateralBlockWords`, `KadisonKastler_BlockCommutantConstruction`, `KadisonKastler_BoundaryBoundedTransport`, `KadisonKastler_BoundaryDiagonal`, `KadisonKastler_BoundaryDiagonalMeasurable`, `KadisonKastler_BoundaryImprovement`, `KadisonKastler_BoundaryIntertwiner`, `KadisonKastler_BoundaryPolarMeasurable`, `KadisonKastler_BoundaryPolarTrace`, `KadisonKastler_BoundedFamilyCurry`, `KadisonKastler_CentralSupportCover`, `KadisonKastler_CocycleMetric`, `KadisonKastler_CommonRightAction`, `KadisonKastler_CommonSpectralMeasurable`, `KadisonKastler_CompletelyBounded`, `KadisonKastler_CompletelyPositive`, `KadisonKastler_CountableProjectionFamilies`, `KadisonKastler_CountableUnitaryL2`, `KadisonKastler_CyclicGeneratorSpan`, `KadisonKastler_CyclicGramEquivalence`, `KadisonKastler_DerivationExtensionFactor`, `KadisonKastler_ExponentialCommutator`, `KadisonKastler_FaithfulRepresentation`, `KadisonKastler_FieldCoordinateCenters`, `KadisonKastler_FourierL1Uniqueness`, `KadisonKastler_FourierLaplace`, `KadisonKastler_GeometricCorrectionScale`, `KadisonKastler_Haagerup`, `KadisonKastler_HaagerupCochains`, `KadisonKastler_HilbertDefect`, `KadisonKastler_HilbertRows`, `KadisonKastler_HilbertVariance`, `KadisonKastler_HorizontalStripGluing`, `KadisonKastler_InvariantOperatorMean`, `KadisonKastler_Jordan`, `KadisonKastler_KMSScalarStrip`, `KadisonKastler_L2LinearFields`, `KadisonKastler_L2MeasurableExtension`, `KadisonKastler_L2PartitionCoordinates`, `KadisonKastler_LocalLaplaceUniqueness`, `KadisonKastler_MatrixBlockSwap`, `KadisonKastler_MatrixNearInclusion`, `KadisonKastler_MatrixProductStateSwap`, `KadisonKastler_MeasurableConullRepresentations`, `KadisonKastler_MeasurableStrongTests`, `KadisonKastler_MinimalResidualFamily`, `KadisonKastler_MinimalSpatialImplementer`, `KadisonKastler_ModularPositiveCone`, `KadisonKastler_MultiplicationCorrectionSequence`, `KadisonKastler_MultiplicationNewtonStep`, `KadisonKastler_NonunitalFiberCenter`, `KadisonKastler_OperatorCochainStar`, `KadisonKastler_PairedRepresentations`, `KadisonKastler_PeriodicStripExtension`, `KadisonKastler_PointedFiniteBlock`, `KadisonKastler_PointedLocalMatrix`, `KadisonKastler_PointedMatrixSum`, `KadisonKastler_PointedPowerConfigurations`, `KadisonKastler_PointedSitesTransport`, `KadisonKastler_PointedWordReduction`, `KadisonKastler_PolishConjugacyRelation`, `KadisonKastler_ProductIntegralUniqueness`, `KadisonKastler_ProductInvariantIntegrals`, `KadisonKastler_ProductStateCentralizer`, `KadisonKastler_PublishedBorelSelection`, `KadisonKastler_RandomWalkPrefix`, `KadisonKastler_RealLaplaceUniqueness`, `KadisonKastler_RegularCoreCharacters`, `KadisonKastler_RegularCoreOperators`, `KadisonKastler_RegularCoreRepresentation`, `KadisonKastler_RegularizedModularGroup`, `KadisonKastler_RemoteSiteDoubling`, `KadisonKastler_ResolventCyclicModel`, `KadisonKastler_ResolventVectorMeasure`, `KadisonKastler_SeparableAlgebraPair`, `KadisonKastler_StarCorrection`, `KadisonKastler_StateScalingAlgebra`, `KadisonKastler_StripAverageKernel`, `KadisonKastler_StripContourBoundary`, `KadisonKastler_StripKernelMass`, `KadisonKastler_StripSineQuotient`, `KadisonKastler_StrongContractionLimits`, `KadisonKastler_StrongUnitaryCoordinates`, `KadisonKastler_TomitaCentralizerGraph`, `KadisonKastler_Transport`, `KadisonKastler_UCPDescent`, `KadisonKastler_WeakFieldKernel`, `KadisonKastler_WeakFieldSpectralSupport`, `KadisonKastler_WeakHilbertConvexLimit`, `KadisonSimilarity_Representation_AERepresentationAgreement`, `KadisonSimilarity_Representation_AEStarRepresentation`, `KadisonSimilarity_Representation_ConullStarRepresentations`, `KadisonSimilarity_Representation_CountableDenseStarSubring`, `KadisonSimilarity_Representation_DenseStarRepresentation`, `KadisonSimilarity_Representation_DiagonalFiberRepresentations`, `KadisonSimilarity_Representation_DiagonalFieldAction`, `KadisonSimilarity_Representation_DiagonalFieldAdjoint`, `KadisonSimilarity_Representation_DiagonalFieldAlgebra`, `KadisonSimilarity_Representation_UnitalizedExtension`, `TracialSplitting_SpatialTensor`.
--
--   **Imports.** It imports the bundle `OAIQ075A029` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q260K011`, `Q260K012`, `Q260K013`, `Q260K014` and `Q260K015`; the statements `OAI.KadisonKastler.HaagerupBound.right_slice`, `OAI.KadisonKastler.HaagerupBound.smul`, `OAI.KadisonKastler.PreservesJordan.multiplicative_of_close_of_II1`, `OAI.KadisonKastler.cochain_coboundary_weak_limit`, `OAI_KadisonKastler_exists_ambient_product_state_of_simple`, `OAI_KadisonKastler_exists_selfAdjoint_split_of_factor`, `OAI.KadisonKastler.exists_selfAdjoint_split_of_factor_commutant`, `OAI.KadisonKastler.exists_unitary_boundary_intertwiner`, `OAI.KadisonKastler.extension_implementer_mem_of_spatial_split`, `OAI.KadisonKastler.factor_of_extreme_signed_derivation_extension`, `OAI.KadisonKastler.finiteFactor_isPrimeAlgebra`, `OAI.KadisonKastler.preservesJordan_of_map_unitary` and `OAI_KadisonKastler_simple_extension_implementer_mem_range`; the proofs of `OAI.KadisonKastler.HaagerupBound.smul`, `OAI.KadisonKastler.PreservesJordan.multiplicative_of_close_of_II1`, `OAI.KadisonKastler.cochain_coboundary_weak_limit` and `OAI.KadisonKastler.preservesJordan_of_map_unitary`.
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
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Group.End
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
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Interval.Set.Group
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Star.Module
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Star.Unitary
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
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.RealImaginaryPart
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Analysis.CStarAlgebra.Exponential
import Mathlib.Analysis.CStarAlgebra.GelfandDuality
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Analysis.CStarAlgebra.SpecialFunctions.PosPart
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.CStarAlgebra.Unitization
import Mathlib.Analysis.Calculus.Deriv.Basic
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
import Mathlib.Analysis.Convex.Cone.Closure
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
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.MeanErgodic
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.Analysis.LocallyConvex.WeakOperatorTopology
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
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
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Isometric
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Data.Finsupp.Single
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.Chain
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.Range
import Mathlib.Data.List.Sublists
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Composition
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Find
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
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
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
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Logic.Equiv.Nat
import Mathlib.Logic.Equiv.Option
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Set
import Mathlib.Logic.Equiv.Sum
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Cylinders
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
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.Trim
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.WithDensityFinite
import Mathlib.MeasureTheory.VectorMeasure.WithDensity
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.Bounds.OrderIso
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.Probability.Distributions.Cauchy
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Moments.ComplexMGF
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
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.Star
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
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.ProperSpace.Real
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.ThickenedIndicator
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
import Definitions.Def_OAIQ075A029

section
-- module Solutions.OAIQ075_KS.Compat
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BoundaryImprovement
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The quadratic step in boundary cocycle correction

Only the structural properties of the boundary mean occur here.  The mean
need not be normal.  Covariance cancellation and polar normalization give
the quadratic improvement used in the measurable iteration.
-/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

universe u v

variable {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]

section Transport

variable {G : Type*} [Group G]

/-- The transport field used before averaging an approximate cocycle. -/
def boundaryTransport (α : G →* (B ≃⋆ₐ[ℂ] B)) (V : G → unitary B) (g t : G) : B :=
  (V t : B) * α g (star (V (g⁻¹ * t) : B))

/-- The transport fields are unitary before averaging. -/
theorem boundaryTransport_mem_unitary (α : G →* (B ≃⋆ₐ[ℂ] B))
    (V : G → unitary B) (g t : G) : boundaryTransport α V g t ∈ unitary B := by
  exact mul_mem (V t).property
    (Unitary.map_mem (α g) (star (V (g⁻¹ * t))).property)

end Transport

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CocycleMetric
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The complete metric space of uniformly bounded unitary families

The cocycle defect is continuous for the uniform norm. This supplies the
metric-space part of the boundary correction iteration.
-/

namespace KadisonKastler

open scoped BoundedContinuousFunction

noncomputable section

variable {G B : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable [CStarAlgebra B]

local instance instCompleteSpaceSubtypeBoundedContinuousFunctionMemSubmonoidUnitary_solutions_ra8bd29_1 : CompleteSpace (unitary (G →ᵇ B)) := isClosed_unitary.completeSpace_coe
/-- Evaluation of an actual uniformly bounded unitary family. -/
def unitaryFamilyEval (V : unitary (G →ᵇ B)) (g : G) : unitary B :=
  ⟨V.val g, by
    have h₁ := congrArg (fun f : G →ᵇ B => f g)
      (Unitary.star_mul_self_of_mem V.property)
    have h₂ := congrArg (fun f : G →ᵇ B => f g)
      (Unitary.mul_star_self_of_mem V.property)
    exact ⟨h₁, h₂⟩⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BoundaryBoundedTransport
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Bounded transport fields and the correction step

For an action on a C-star algebra, the transport fields are actual bounded
unitary families.  An equivariant bimodule mean therefore gives the quadratic
step in the complete metric space of unitary families.
-/

namespace KadisonKastler

open scoped BoundedContinuousFunction CStarAlgebra

noncomputable section

variable {G B : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable [CStarAlgebra B]

local instance boundaryBoundedCStar : CStarAlgebra (G →ᵇ B) where

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_Transport
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# Transport and correction of multiplication

These are the algebraic and norm estimates in the UCP criterion of §2 of
*Universal strong Kadison–Kastler stability* (2026). No perturbation theorem
is assumed here. If a linear equivalence correcting the transported product
is supplied, its composition with the original map gives an actual algebra
equivalence.
-/

namespace KadisonKastler

noncomputable section

variable {A B : Type*} [NormedRing A] [NormedAlgebra ℂ A]
  [NormedRing B] [NormedAlgebra ℂ B]

/-- Multiplication on the source transported through a linear equivalence. -/
def transportedMul (F : A ≃ₗ[ℂ] B) (x y : A) : A := F.symm (F x * F y)

@[simp] theorem map_transportedMul (F : A ≃ₗ[ℂ] B) (x y : A) :
    F (transportedMul F x y) = F x * F y := F.apply_symm_apply _

theorem transportedMul_add_left (F : A ≃ₗ[ℂ] B) (x y z : A) :
    transportedMul F (x + y) z = transportedMul F x z + transportedMul F y z := by
  simp only [transportedMul, map_add, add_mul]

theorem transportedMul_add_right (F : A ≃ₗ[ℂ] B) (x y z : A) :
    transportedMul F x (y + z) = transportedMul F x y + transportedMul F x z := by
  simp only [transportedMul, map_add, mul_add]

theorem transportedMul_smul_left (F : A ≃ₗ[ℂ] B) (c : ℂ) (x y : A) :
    transportedMul F (c • x) y = c • transportedMul F x y := by
  simp only [transportedMul, map_smul, smul_mul_assoc]

theorem transportedMul_smul_right (F : A ≃ₗ[ℂ] B) (c : ℂ) (x y : A) :
    transportedMul F x (c • y) = c • transportedMul F x y := by
  simp only [transportedMul, map_smul, mul_smul_comm]

/-- A correction intertwines the transported product and the original one;
its inverse intertwines them in the opposite direction. -/
theorem inverse_correction_mul (F : A ≃ₗ[ℂ] B) (L : A ≃ₗ[ℂ] A)
    (hL : ∀ x y, L (transportedMul F x y) = L x * L y) (x y : A) :
    L.symm (x * y) = transportedMul F (L.symm x) (L.symm y) := by
  apply L.injective
  rw [L.apply_symm_apply, hL, L.apply_symm_apply, L.apply_symm_apply]

/-- The map `F ∘ L⁻¹` is multiplicative after correction. -/
theorem correctedMap_mul (F : A ≃ₗ[ℂ] B) (L : A ≃ₗ[ℂ] A)
    (hL : ∀ x y, L (transportedMul F x y) = L x * L y) (x y : A) :
    F (L.symm (x * y)) = F (L.symm x) * F (L.symm y) := by
  rw [inverse_correction_mul F L hL, map_transportedMul]

/-- Bijective multiplicativity ensures the corrected map preserves the unit;
unit preservation of the original linear maps need not be assumed. -/
theorem correctedMap_one (F : A ≃ₗ[ℂ] B) (L : A ≃ₗ[ℂ] A)
    (hL : ∀ x y, L (transportedMul F x y) = L x * L y) :
    F (L.symm 1) = 1 := by
  obtain ⟨x, hx⟩ := (L.symm.trans F).surjective (1 : B)
  have h := correctedMap_mul F L hL 1 x
  change F (L.symm x) = 1 at hx
  simpa only [one_mul, hx, mul_one] using h.symm

/-- The genuine algebra equivalence resulting from a correction of the
transported product. Its underlying map is exactly `F ∘ L⁻¹`. -/
def correctedAlgEquiv (F : A ≃ₗ[ℂ] B) (L : A ≃ₗ[ℂ] A)
    (hL : ∀ x y, L (transportedMul F x y) = L x * L y) : A ≃ₐ[ℂ] B :=
  AlgEquiv.ofLinearEquiv (L.symm.trans F) (correctedMap_one F L hL)
    (correctedMap_mul F L hL)

@[simp] theorem correctedAlgEquiv_apply (F : A ≃ₗ[ℂ] B) (L : A ≃ₗ[ℂ] A)
    (hL : ∀ x y, L (transportedMul F x y) = L x * L y) (x : A) :
    correctedAlgEquiv F L hL x = F (L.symm x) := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CompletelyBounded
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# Matrix bounds for perturbation maps

All norms here are the C*-matrix norms, including for rectangular matrices.
The rectangular formulation records exactly the estimates needed for the
Haagerup product norm in the multiplication-correction argument.
-/

namespace KadisonKastler

noncomputable section

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- The row-column defect of the transported multiplication. This is the
concrete inequality used to invoke the published multiplication theorem. -/
def TransportedProductBound (F : A ≃ₗ[ℂ] B) (c : ℝ) : Prop :=
  ∀ (p r q : ℕ) (X : CStarMatrix (Fin p) (Fin r) A)
      (Y : CStarMatrix (Fin r) (Fin q) A),
    ‖CStarMatrix.mapₗ F.symm.toLinearMap
        (CStarMatrix.mapₗ F.toLinearMap X * CStarMatrix.mapₗ F.toLinearMap Y) -
        X * Y‖ ≤ c * ‖X‖ * ‖Y‖

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CompletelyPositive
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# Contractivity of unital completely positive maps

The proofs use Mathlib's completely positive maps and the spectral order
on C⋆-matrices. The Schwarz inequality is obtained from positivity of a
two-by-two Gram matrix.
-/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- The positive Gram matrix used for the Schwarz inequality. -/
def schwarzGram (a : A) : CStarMatrix (Fin 2) (Fin 2) A :=
  CStarMatrix.ofMatrix !![star a * a, star a; a, 1]

theorem schwarzGram_nonneg (a : A) : 0 ≤ schwarzGram a := by
  let V : CStarMatrix (Fin 2) (Fin 2) A := CStarMatrix.ofMatrix !![a, 1; 0, 0]
  have hfactor : schwarzGram a = star V * V := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [schwarzGram, V, CStarMatrix.mul_apply, CStarMatrix.star_eq_conjTranspose,
        CStarMatrix.conjTranspose_apply, Fin.sum_univ_two]
  rw [hfactor]
  exact star_mul_self_nonneg _

/-- Complete positivity already forces preservation of the involution. -/
theorem completelyPositive_map_star (φ : A →CP B) (a : A) :
    φ (star a) = star (φ a) := by
  let P := (schwarzGram a).map φ
  have hP : 0 ≤ P := φ.map_cstarMatrix_nonneg _ (schwarzGram_nonneg a)
  have h := congrArg (fun N : CStarMatrix (Fin 2) (Fin 2) B => N 0 1) hP.star_eq
  simpa [P, schwarzGram, CStarMatrix.star_eq_conjTranspose,
    CStarMatrix.conjTranspose_apply] using h.symm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FaithfulRepresentation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# Faithful representations are completely isometric

Injective star-algebra homomorphisms preserve C⋆-norms at each square
matrix level. The isometric corner embedding then gives the same statement
for every rectangular matrix size used in the perturbation estimates.
-/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

variable [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
/-- Applying a faithful star homomorphism entrywise remains injective. -/
theorem injective_starAlgHom_matrix (φ : A →⋆ₐ[ℂ] B) (hφ : Function.Injective φ)
    {n : Type*} [Fintype n] :
    Function.Injective (CStarMatrix.mapₙₐ (n := n) φ.toNonUnitalStarAlgHom) := by
  intro X Y hXY
  ext i j
  exact hφ (congrArg (fun Z : CStarMatrix n n B => Z i j) hXY)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_InvariantOperatorMean
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance invariantMeanFamilyCStar : CStarAlgebra (G →ᵇ (H →L[ℂ] H)) where

/-- Translation invariance survives the coefficient construction. -/
def translateFamily (g : G) (F : G →ᵇ (H →L[ℂ] H)) : G →ᵇ (H →L[ℂ] H) :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun t => F (g⁻¹ * t)) ‖F‖ (fun _ => F.norm_coe_le_norm _)

local instance invariantMeanFamilyOrder : PartialOrder (G →ᵇ (H →L[ℂ] H)) :=
  CStarAlgebra.spectralOrder _
local instance invariantMeanFamilyStarOrder : StarOrderedRing (G →ᵇ (H →L[ℂ] H)) :=
  CStarAlgebra.spectralOrderedRing _

def evaluationHom (g : G) : (G →ᵇ (H →L[ℂ] H)) →⋆ₐ[ℂ] (H →L[ℂ] H) where
  toFun := fun F => F g
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

end ScalarInvariantMean

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_AbelianCesaro
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Finite Cesaro averages in an abelian group

Iterating the one-generator averages over a finite list gives positive
contractions. A translation by any generator in the list changes the
average by at most twice the reciprocal averaging length.
-/

namespace KadisonKastler

open scoped BigOperators BoundedContinuousFunction

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [DiscreteTopology G]

omit [CommGroup G] [TopologicalSpace G] [DiscreteTopology G] in
theorem norm_inv_nat_smul_sub_le {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℂ E] (n : ℕ) (x y : E) (hxy : ‖x‖ ≤ ‖y‖) :
    ‖(((n + 1 : ℕ) : ℝ)⁻¹ : ℂ) • (x - y)‖ ≤
      2 * (((n + 1 : ℕ) : ℝ)⁻¹) * ‖y‖ := by
  have hp : 0 ≤ ((n + 1 : ℕ) : ℝ)⁻¹ := by positivity
  rw [norm_smul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (n + 1))]
  calc
    _ ≤ ((n + 1 : ℕ) : ℝ)⁻¹ * (‖x‖ + ‖y‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) hp
    _ ≤ ((n + 1 : ℕ) : ℝ)⁻¹ * (‖y‖ + ‖y‖) :=
      mul_le_mul_of_nonneg_left (add_le_add hxy le_rfl) hp
    _ = _ := by ring

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_AbelianInvariantMean
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

def abelianMeanFilter (G : Type*) [CommGroup G] : Ultrafilter (Finset G × ℕ) := by
  classical
  exact Ultrafilter.of atTop

omit [TopologicalSpace G] [DiscreteTopology G] in
theorem abelianMeanFilter_le :
    ((abelianMeanFilter G) : Filter (Finset G × ℕ)) ≤ atTop := by
  classical
  exact Ultrafilter.of_le atTop

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_Amenable
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# Conditional strong stability for injective represented algebras

The hypothesis `ChristensenMutual` is the mutual near-inclusion
consequence of Cameron–Christensen–Sinclair–Smith–White–Wiggins,
*Kadison–Kastler stable factors*, Duke Math. J. 163 (2014), Theorem 3.3(i),
building on Christensen, *Near inclusions of C*-algebras* (1980).
The stability theorem is conditional on this near-inclusion property.
-/

namespace KadisonKastler

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Injectivity in the given representation, expressed as a contractive linear
projection of the ambient bounded operators onto the algebra. Normality of the
projection is not required. -/
def IsInjective (M : VonNeumannAlgebra H) : Prop :=
  ∃ E : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H),
    ‖E‖ ≤ 1 ∧ (∀ x, E x ∈ M) ∧ ∀ x ∈ M, E x = x

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BoundaryIntertwiner
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Averaging and polar normalization of a boundary intertwiner

A supplied equivariant bimodule mean gives a near-identity semilinear
intertwiner. Continuous functional calculus passes its transformation law
to the unitary polar factor.
-/

namespace KadisonKastler

open scoped CStarAlgebra BoundedContinuousFunction

noncomputable section

variable {B : Type*} [CStarAlgebra B]
local instance boundaryIntertwinerOrder : PartialOrder B := CStarAlgebra.spectralOrder B
local instance boundaryIntertwinerStarOrder : StarOrderedRing B :=
  CStarAlgebra.spectralOrderedRing B

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
local instance boundaryIntertwinerFunctionCStar : CStarAlgebra (G →ᵇ B) where

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PairedRepresentations
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# Close representations from the published commutant-distance formula

The explicit input `PublishedBlockCommutantApproximation` is the block
specialization of Arveson's distance formula, in the form of Christensen,
*Perturbations of operator algebras II*, Indiana Univ. Math. J. 26 (1977),
Proposition 2.1. See also Christensen--Sinclair--Smith--White,
*Perturbations of C*-algebraic invariants*, GAFA 20 (2010), equation (2.1),
and Cameron et al., *Kadison--Kastler stable factors* (2014), equation (2.2).

The 2010 formulation applies to represented C*-algebras. Passing through
the quotient by the representation kernel gives the formulation below
with the complete bound on the source algebra. No normality is required.
-/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

variable {R : Type*} [Ring R] [Algebra ℂ R]

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

variable [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

variable (A) (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

local instance instPartialOrderContinuousLinearMapComplexId_solutions : PartialOrder (K →L[ℂ] K) := CStarAlgebra.spectralOrder _
local instance instStarOrderedRingContinuousLinearMapComplexId_solutions : StarOrderedRing (K →L[ℂ] K) := CStarAlgebra.spectralOrderedRing _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_HilbertRows
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Products of operator rows on finite Hilbert sums -/

namespace KadisonKastler

open Finset

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {I J : Type*} [Fintype I] [Fintype J]

local instance hilbertRowOrder_ra8bd29_1 : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
local instance hilbertRowStarOrder_ra8bd29_1 : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _
def operatorRow (C : I → H →L[ℂ] H) : CStarMatrix Unit I (H →L[ℂ] H) :=
  CStarMatrix.ofMatrix (fun _ i => C i)

omit [CompleteSpace H] [Fintype I] in
@[simp]
theorem operatorRow_apply (C : I → H →L[ℂ] H) (u : Unit) (i : I) :
    operatorRow C u i = C i := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BoundaryDiagonal
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Pointwise diagonal comparison in a finite algebra

The least-norm argument is carried out in a supplied faithful tracial
Hilbert realization. Bounded completeness of the concrete finite algebra
keeps Hilbert limits in the operator algebra. No measurable selection or
existence of a boundary space is asserted here.
-/

namespace KadisonKastler

open Filter Set
open scoped Topology

noncomputable section


section Polar

variable {B : Type*} [CStarAlgebra B]
local instance boundaryDiagonalOrder : PartialOrder B := CStarAlgebra.spectralOrder B
local instance boundaryDiagonalStarOrder : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B

end Polar


end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BoundaryDiagonalMeasurable
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Measurability of diagonal least-norm vectors

Finite rational convex expressions form a countable dense subset of each
closed convex hull. Choosing the first expression within a specified
squared-norm tolerance gives measurable approximants; the parallelogram
identity forces their convergence to the unique least vector.
-/

namespace KadisonKastler

open Filter Set MeasureTheory TopologicalSpace
open scoped Topology

noncomputable section

/-- A countable syntax for rational convex combinations. Clamping the
rational parameter avoids proof fields in the syntax. -/
inductive RationalConvexExpr (ι : Type*) where
  | leaf : ι → RationalConvexExpr ι
  | blend : ℚ → RationalConvexExpr ι → RationalConvexExpr ι → RationalConvexExpr ι
  deriving Countable

def convexParameter (t : ℝ) : ℝ := max 0 (min 1 t)

namespace RationalConvexExpr

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Evaluation of the rational convex syntax. -/
def eval (v : ι → E) : RationalConvexExpr ι → E
  | leaf i => v i
  | blend q a b => convexParameter (q : ℝ) • eval v a +
      (1 - convexParameter (q : ℝ)) • eval v b

end RationalConvexExpr

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BoundaryPolarTrace
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Tracial continuity of the near-identity polar factor

The proof uses the trace pairing and the norm bound on each positive
polar factor. It does not require a measurable functional-calculus
selection or an operator-topology continuity theorem.
-/

namespace KadisonKastler

noncomputable section

variable {B : Type*} [CStarAlgebra B]

local instance boundaryPolarTraceOrder : PartialOrder B := CStarAlgebra.spectralOrder B
local instance boundaryPolarTraceStarOrder : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BoundaryPolarMeasurable
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Measurability of the diagonal unitary polar field

The polar factor is a Lipschitz function of a near-identity operator in
its tracial Hilbert realization. Factoring through the range of the
measurable least field therefore supplies its measurability.
-/

namespace KadisonKastler

open MeasureTheory TopologicalSpace Set

noncomputable section

section Polar

variable {B E P : Type*} [CStarAlgebra B]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [SeparableSpace E] [MeasurableSpace P]
local instance boundaryPolarMeasurableOrder : PartialOrder B := CStarAlgebra.spectralOrder B
local instance boundaryPolarMeasurableStarOrder : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B

end Polar

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCoreOperators
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

/-- Pointwise action of a constant bounded operator on a Hilbert-valued
`L²` space. -/
def regularConstantOperator (μ : Measure D) (T : H →L[ℂ] H) :
    Lp H 2 μ →L[ℂ] Lp H 2 μ :=
  T.compLpL 2 μ

omit [CompleteSpace H] in
theorem regularConstantOperator_apply_ae (μ : Measure D) (T : H →L[ℂ] H)
    (f : Lp H 2 μ) :
    regularConstantOperator μ T f =ᵐ[μ] fun t => T (f t) :=
  T.coeFn_compLpL f

omit [CompleteSpace H] in
theorem regularConstantOperator_mul (μ : Measure D) (T S : H →L[ℂ] H) :
    regularConstantOperator μ (T * S) =
      regularConstantOperator μ T * regularConstantOperator μ S := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [regularConstantOperator_apply_ae μ (T * S) f,
    regularConstantOperator_apply_ae μ T (regularConstantOperator μ S f),
    regularConstantOperator_apply_ae μ S f] with t hTS hT hS
  simp only [mul_apply_eq_comp]
  rw [hTS, hT, hS]
  rfl

omit [CompleteSpace H] in
theorem regularConstantOperator_one (μ : Measure D) :
    regularConstantOperator μ (1 : H →L[ℂ] H) = 1 := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [regularConstantOperator_apply_ae μ (1 : H →L[ℂ] H) f] with t ht
  simpa only [one_apply_eq_self] using ht

theorem regularConstantOperator_star (μ : Measure D) (T : H →L[ℂ] H) :
    regularConstantOperator μ (star T) = star (regularConstantOperator μ T) := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_left ℂ
  intro g
  simp only [ContinuousLinearMap.star_eq_adjoint]
  rw [ContinuousLinearMap.adjoint_inner_right]
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [regularConstantOperator_apply_ae μ (star T) f,
    regularConstantOperator_apply_ae μ T g] with t hf hg
  simp only [ContinuousLinearMap.star_eq_adjoint] at hf
  rw [hf, hg, ContinuousLinearMap.adjoint_inner_right]

/-- The constant copy of `B(H)` on a Hilbert-valued `L²` space. -/
def regularConstantHom (μ : Measure D) :
    (H →L[ℂ] H) →⋆ₐ[ℂ] (Lp H 2 μ →L[ℂ] Lp H 2 μ) where
  toFun := regularConstantOperator μ
  map_one' := regularConstantOperator_one μ
  map_mul' := regularConstantOperator_mul μ
  map_zero' := by
    apply ContinuousLinearMap.ext
    intro f
    apply Lp.ext
    filter_upwards [regularConstantOperator_apply_ae μ (0 : H →L[ℂ] H) f,
      Lp.coeFn_zero H 2 μ] with t ht hz
    simpa only [zero_apply] using ht.trans hz.symm
  map_add' T S := ContinuousLinearMap.add_compLpL T S
  commutes' c := by
    apply ContinuousLinearMap.ext
    intro f
    apply Lp.ext
    filter_upwards [regularConstantOperator_apply_ae μ (algebraMap ℂ (H →L[ℂ] H) c) f,
      Lp.coeFn_smul c f] with t ht hc
    simpa only [Algebra.algebraMap_eq_smul_one, smul_apply,
      one_apply_eq_self] using ht.trans hc.symm
  map_star' := regularConstantOperator_star μ

theorem regularConstantHom_apply_ae (μ : Measure D) (T : H →L[ℂ] H)
    (f : Lp H 2 μ) :
    regularConstantHom μ T f =ᵐ[μ] fun t => T (f t) :=
  regularConstantOperator_apply_ae μ T f

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCoreRepresentation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The real regular representation and the core embedding

The translation and gauge operators below act on `L²(ℝ,H)` itself. A
strongly continuous unitary group gives the faithful embedding
`π(x)(t) = U(t)* x U(t)`. No crossed-product or fixed-point identification
is assumed in these constructions.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Topology ENNReal

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))

theorem regularGroup_star_eq (t : ℝ) :
    star (U (Multiplicative.ofAdd t)) = U (Multiplicative.ofAdd (-t)) := by
  change (U (Multiplicative.ofAdd t))⁻¹ = U (Multiplicative.ofAdd t)⁻¹
  exact (map_inv U _).symm

include hU in
theorem regularGroup_star_measurable (x : H) :
    AEStronglyMeasurable
      (fun t : ℝ => (star (U (Multiplicative.ofAdd t)) : H →L[ℂ] H) x) volume := by
  have he : (fun t : ℝ => (star (U (Multiplicative.ofAdd t)) : H →L[ℂ] H) x) =
      (fun t : ℝ => (U (Multiplicative.ofAdd (-t)) : H →L[ℂ] H) x) := by
    funext t
    exact congrArg (fun v : unitary (H →L[ℂ] H) => (v : H →L[ℂ] H) x)
      (regularGroup_star_eq U t)
  rw [he]
  exact ((hU x).comp continuous_neg).aestronglyMeasurable

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCoreCharacters
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

def regularCharacterScalar (a t : ℝ) : ℂ := Circle.exp (a * t)

theorem regularCharacterScalar_continuous (a : ℝ) : Continuous (regularCharacterScalar a) :=
  (continuous_subtype_val.comp Circle.exp.continuous).comp (continuous_const.mul continuous_id)

def regularCharacterFiber (a t : ℝ) : unitary (H →L[ℂ] H) :=
  ⟨regularCharacterScalar a t • (1 : H →L[ℂ] H), by
    have hz : star (regularCharacterScalar a t) * regularCharacterScalar a t = (1 : ℂ) := by
      rw [Complex.star_def, Complex.conj_mul']
      simp only [regularCharacterScalar, Circle.norm_coe, one_pow, Complex.ofReal_one]
    have hz' : regularCharacterScalar a t * star (regularCharacterScalar a t) = (1 : ℂ) := by
      rw [mul_comm, hz]
    constructor
    · simp only [star_smul, star_one, smul_mul_assoc, mul_smul_comm,
        one_mul, smul_smul, hz', one_smul]
    · simp only [star_smul, star_one, smul_mul_assoc, mul_smul_comm,
        one_mul, smul_smul, hz, one_smul]⟩

theorem regularCharacterFiber_measurable (a : ℝ) (x : H) :
    AEStronglyMeasurable (fun t => (regularCharacterFiber (H := H) a t : H →L[ℂ] H) x) volume := by
  change AEStronglyMeasurable (fun t => regularCharacterScalar a t • x) volume
  exact ((regularCharacterScalar_continuous a).smul continuous_const).aestronglyMeasurable

theorem regularCharacterFiber_star_measurable (a : ℝ) (x : H) :
    AEStronglyMeasurable (fun t => (star (regularCharacterFiber (H := H) a t) : H →L[ℂ] H) x) volume := by
  have he (t : ℝ) : (star (regularCharacterFiber (H := H) a t) : H →L[ℂ] H) x =
      star (regularCharacterScalar a t) • x := by
    simp only [regularCharacterFiber, star_smul, star_one,
      smul_apply, one_apply_eq_self]
  simp only [he]
  exact ((regularCharacterScalar_continuous a).star.smul continuous_const).aestronglyMeasurable

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MeasurableStrongTests
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Measurability of countable strong approximation conditions

Only vector evaluation is required to be measurable. Countable tests
then give a measurable implementer condition without placing the norm
topology on the operator algebra.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H]

def PrefixStrongTests (ξ : ℕ → H) (T : X → H →L[ℂ] H)
    (S : X → ℕ → H →L[ℂ] H) (p : X) : Prop :=
  ∀ m k : ℕ, ∃ q : ℕ, ∀ l ≤ m, ‖(T p - S p q) (ξ l)‖ < 1 / (k + 1 : ℝ)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_StrongContractionLimits
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Recovering a strong contraction limit from countable coordinates -/

namespace KadisonKastler

open Filter TopologicalSpace
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

theorem cauchySeq_apply_of_dense_contractions (ξ : ℕ → H) (hξ : DenseRange ξ)
    (A : ℕ → H →L[ℂ] H) (hA : ∀ n, ‖A n‖ ≤ 1)
    (h : ∀ j, CauchySeq (fun n => A n (ξ j))) (x : H) :
    CauchySeq (fun n => A n x) := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨j, hj⟩ := hξ.exists_dist_lt x (by positivity : 0 < ε / 4)
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp (h j) (ε / 2) (by positivity)
  refine ⟨N, fun m hm n hn => ?_⟩
  have hdist (k : ℕ) (u v : H) : dist (A k u) (A k v) ≤ dist u v := by
    simp only [dist_eq_norm, ← map_sub]
    exact ((A k).le_opNorm (u - v)).trans
      (by simpa using mul_le_mul_of_nonneg_right (hA k) (norm_nonneg (u - v)))
  have hleft := hdist m x (ξ j)
  have hright := hdist n (ξ j) x
  have hmid := hN m hm n hn
  have ht := (dist_triangle (A m x) (A m (ξ j)) (A n x)).trans
    (add_le_add le_rfl (dist_triangle (A m (ξ j)) (A n (ξ j)) (A n x)))
  rw [dist_comm (ξ j) x] at hright
  linarith

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_StrongUnitaryCoordinates
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A closed Polish coordinate model of the unitary group

Both the operator and its adjoint are evaluated on a fixed dense sequence.
The range is closed: coordinate limits extend to contractions, and the
inverse and adjoint identities pass to strong limits.
-/

namespace KadisonKastler

open Filter TopologicalSpace
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def unitaryCoordinates (ξ : ℕ → H) (u : unitary (H →L[ℂ] H)) :
    (ℕ → H) × (ℕ → H) :=
  (fun n => (u : H →L[ℂ] H) (ξ n), fun n => (star u : H →L[ℂ] H) (ξ n))

/-- This is the strong-star coordinate model, not the operator-norm topology. -/
def StrongUnitarySpace (ξ : ℕ → H) := Set.range (unitaryCoordinates ξ)

instance instTopologicalSpaceElemProdForallNatStrongUnitarySpace (ξ : ℕ → H) : TopologicalSpace (StrongUnitarySpace ξ) :=
  inferInstanceAs (TopologicalSpace (Set.range (unitaryCoordinates ξ)))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PolishConjugacyRelation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The Borel implementer relation on the Polish unitary model

Measurable evaluation of the countable contraction fields suffices.
No measurability in the operator norm topology is imposed.
-/

namespace KadisonKastler

open MeasureTheory TopologicalSpace

noncomputable section

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [SeparableSpace H] [MeasurableSpace H] [BorelSpace H]

instance strongUnitarySpaceMeasurable (ξ : ℕ → H) : MeasurableSpace (StrongUnitarySpace ξ) :=
  borel (StrongUnitarySpace ξ)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PublishedBorelSelection
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The published Borel selection input

Alexander S. Kechris, *Classical Descriptive Set Theory*, GTM 156,
Springer (1995), Theorem 18.1, pp.120–121, and Theorem 21.10, pp.155–156.
DOI: 10.1007/978-1-4612-4190-4.

We retain only selection for Borel relations whose second coordinate is
the proved Polish unitary coordinate space, for one finite Borel measure.
The published universally measurable selector is measurable for the
completed measure, hence has the `AEMeasurable` formulation used here.
No algebra-conjugacy or perturbation conclusion is part of this input.
-/

namespace KadisonKastler

open MeasureTheory TopologicalSpace

universe u v

def PublishedUnitaryBorelSelection : Prop :=
  ∀ (X : Type u) [MeasurableSpace X] [StandardBorelSpace X]
    (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [SeparableSpace H] [MeasurableSpace H] [BorelSpace H]
    (ξ : ℕ → H), DenseRange ξ →
    ∀ (μ : Measure X) [IsFiniteMeasure μ] (R : Set (X × StrongUnitarySpace ξ)),
      MeasurableSet R → (∀ᵐ x ∂μ, ∃ p, (x, p) ∈ R) →
      ∃ f : X → StrongUnitarySpace ξ,
        AEMeasurable f μ ∧ ∀ᵐ x ∂μ, (x, f x) ∈ R

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_StarCorrection
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# The involution in multiplication correction

This is the algebraic star-preserving part of the UCP criterion. The
linear correction itself remains an explicit hypothesis.
-/

namespace KadisonKastler

variable {A B : Type*} [NormedRing A] [NormedAlgebra ℂ A] [StarRing A]
  [NormedRing B] [NormedAlgebra ℂ B] [StarRing B]

theorem linearEquiv_symm_map_star (F : A ≃ₗ[ℂ] B)
    (hstar : ∀ x, F (star x) = star (F x)) (y : B) :
    F.symm (star y) = star (F.symm y) := by
  apply F.injective
  rw [F.apply_symm_apply, hstar, F.apply_symm_apply]

/-- The star-algebra equivalence furnished by a star-preserving linear
correction of the transported multiplication. -/
noncomputable def correctedStarAlgEquiv (F : A ≃ₗ[ℂ] B) (L : A ≃ₗ[ℂ] A)
    (hL : ∀ x y, L (transportedMul F x y) = L x * L y)
    (hFstar : ∀ x, F (star x) = star (F x))
    (hLstar : ∀ x, L (star x) = star (L x)) : A ≃⋆ₐ[ℂ] B :=
  { correctedAlgEquiv F L hL with
    map_smul' c x := by
      change F (L.symm (c • x)) = c • F (L.symm x)
      rw [map_smul, map_smul]
    map_star' x := by
      change F (L.symm (star x)) = star (F (L.symm x))
      rw [linearEquiv_symm_map_star L hLstar, hFstar] }

@[simp] theorem correctedStarAlgEquiv_apply (F : A ≃ₗ[ℂ] B) (L : A ≃ₗ[ℂ] A)
    (hL : ∀ x y, L (transportedMul F x y) = L x * L y)
    (hFstar : ∀ x, F (star x) = star (F x))
    (hLstar : ∀ x, L (star x) = star (L x)) (x : A) :
    correctedStarAlgEquiv F L hL hFstar hLstar x = F (L.symm x) := rfl

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_Haagerup
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# Row-column bounds for bilinear multiplication

The Haagerup bound is expressed directly by all finite rectangular matrix
products, as in the UCP criterion of §2 of *Universal strong
Kadison–Kastler stability* (2026). For multiplication transported through
a linear equivalence, this is exactly the matrix defect already bounded
in `CompletelyBounded`.
-/

namespace KadisonKastler

noncomputable section

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

omit [PartialOrder A] [StarOrderedRing A] in
/-- The row-column extension of a bilinear product to rectangular matrices. -/
def bilinearProduct (m : A →ₗ[ℂ] A →ₗ[ℂ] A) {p r q : ℕ}
    (X : CStarMatrix (Fin p) (Fin r) A) (Y : CStarMatrix (Fin r) (Fin q) A) :
    CStarMatrix (Fin p) (Fin q) A :=
  CStarMatrix.ofMatrix fun i k => ∑ j, m (X i j) (Y j k)

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] theorem bilinearProduct_apply (m : A →ₗ[ℂ] A →ₗ[ℂ] A) {p r q : ℕ}
    (X : CStarMatrix (Fin p) (Fin r) A) (Y : CStarMatrix (Fin r) (Fin q) A)
    (i : Fin p) (k : Fin q) :
    bilinearProduct m X Y i k = ∑ j, m (X i j) (Y j k) := rfl

/-- The norm bound on the bilinear map viewed on the Haagerup product,
in its concrete finite row-column formulation. -/
def HaagerupBound (m : A →ₗ[ℂ] A →ₗ[ℂ] A) (c : ℝ) : Prop :=
  ∀ (p r q : ℕ) (X : CStarMatrix (Fin p) (Fin r) A)
    (Y : CStarMatrix (Fin r) (Fin q) A),
    ‖bilinearProduct m X Y‖ ≤ c * ‖X‖ * ‖Y‖

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
/-- Transported multiplication as a bundled complex-bilinear product. -/
def transportedBilinear (F : A ≃ₗ[ℂ] B) : A →ₗ[ℂ] A →ₗ[ℂ] A where
  toFun x :=
    { toFun := transportedMul F x
      map_add' y z := transportedMul_add_right F x y z
      map_smul' c y := transportedMul_smul_right F c x y }
  map_add' x y := by
    ext z
    exact transportedMul_add_left F x y z
  map_smul' c x := by
    ext y
    exact transportedMul_smul_left F c x y

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem transportedBilinear_apply (F : A ≃ₗ[ℂ] B) (x y : A) :
    transportedBilinear F x y = transportedMul F x y := rfl

omit [PartialOrder A] [StarOrderedRing A] in
/-- The ordinary bilinear multiplication extends to the usual rectangular
matrix product. -/
@[simp] theorem bilinearProduct_mul {p r q : ℕ}
    (X : CStarMatrix (Fin p) (Fin r) A) (Y : CStarMatrix (Fin r) (Fin q) A) :
    bilinearProduct (LinearMap.mul ℂ A) X Y = X * Y := by
  ext i k
  rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_UCPDescent
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Descending an amplified conjugacy through a UCP retraction

These are the operator-space estimates used when a character average or
an auxiliary tensor-factor average returns an amplified map to the base.
-/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

section Abstract

variable {A B C : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
  [PartialOrder C] [StarOrderedRing C]

/-- Composition of completely positive linear maps. -/
def completelyPositiveComp (E : B →CP C) (F : A →CP B) : A →CP C where
  toLinearMap := E.toLinearMap.comp F.toLinearMap
  map_cstarMatrix_nonneg' n X hX := by
    have h := E.map_cstarMatrix_nonneg (X.map F) (F.map_cstarMatrix_nonneg X hX)
    exact h

/-- Positivity at all matrix levels is reflected by a faithful embedding. -/
def completelyPositive_of_embedding (j : B →⋆ₐ[ℂ] C) (hj : Function.Injective j)
    (φ : A →CP C) (F : A →ₗ[ℂ] B) (hF : ∀ a, j (F a) = φ a) : A →CP B where
  toLinearMap := F
  map_cstarMatrix_nonneg' n X hX := by
    let jn := CStarMatrix.mapₙₐ (n := Fin n) j.toNonUnitalStarAlgHom
    have hpos : 0 ≤ jn (CStarMatrix.mapₗ F X) := by
      have he : jn (CStarMatrix.mapₗ F X) = CStarMatrix.mapₗ φ.toLinearMap X := by
        ext i k
        exact hF (X i k)
      rw [he]
      exact φ.map_cstarMatrix_nonneg X hX
    apply (NonUnitalStarAlgHom.map_le_map_iff jn (injective_starAlgHom_matrix j hj)).mp
    rw [map_zero]
    change 0 ≤ jn (CStarMatrix.mapₗ F X)
    exact hpos

end Abstract

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_AveragedRangeDescent
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Descent when only the averaged conjugates lie in the embedded range

The averaging map acts on the upper ambient operator algebra. Its range
on other inputs need not lie in the embedded lower algebra. The map below
uses the inverse of a faithful embedding only on the averaged conjugates
of the source algebra, which is exactly the range condition in §8.
-/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

section Linear

variable {A B C : Type*} [AddCommGroup A] [Module ℂ A]
  [AddCommGroup B] [Module ℂ B] [AddCommGroup C] [Module ℂ C]

/-- Restrict a linear map to the range of an injection and invert there. -/
def linearDescendRange (j : B →ₗ[ℂ] C) (hj : Function.Injective j)
    (F : A →ₗ[ℂ] C) (hF : ∀ a, F a ∈ j.range) : A →ₗ[ℂ] B :=
  (LinearEquiv.ofInjective j hj).symm.toLinearMap.comp (F.codRestrict j.range hF)

theorem linearDescendRange_spec (j : B →ₗ[ℂ] C) (hj : Function.Injective j)
    (F : A →ₗ[ℂ] C) (hF : ∀ a, F a ∈ j.range) (a : A) :
    j (linearDescendRange j hj F hF a) = F a := by
  exact congrArg Subtype.val
    ((LinearEquiv.ofInjective j hj).apply_symm_apply ⟨F a, hF a⟩)

end Linear

section Concrete

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M N : VonNeumannAlgebra H}

local instance averagedDescentOperatorOrder {J : Type*} [NormedAddCommGroup J]
    [InnerProductSpace ℂ J] [CompleteSpace J] : PartialOrder (J →L[ℂ] J) :=
  CStarAlgebra.spectralOrder _
local instance averagedDescentOperatorStarOrder {J : Type*} [NormedAddCommGroup J]
    [InnerProductSpace ℂ J] [CompleteSpace J] : StarOrderedRing (J →L[ℂ] J) :=
  CStarAlgebra.spectralOrderedRing _

end Concrete

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_AnalyticAlgebraBounds
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Algebra errors of the demodulated analytic products

The Hardy product identity follows from evaluation and preservation of
the frequency nest. The resulting norm estimates pass from boundary
algebra distance to positive-height distance.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem ae_norm_sandwich_le
    (B S : ℝ → H →L[ℂ] H) {CB CS : ℝ} (hCB : 0 ≤ CB)
    (hB : ∀ᵐ s, ‖B s‖ ≤ CB) (hS : ∀ᵐ s, ‖S s‖ ≤ CS) (x : H →L[ℂ] H) :
    ∀ᵐ s, ‖B s * x * S s‖ ≤ CB * ‖x‖ * CS := by
  filter_upwards [hB, hS] with s hb hs
  exact ((norm_mul_le _ _).trans
    (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))).trans
      (mul_le_mul (mul_le_mul_of_nonneg_right hb (norm_nonneg _)) hs
        (norm_nonneg _) (by positivity))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BaireMeasurableBranch
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Measurable successive choices of Baire digits -/

namespace KadisonKastler

open MeasureTheory Set Filter
open scoped Topology

noncomputable section

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]

instance instMeasurableSpaceListNat_solutions : MeasurableSpace (List ℕ) := ⊤

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProductIntegralUniqueness
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Rectangle tests determine an integrable product function

This finite-measure bridge will identify the range of the boundary projection.
It uses uniqueness of vector measures on the rectangle pi-system, avoiding
any unproved tensor-product identification of L2 spaces.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory Set

variable {X Y E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem integrable_eq_zero_of_rectangle_integrals {f : X × Y → E}
    (hf : Integrable f (μ.prod ν))
    (hrect : ∀ A B, MeasurableSet A → MeasurableSet B →
      ∫ z in A ×ˢ B, f z ∂μ.prod ν = 0) : f =ᵐ[μ.prod ν] 0 := by
  have he : (μ.prod ν).withDensityᵥ f = 0 := by
    apply VectorMeasure.ext_of_generateFrom
      (image2 (· ×ˢ ·) {A : Set X | MeasurableSet A} {B : Set Y | MeasurableSet B})
    · rintro _ ⟨A, hA, B, hB, rfl⟩
      rw [withDensityᵥ_apply hf (hA.prod hB), hrect A B hA hB]
      rfl
    · exact generateFrom_prod.symm
    · exact isPiSystem_prod
    · rw [withDensityᵥ_apply hf MeasurableSet.univ]
      simpa using hrect univ univ MeasurableSet.univ MeasurableSet.univ
  apply hf.ae_eq_of_withDensityᵥ_eq (integrable_zero _ _ _)
  simpa using he

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProductInvariantIntegrals
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Invariant sections and rectangle tests

For a function invariant under a shift in its first coordinate, integrating
over a set in the second coordinate gives a function on the invariant sigma
algebra. Consequently invariant rectangles already determine such a function.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory Set

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
  {S : X → X} {f : X × Y → ℂ}

omit [IsFiniteMeasure μ] in
theorem integrable_section_setIntegral (hf : Integrable f (μ.prod ν))
    (B : Set Y) : Integrable (fun x => ∫ y in B, f (x, y) ∂ν) μ := by
  have h : Integrable f (μ.prod (ν.restrict B)) :=
    hf.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
  exact h.integral_prod_left

omit [IsFiniteMeasure μ] in
theorem invariant_section_setIntegral
    (hf : ∀ᵐ z ∂μ.prod ν, f (S z.1, z.2) = f z) (B : Set Y) :
    ∀ᵐ x ∂μ, (∫ y in B, f (S x, y) ∂ν) = ∫ y in B, f (x, y) ∂ν := by
  filter_upwards [Measure.ae_ae_of_ae_prod hf] with x hx
  exact integral_congr_ae (ae_restrict_of_ae hx)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_WeakHilbertConvexLimit
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Closed convex constraints on weak scalar limits

Separation retains closed convex conditions under a bounded Hilbert-space
weak limit. Applied in L2, this retains almost-everywhere disk and positivity
conditions for the scalar boundary averages.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory Filter
open scoped Topology

theorem mem_closed_convex_of_inner_tendsto
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ι : Type*} {l : Filter ι} [l.NeBot] {C : Set H} (hC : IsClosed C)
    (hc : Convex ℝ C) (v : ι → H) (x : H) (hv : ∀ i, v i ∈ C)
    (ht : ∀ y, Tendsto (fun i => inner ℂ y (v i)) l (𝓝 (inner ℂ y x))) : x ∈ C := by
  by_contra hx
  obtain ⟨f, a, hf, hax⟩ := RCLike.geometric_hahn_banach_closed_point (𝕜 := ℂ) hc hC hx
  let y := (InnerProductSpace.toDual ℂ H).symm f
  have hy (z : H) : inner ℂ y z = f z := InnerProductSpace.toDual_symm_apply
  have hr : Tendsto (fun i => (f (v i)).re) l (𝓝 (f x).re) := by
    simpa only [hy, Function.comp_def] using (Complex.continuous_re.tendsto _).comp (ht y)
  exact hax.not_ge (le_of_tendsto hr (Eventually.of_forall (fun i => (hf _ (hv i)).le)))

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem isClosed_L2_ae_mem {C : Set ℂ} (hC : IsClosed C) :
    IsClosed {f : Lp ℂ 2 μ | ∀ᵐ x ∂μ, f x ∈ C} := by
  apply IsSeqClosed.isClosed
  intro f g hf hfg
  obtain ⟨ns, _, hns⟩ := (tendstoInMeasure_of_tendsto_Lp hfg).exists_seq_tendsto_ae
  filter_upwards [ae_all_iff.mpr hf, hns] with x hx hlim
  exact hC.mem_of_tendsto hlim (Eventually.of_forall (fun n => hx (ns n)))

theorem convex_L2_ae_mem {C : Set ℂ} (hC : Convex ℝ C) :
    Convex ℝ {f : Lp ℂ 2 μ | ∀ᵐ x ∂μ, f x ∈ C} := by
  intro f hf g hg a b ha hb hab
  filter_upwards [hf, hg, Lp.coeFn_add (a • f) (b • g),
    Lp.coeFn_smul a f, Lp.coeFn_smul b g] with x hfx hgx hs hfsm hgsm
  simp only [Pi.add_apply, Pi.smul_apply] at hs hfsm hgsm
  rw [hs, hfsm, hgsm]
  exact hC hfx hgx ha hb hab

theorem L2_ae_mem_of_inner_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {C : Set ℂ} (hC : IsClosed C) (hc : Convex ℝ C)
    (f : ι → Lp ℂ 2 μ) (g : Lp ℂ 2 μ) (hf : ∀ i, ∀ᵐ x ∂μ, f i x ∈ C)
    (ht : ∀ y, Tendsto (fun i => inner ℂ y (f i)) l (𝓝 (inner ℂ y g))) :
    ∀ᵐ x ∂μ, g x ∈ C :=
  mem_closed_convex_of_inner_tendsto (isClosed_L2_ae_mem hC) (convex_L2_ae_mem hc) f g hf ht

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RandomWalkPrefix
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! Inserting prescribed countable roots and first increments is nonsingular. -/

namespace KadisonKastler

noncomputable section

open MeasureTheory

variable (G : Type*) [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]

def randomWalkPrepend (g : G) (ω : ℕ → G) (n : ℕ) : G := Nat.casesOn n g ω

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BilateralBlockWords
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! Three separated increment blocks in the double-ergodicity proof. -/

namespace KadisonKastler

noncomputable section

open MeasureTheory Set

variable (G : Type*) [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]

variable {G}

def bilateralSymmetricWindow (m : ℕ) : Set ℤ := {j | -(m : ℤ) ≤ j ∧ j ≤ m}

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_HilbertDefect
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The defect isometry of a Hilbert-space contraction

The positive square root of `1 - A* A` completes a contraction to an
isometry. This is the geometric ingredient in finite block completion.
-/

namespace KadisonKastler

open scoped InnerProductSpace

noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem adjoint_comp_self_le_one (A : E →L[ℂ] F) (hA : ‖A‖ ≤ 1) :
    A.adjoint.comp A ≤ 1 := by
  apply (CStarAlgebra.norm_le_one_iff_of_nonneg _
    ((ContinuousLinearMap.nonneg_iff_isPositive _).mpr
      (ContinuousLinearMap.isPositive_adjoint_comp_self A))).mp
  rw [ContinuousLinearMap.norm_adjoint_comp_self]
  nlinarith [norm_nonneg A]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BlockCommutantConstruction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Commutant distance for paired representations

This is the exact two-by-two specialization used by the stability proof.
The general represented estimate is transported through the faithful
finite Hilbert-sum matrix representation, preserving its constant.
-/

namespace KadisonKastler

noncomputable section

variable (A K : Type*) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

local instance blockDistanceBaseOrder : PartialOrder (K →L[ℂ] K) := CStarAlgebra.spectralOrder _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BoundedFamilyCurry
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Bounded currying for two discrete group coordinates -/

namespace KadisonKastler

noncomputable section

open scoped BoundedContinuousFunction

variable {G H E : Type*} [TopologicalSpace G] [TopologicalSpace H]
  [DiscreteTopology G] [DiscreteTopology H]
  [NormedAddCommGroup E] [NormedSpace ℂ E]

def boundedFamilyRow (F : (G × H) →ᵇ E) (g : G) : H →ᵇ E :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete (fun h => F (g, h)) ‖F‖
    (fun h => F.norm_coe_le_norm (g, h))

omit [DiscreteTopology G] [NormedSpace ℂ E] in
@[simp]
theorem boundedFamilyRow_apply (F : (G × H) →ᵇ E) (g : G) (h : H) :
    boundedFamilyRow F g h = F (g, h) := rfl

omit [DiscreteTopology G] [NormedSpace ℂ E] in
theorem boundedFamilyRow_norm_le (F : (G × H) →ᵇ E) (g : G) :
    ‖boundedFamilyRow F g‖ ≤ ‖F‖ :=
  (BoundedContinuousFunction.norm_le (norm_nonneg F)).mpr (fun h => F.norm_coe_le_norm (g, h))

def boundedFamilyCurry (F : (G × H) →ᵇ E) : G →ᵇ H →ᵇ E :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete (boundedFamilyRow F) ‖F‖
    (boundedFamilyRow_norm_le F)

omit [NormedSpace ℂ E] in
@[simp]
theorem boundedFamilyCurry_apply (F : (G × H) →ᵇ E) (g : G) :
    boundedFamilyCurry F g = boundedFamilyRow F g := rfl

def boundedFamilyCurryL : ((G × H) →ᵇ E) →L[ℂ] (G →ᵇ H →ᵇ E) :=
  LinearMap.mkContinuous
    { toFun := boundedFamilyCurry
      map_add' F K := by ext g h; rfl
      map_smul' c F := by ext g h; rfl }
    1 (fun F => by
      rw [one_mul]
      exact (BoundedContinuousFunction.norm_le (norm_nonneg F)).mpr
        (boundedFamilyRow_norm_le F))

@[simp]
theorem boundedFamilyCurryL_apply (F : (G × H) →ᵇ E) (g : G) (h : H) :
    boundedFamilyCurryL F g h = F (g, h) := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CentralSupportCover
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! An orthogonal family of initial projections equivalent to subprojections
of e fills the central support of e. This is the geometric step in the
localized row-averaging proof; no countability is imposed. -/

namespace KadisonKastler

noncomputable section

open Generator Generator.Tracial

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

def IsCentralSupportFamily (e : AlgebraProjection M) (S : Set (PartialIsometry M)) : Prop :=
  (∀ v ∈ S, v.target ≤ e ∧ v.support.val ≠ 0) ∧
    S.Pairwise (fun v w => v.support.val * w.support.val = 0)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CommonRightAction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

/-- A cyclic vector separates the commutant, expressed without introducing
any representation or standard-form hypothesis. -/
theorem operator_eq_of_commute_of_eq_on_cyclicVector
    {I : Type*} (A : I → H →L[ℂ] H) (Ω : H)
    (hcyclic : DenseRange (fun i => A i Ω)) (q r : H →L[ℂ] H)
    (hq : ∀ i, Commute q (A i)) (hr : ∀ i, Commute r (A i))
    (hΩ : q Ω = r Ω) : q = r := by
  have he : (fun ξ => q ξ) = fun ξ => r ξ :=
    hcyclic.equalizer q.continuous r.continuous (by
      funext i
      change q (A i Ω) = r (A i Ω)
      calc
        q (A i Ω) = A i (q Ω) := congrArg (fun b : H →L[ℂ] H => b Ω) (hq i).eq
        _ = A i (r Ω) := by rw [hΩ]
        _ = r (A i Ω) := (congrArg (fun b : H →L[ℂ] H => b Ω) (hr i).eq).symm)
  ext ξ
  exact congrFun he ξ

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MeasurableConullRepresentations
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Measurable representatives of a separable operator-algebra field

A single measurable conull set suffices for every algebra element and vector.
Countably many dense tests are made measurable there; continuity supplies the
remaining evaluations without any uncountable intersection of conull sets.
-/

namespace KadisonKastler

open MeasureTheory TopologicalSpace Filter
open scoped Topology CStarAlgebra

noncomputable section

variable {X A H : Type*} [MeasurableSpace X]

theorem measurable_of_dense_parameters
    [TopologicalSpace A] [FirstCountableTopology A]
    [TopologicalSpace H] [PseudoMetrizableSpace H] [MeasurableSpace H] [BorelSpace H]
    (g : A → X → H) (hg : ∀ x, Continuous fun a => g a x)
    (d : ℕ → A) (hd : DenseRange d) (hm : ∀ n, Measurable (g (d n))) (a : A) :
    Measurable (g a) := by
  have hc : IsClosed {a | Measurable (g a)} := by
    apply IsSeqClosed.isClosed
    intro u a hu ha
    apply measurable_of_tendsto_metrizable hu
    rw [tendsto_pi_nhds]
    intro x
    exact ((hg x).tendsto a).comp ha
  exact (closure_minimal (by rintro _ ⟨n, rfl⟩; exact hm n) hc) (hd a)

variable [CStarAlgebra A] [SeparableSpace A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [SeparableSpace H] [MeasurableSpace H] [BorelSpace H]

/-- An a.e. measurable representation field is strongly Borel measurable
on a single measurable conull subset, simultaneously for all evaluations. -/
theorem exists_conull_measurable_representations (μ : Measure X)
    (ρ : X → A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (hρ : ∀ a v, AEStronglyMeasurable (fun x => ρ x a v) μ) :
    ∃ s : Set X, MeasurableSet s ∧ μ sᶜ = 0 ∧
      ∀ a v, Measurable fun x : s => ρ x.val a v := by
  let a : ℕ → A := denseSeq A
  let v : ℕ → H := denseSeq H
  have he : ∀ᵐ x ∂μ, ∀ n m : ℕ,
      ρ x (a n) (v m) = (hρ (a n) (v m)).mk (fun y => ρ y (a n) (v m)) x :=
    eventually_countable_forall.mpr fun n =>
      eventually_countable_forall.mpr fun m => (hρ (a n) (v m)).ae_eq_mk
  obtain ⟨s, hs, hsm, hse⟩ := he.exists_measurable_mem
  refine ⟨s, hsm, mem_ae_iff.mp hs, ?_⟩
  have htest (n m : ℕ) : Measurable fun x : s => ρ x.val (a n) (v m) := by
    have hm : Measurable fun x : s =>
        (hρ (a n) (v m)).mk (fun y => ρ y (a n) (v m)) x.val :=
      (hρ (a n) (v m)).measurable_mk.comp measurable_subtype_coe
    convert hm using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    exact hse x.val x.property n m
  have ha (n : ℕ) (w : H) : Measurable fun x : s => ρ x.val (a n) w :=
    measurable_of_dense_parameters (fun (w : H) (x : s) => ρ x.val (a n) w)
      (fun x => (ρ x.val (a n)).continuous) v (denseRange_denseSeq H) (htest n) w
  intro c w
  exact measurable_of_dense_parameters (fun (c : A) (x : s) => ρ x.val c w)
    (fun x => (ContinuousLinearMap.apply ℂ H w).continuous.comp (map_continuous (ρ x.val)))
    a (denseRange_denseSeq A) (fun n => ha n w) c

/-- Extend the common conull restriction by the zero representation. This
preserves every fixed algebra element almost everywhere and is Borel everywhere. -/
theorem exists_measurable_nonunitalRepresentation_version (μ : Measure X)
    (ρ : X → A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (hρ : ∀ a v, AEStronglyMeasurable (fun x => ρ x a v) μ) :
    ∃ σ : X → A →⋆ₙₐ[ℂ] (H →L[ℂ] H),
      (∀ a v, Measurable fun x => σ x a v) ∧
      ∀ a, ∀ᵐ x ∂μ, σ x a = ρ x a := by
  classical
  obtain ⟨s, hs, hsnull, hm⟩ := exists_conull_measurable_representations μ ρ hρ
  let σ : X → A →⋆ₙₐ[ℂ] (H →L[ℂ] H) := fun x => if x ∈ s then ρ x else 0
  refine ⟨σ, ?_, ?_⟩
  · intro a v
    have h := (hm a v).dite (measurable_const :
      Measurable fun _ : (sᶜ : Set X) => (0 : H)) hs
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    by_cases hx : x ∈ s <;> simp [σ, hx]
  · intro a
    filter_upwards [mem_ae_iff.mpr hsnull] with x hx
    simp only [σ, ite_eq_left hx]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_DenseStarRepresentation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Extending the pointwise algebra in a fiber

This is the norm-continuity step in Blackadar, III.5.1.11. A contractive
unital ring representation on a dense subring extends to the C-star algebra.
Preservation of star and of `i · 1` makes that extension a complex star
representation. Countability is needed only to gather almost-everywhere
relations on a common conull set, not for the extension itself.
-/

noncomputable section
namespace KadisonSimilarity

open scoped Topology CStarAlgebra

variable {A : Type*} [CStarAlgebra A]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem denseSubringRepresentation_continuous
    (S : Subring A) (hdense : Dense (S : Set A))
    (f : S →+* (H →L[ℂ] H)) (hnorm : ∀ a : S, ‖f a‖ ≤ ‖a‖) :
    Continuous (denseSubringRepresentation S hdense f hnorm) := by
  exact (uniformContinuous_uniformly_extend
    isUniformEmbedding_subtype_val.isUniformInducing hdense.denseRange_val
    (denseSubring_uniformContinuous S f hnorm)).continuous

omit [CompleteSpace H] in
/-- Continuity of an additive map gives real linearity; preserving `i · 1`
then forces preservation of every complex scalar. -/
theorem continuousRingHom_commutes_complex
    (F : A →+* (H →L[ℂ] H)) (hF : Continuous F)
    (hI : F (algebraMap ℂ A Complex.I) = algebraMap ℂ (H →L[ℂ] H) Complex.I) :
    ∀ z : ℂ, F (algebraMap ℂ A z) = algebraMap ℂ (H →L[ℂ] H) z := by
  have hr (r : ℝ) : F (algebraMap ℂ A (r : ℂ)) =
      algebraMap ℂ (H →L[ℂ] H) (r : ℂ) := by
    calc
      F (algebraMap ℂ A (r : ℂ)) = F (r • (1 : A)) := by
        rw [RCLike.real_smul_eq_coe_smul (K := ℂ), Algebra.algebraMap_eq_smul_one]
        rfl
      _ = r • F 1 := map_real_smul F hF r 1
      _ = algebraMap ℂ (H →L[ℂ] H) (r : ℂ) := by
        rw [map_one, RCLike.real_smul_eq_coe_smul (K := ℂ),
          Algebra.algebraMap_eq_smul_one]
        rfl
  intro z
  calc
    F (algebraMap ℂ A z) =
        F (algebraMap ℂ A ((z.re : ℂ) + (z.im : ℂ) * Complex.I)) := by
      rw [Complex.re_add_im]
    _ = algebraMap ℂ (H →L[ℂ] H) ((z.re : ℂ) + (z.im : ℂ) * Complex.I) := by
      simp only [map_add, map_mul, hr, hI]
    _ = algebraMap ℂ (H →L[ℂ] H) z := by rw [Complex.re_add_im]

/-- A continuous ring extension is a complex star representation when its
dense restriction preserves star and the scalar `i`. -/
theorem exists_starRepresentation_of_ring_extension
    (S : Subring A) (hdense : Dense (S : Set A))
    (hstarS : ∀ a ∈ S, star a ∈ S) (hIS : algebraMap ℂ A Complex.I ∈ S)
    (f : S →+* (H →L[ℂ] H)) (F : A →+* (H →L[ℂ] H))
    (hF : Continuous F) (hext : ∀ a : S, F a = f a)
    (hstar : ∀ a : S, f ⟨star a.val, hstarS a.val a.property⟩ = star (f a))
    (hI : f ⟨algebraMap ℂ A Complex.I, hIS⟩ = algebraMap ℂ (H →L[ℂ] H) Complex.I) :
    ∃ σ : A →⋆ₐ[ℂ] (H →L[ℂ] H), ∀ a : S, σ a = f a := by
  have hFstar : ∀ a : A, F (star a) = star (F a) := by
    intro a
    refine hdense.denseRange_val.induction_on
      (p := fun a => F (star a) = star (F a)) a
      (isClosed_eq (hF.comp continuous_star) (continuous_star.comp hF)) ?_
    intro b
    calc
      F (star (b : A)) = f ⟨star b.val, hstarS b.val b.property⟩ :=
        hext ⟨star b.val, hstarS b.val b.property⟩
      _ = star (f b) := hstar b
      _ = star (F (b : A)) :=
        congrArg star (hext b).symm
  have hFI : F (algebraMap ℂ A Complex.I) = algebraMap ℂ (H →L[ℂ] H) Complex.I := by
    exact (hext ⟨algebraMap ℂ A Complex.I, hIS⟩).trans hI
  let σ : A →⋆ₐ[ℂ] (H →L[ℂ] H) := {
    F with
    commutes' := continuousRingHom_commutes_complex F hF hFI
    map_star' := hFstar }
  exact ⟨σ, hext⟩

/-- A contractive unital ring representation on a dense star subring extends
to a complex star representation when it preserves the scalar `i`. -/
theorem exists_starRepresentation_of_dense_subring
    (S : Subring A) (hdense : Dense (S : Set A))
    (hstarS : ∀ a ∈ S, star a ∈ S) (hIS : algebraMap ℂ A Complex.I ∈ S)
    (f : S →+* (H →L[ℂ] H)) (hnorm : ∀ a : S, ‖f a‖ ≤ ‖a‖)
    (hstar : ∀ a : S, f ⟨star a.val, hstarS a.val a.property⟩ = star (f a))
    (hI : f ⟨algebraMap ℂ A Complex.I, hIS⟩ = algebraMap ℂ (H →L[ℂ] H) Complex.I) :
    ∃ σ : A →⋆ₐ[ℂ] (H →L[ℂ] H), ∀ a : S, σ a = f a :=
  exists_starRepresentation_of_ring_extension S hdense hstarS hIS f
    (denseSubringRepresentation S hdense f hnorm)
    (denseSubringRepresentation_continuous S hdense f hnorm)
    (denseSubringRepresentation_apply S hdense f hnorm) hstar hI

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_AEStarRepresentation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A common conull set for fiber representations

Countability of the dense subring lets all algebraic identities and norm
bounds hold on a single conull set. Each of those fibers then has the genuine
complex star representation constructed in `DenseStarRepresentation`.
Exceptional fibers are left out of the existence assertion.
-/

noncomputable section
namespace KadisonSimilarity

open MeasureTheory Filter

variable {A : Type*} [CStarAlgebra A]
  {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  (K : Ω → Type*) [∀ x, NormedAddCommGroup (K x)]
  [∀ x, InnerProductSpace ℂ (K x)] [∀ x, CompleteSpace (K x)]

/-- Pointwise representatives on a countable dense star subring extend to
complex star representations almost everywhere. Each input identity is
required only almost everywhere for its fixed tuple of arguments. -/
theorem ae_exists_starRepresentation_of_countable_subring
    (S : Subring A) [Countable S] (hdense : Dense (S : Set A))
    (hstarS : ∀ a ∈ S, star a ∈ S) (hIS : algebraMap ℂ A Complex.I ∈ S)
    (f : ∀ _a : S, ∀ x, K x →L[ℂ] K x)
    (hzero : ∀ᵐ x ∂μ, f 0 x = 0)
    (hone : ∀ᵐ x ∂μ, f 1 x = 1)
    (hadd : ∀ a b : S, ∀ᵐ x ∂μ, f (a + b) x = f a x + f b x)
    (hmul : ∀ a b : S, ∀ᵐ x ∂μ, f (a * b) x = f a x * f b x)
    (hnorm : ∀ a : S, ∀ᵐ x ∂μ, ‖f a x‖ ≤ ‖a‖)
    (hstar : ∀ a : S, ∀ᵐ x ∂μ,
      f ⟨star a.val, hstarS a.val a.property⟩ x = star (f a x))
    (hI : ∀ᵐ x ∂μ, f ⟨algebraMap ℂ A Complex.I, hIS⟩ x =
      algebraMap ℂ (K x →L[ℂ] K x) Complex.I) :
    ∀ᵐ x ∂μ, ∃ σ : A →⋆ₐ[ℂ] (K x →L[ℂ] K x), ∀ a : S, σ a = f a x := by
  have hadd_all : ∀ᵐ x ∂μ, ∀ a b : S, f (a + b) x = f a x + f b x :=
    eventually_countable_forall.mpr fun a => eventually_countable_forall.mpr (hadd a)
  have hmul_all : ∀ᵐ x ∂μ, ∀ a b : S, f (a * b) x = f a x * f b x :=
    eventually_countable_forall.mpr fun a => eventually_countable_forall.mpr (hmul a)
  have hnorm_all : ∀ᵐ x ∂μ, ∀ a : S, ‖f a x‖ ≤ ‖a‖ :=
    eventually_countable_forall.mpr hnorm
  have hstar_all : ∀ᵐ x ∂μ, ∀ a : S,
      f ⟨star a.val, hstarS a.val a.property⟩ x = star (f a x) :=
    eventually_countable_forall.mpr hstar
  filter_upwards [hzero, hone, hadd_all, hmul_all, hnorm_all, hstar_all, hI]
    with x hz ho ha hm hn hs hi
  let F : S →+* (K x →L[ℂ] K x) := {
    toFun := fun a => f a x
    map_zero' := hz
    map_one' := ho
    map_add' := ha
    map_mul' := hm }
  exact exists_starRepresentation_of_dense_subring S hdense hstarS hIS F hn hs hi

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_CountableDenseStarSubring
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Countable dense star subrings

A separable complex C-star algebra has a countable norm-dense subring,
closed under star and containing the scalar `i`. This supplies the domain
on which countably many almost-everywhere algebra identities suffice.
-/

noncomputable section
namespace KadisonSimilarity

open scoped Topology Pointwise

theorem countable_subringClosure {R : Type*} [Ring R] {s : Set R}
    (hs : s.Countable) : (Subring.closure s : Set R).Countable := by
  let : Countable s := hs.to_subtype
  let f : FreeRing s →+* R := FreeRing.lift (fun x : s => (x : R))
  have hle : Subring.closure s ≤ f.range := Subring.closure_le.mpr fun x hx => by
    exact ⟨FreeRing.of ⟨x, hx⟩, FreeRing.lift_of _ _⟩
  exact (Set.countable_range f).mono hle

theorem star_mem_subringClosure_union {R : Type*} [Ring R] [StarRing R]
    (s : Set R) {x : R} (hx : x ∈ Subring.closure (s ∪ star s)) :
    star x ∈ Subring.closure (s ∪ star s) := by
  induction hx using Subring.closure_induction with
  | mem x hx =>
      apply Subring.subset_closure
      rcases hx with hx | hx
      · exact Or.inr (Set.star_mem_star.mpr hx)
      · exact Or.inl (Set.mem_star.mp hx)
  | zero => simpa only [star_zero] using (Subring.closure (s ∪ star s)).zero_mem
  | one => simpa only [star_one] using (Subring.closure (s ∪ star s)).one_mem
  | add x y _ _ hx hy => simpa only [star_add] using add_mem hx hy
  | neg x _ hx => simpa only [star_neg] using neg_mem hx
  | mul x y _ _ hx hy => simpa only [star_mul] using mul_mem hy hx

/-- A concrete countable domain for gathering the pointwise fiber laws. -/
theorem exists_countable_dense_star_subring (A : Type*) [CStarAlgebra A]
    [TopologicalSpace.SeparableSpace A] :
    ∃ S : Subring A, (S : Set A).Countable ∧ Dense (S : Set A) ∧
      (∀ a ∈ S, star a ∈ S) ∧ algebraMap ℂ A Complex.I ∈ S := by
  let s : Set A := Set.range (TopologicalSpace.denseSeq A) ∪
    {algebraMap ℂ A Complex.I}
  let S := Subring.closure (s ∪ star s)
  have hs : s.Countable := (Set.countable_range _).union (Set.countable_singleton _)
  have hstar : (star s).Countable := by
    rw [← Set.image_star]
    exact hs.image star
  refine ⟨S, countable_subringClosure (hs.union hstar), ?_, ?_, ?_⟩
  · exact (TopologicalSpace.denseRange_denseSeq A).mono fun a ha =>
      Subring.subset_closure (Or.inl (Or.inl ha))
  · exact fun a ha => star_mem_subringClosure_union s ha
  · exact Subring.subset_closure (Or.inl (Or.inr (Set.mem_singleton _)))

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_AERepresentationAgreement
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Agreement of the reconstructed fiber representations

For each fixed algebra element, the genuine representations reconstructed
from a countable dense subring agree almost everywhere with the original
operator representatives. Only countably many approximants are used for
that element; no uncountable intersection of conull sets is taken.
-/

noncomputable section
namespace KadisonSimilarity

open MeasureTheory Filter
open scoped Topology CStarAlgebra

variable {A : Type*} [CStarAlgebra A]
  {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  (K : Ω → Type*) [∀ x, NormedAddCommGroup (K x)]
  [∀ x, InnerProductSpace ℂ (K x)] [∀ x, CompleteSpace (K x)]

/-- Every extension of the dense-subring representatives has the correct
value at a fixed `a`, outside a null set that may depend on `a`. -/
theorem ae_starRepresentation_agrees_at
    (S : Subring A) (hdense : Dense (S : Set A))
    (f : ∀ _a : A, ∀ x, K x →L[ℂ] K x)
    (hsub : ∀ a b : A, ∀ᵐ x ∂μ, f (a - b) x = f a x - f b x)
    (hnorm : ∀ a : A, ∀ᵐ x ∂μ, ‖f a x‖ ≤ ‖a‖) (a : A) :
    ∀ᵐ x ∂μ, ∀ σ : A →⋆ₐ[ℂ] (K x →L[ℂ] K x),
      (∀ b : S, σ b = f b x) → σ a = f a x := by
  obtain ⟨b, hb, hlim⟩ := mem_closure_iff_seq_limit.mp (hdense a)
  have hsub_all : ∀ᵐ x ∂μ, ∀ n : ℕ, f (a - b n) x = f a x - f (b n) x :=
    eventually_countable_forall.mpr (fun n => hsub a (b n))
  have hnorm_all : ∀ᵐ x ∂μ, ∀ n : ℕ, ‖f (a - b n) x‖ ≤ ‖a - b n‖ :=
    eventually_countable_forall.mpr (fun n => hnorm (a - b n))
  filter_upwards [hsub_all, hnorm_all] with x hsubx hnormx
  intro σ hσ
  have hbound (n : ℕ) : ‖σ a - f a x‖ ≤ ‖a - b n‖ + ‖a - b n‖ := by
    calc
      ‖σ a - f a x‖ ≤ ‖σ a - σ (b n)‖ + ‖σ (b n) - f a x‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ ‖a - b n‖ + ‖a - b n‖ := add_le_add
        (by rw [← map_sub]; exact NonUnitalStarAlgHom.norm_apply_le σ _)
        (by
          rw [hσ ⟨b n, hb n⟩, norm_sub_rev, ← hsubx n]
          exact hnormx n)
  have hzero : Tendsto (fun n => ‖a - b n‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => a) atTop (𝓝 a)).sub hlim).norm
  have hle : ‖σ a - f a x‖ ≤ 0 := by
    simpa only [zero_add] using ge_of_tendsto' (hzero.add hzero) hbound
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hle (norm_nonneg _)))

/-- Countably many fiber relations suffice for genuine representations,
and their values agree almost everywhere with every fixed original section.
The statement leaves exceptional fibers unspecified. -/
theorem exists_dense_subring_ae_fiber_representations
    [TopologicalSpace.SeparableSpace A]
    (f : ∀ _a : A, ∀ x, K x →L[ℂ] K x)
    (hzero : ∀ᵐ x ∂μ, f 0 x = 0)
    (hone : ∀ᵐ x ∂μ, f 1 x = 1)
    (hadd : ∀ a b : A, ∀ᵐ x ∂μ, f (a + b) x = f a x + f b x)
    (hmul : ∀ a b : A, ∀ᵐ x ∂μ, f (a * b) x = f a x * f b x)
    (hnorm : ∀ a : A, ∀ᵐ x ∂μ, ‖f a x‖ ≤ ‖a‖)
    (hstar : ∀ a : A, ∀ᵐ x ∂μ, f (star a) x = star (f a x))
    (hI : ∀ᵐ x ∂μ, f (algebraMap ℂ A Complex.I) x =
      algebraMap ℂ (K x →L[ℂ] K x) Complex.I) :
    ∃ S : Subring A, Countable S ∧ Dense (S : Set A) ∧
      (∀ᵐ x ∂μ, ∃ σ : A →⋆ₐ[ℂ] (K x →L[ℂ] K x), ∀ b : S, σ b = f b x) ∧
      (∀ a : A, ∀ᵐ x ∂μ, ∀ σ : A →⋆ₐ[ℂ] (K x →L[ℂ] K x),
        (∀ b : S, σ b = f b x) → σ a = f a x) := by
  obtain ⟨S, hcount, hdense, hstarS, hIS⟩ := exists_countable_dense_star_subring A
  let : Countable S := hcount.to_subtype
  refine ⟨S, inferInstance, hdense, ?_, ?_⟩
  · exact ae_exists_starRepresentation_of_countable_subring μ K S hdense hstarS hIS
      (fun b x => f b x) hzero hone (fun a b => hadd a b) (fun a b => hmul a b)
      (fun a => hnorm a) (fun a => hstar a) hI
  · intro a
    apply ae_starRepresentation_agrees_at μ K S hdense f _ hnorm a
    intro b c
    filter_upwards [hadd (b - c) c] with x hx
    apply eq_sub_iff_add_eq.mpr
    simpa only [sub_add_cancel] using hx.symm

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_ConullStarRepresentations
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Genuine fiber representations on a measurable conull base

Restricting to a measurable conull set allows the almost-everywhere
representation theorem to be used as an actual family of representations.
The original section for each fixed algebra element remains unchanged
almost everywhere after this restriction.
-/

noncomputable section
namespace KadisonSimilarity

open MeasureTheory Filter

variable {A : Type*} [CStarAlgebra A]
  {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  (K : Ω → Type*) [∀ x, NormedAddCommGroup (K x)]
  [∀ x, InnerProductSpace ℂ (K x)] [∀ x, CompleteSpace (K x)]

/-- Choose genuine representations on a measurable conull set, retaining
the prescribed representatives almost everywhere for each fixed element. -/
theorem exists_conull_starRepresentations
    (S : Subring A) (f : ∀ _a : A, ∀ x, K x →L[ℂ] K x)
    (hexists : ∀ᵐ x ∂μ, ∃ σ : A →⋆ₐ[ℂ] (K x →L[ℂ] K x),
      ∀ b : S, σ b = f b x)
    (hagrees : ∀ a : A, ∀ᵐ x ∂μ, ∀ σ : A →⋆ₐ[ℂ] (K x →L[ℂ] K x),
      (∀ b : S, σ b = f b x) → σ a = f a x) :
    ∃ s : Set Ω, MeasurableSet s ∧ μ sᶜ = 0 ∧
      ∃ σ : ∀ x : s, A →⋆ₐ[ℂ] (K x →L[ℂ] K x),
        ∀ a : A, ∀ᵐ x ∂Measure.comap ((↑) : s → Ω) μ, σ x a = f a x := by
  classical
  obtain ⟨s, hs, hsm, hsexists⟩ := hexists.exists_measurable_mem
  choose σ hσ using fun x : s => hsexists x x.property
  refine ⟨s, hsm, ?_, σ, ?_⟩
  · exact (mem_ae_iff.mp hs)
  · intro a
    have h := (ae_restrict_iff_subtype hsm).mp (ae_restrict_of_ae (hagrees a))
    exact h.mono fun x hx => hx (σ x) (hσ x)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_DiagonalFieldAction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Pointwise action on all L² vectors

The field reconstructed from constant columns acts pointwise on arbitrary
L² vectors. Indicator constants give a dense class; two successive AE
subsequences prove that the pointwise-action identity is norm closed.
-/

noncomputable section
namespace KadisonSimilarity

open MeasureTheory Filter
open scoped Topology ENNReal

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [TopologicalSpace.SeparableSpace H]

omit [IsFiniteMeasure μ] [CompleteSpace H] [TopologicalSpace.SeparableSpace H] in
/-- An AE norm bound on a conull pointwise field bounds the original L²
operator. This proves the converse direction of the essential-norm formula. -/
theorem norm_le_of_conull_pointwise_action
    (T : Lp H 2 μ →L[ℂ] Lp H 2 μ)
    (s : Set Ω) (hsm : MeasurableSet s) (hsnull : μ sᶜ = 0)
    (field : ∀ _a : s, H →L[ℂ] H)
    (haction : ∀ f : Lp H 2 μ, ∀ᵐ (a : s) ∂Measure.comap ((↑) : s → Ω) μ,
      T f a = field a (f a))
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ᵐ (a : s) ∂Measure.comap ((↑) : s → Ω) μ, ‖field a‖ ≤ C) : ‖T‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro f
  have hs : ∀ᵐ a ∂μ, a ∈ s := mem_ae_iff.mpr hsnull
  have hsub : ∀ᵐ (a : s) ∂Measure.comap ((↑) : s → Ω) μ, ‖T f a‖ ≤ C * ‖f a‖ := by
    filter_upwards [haction f, hbound] with a he hb
    rw [he]
    exact ((field a).le_opNorm _).trans (mul_le_mul_of_nonneg_right hb (norm_nonneg _))
  have hglobal : ∀ᵐ a ∂μ, ‖T f a‖ ≤ C * ‖f a‖ := by
    have hr : ∀ᵐ a ∂μ.restrict s, ‖T f a‖ ≤ C * ‖f a‖ :=
      (ae_restrict_iff_subtype (μ := μ)
        (p := fun a : Ω => ‖T f a‖ ≤ C * ‖f a‖) hsm).mpr hsub
    filter_upwards [hs, (ae_restrict_iff' hsm).mp hr] with a ha h
    exact h ha
  calc
    ‖T f‖ ≤ ‖(C : ℂ) • f‖ := by
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [hglobal, Lp.coeFn_smul (C : ℂ) f] with a ha he
      rw [he, Pi.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hC]
      exact ha
    _ = C * ‖f‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_DiagonalFieldAlgebra
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Algebraic laws for fields of diagonal-commuting operators

The fields are constructed from the actual operators. Their algebraic laws
hold almost everywhere, by the pointwise action on all L² vectors and a
countable dense family of constant columns.
-/

noncomputable section
namespace KadisonSimilarity

open MeasureTheory Filter
open scoped Topology ENNReal

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

theorem diagonalField_norm
    (T : Lp H 2 μ →L[ℂ] Lp H 2 μ)
    (hT : ∀ (r : Set Ω) (hr : MeasurableSet r),
      T * l2Localization μ r hr = l2Localization μ r hr * T) (a : Ω) :
    ‖diagonalField μ T hT a‖ ≤ ‖T‖ :=
  (Classical.choose_spec (exists_global_diagonal_field μ T hT)).1 a

omit [CompleteSpace H] in
/-- Zero is preserved by any field realizing its pointwise action. -/
theorem pointwise_field_zero (R : Ω → H →L[ℂ] H)
    (hR : ∀ f : Lp H 2 μ, ∀ᵐ a ∂μ, (0 : Lp H 2 μ →L[ℂ] Lp H 2 μ) f a = R a (f a)) :
    ∀ᵐ a ∂μ, R a = 0 := by
  apply ae_operator_eq_of_forall_vectors
  intro x
  filter_upwards [pointwise_action_column μ 0 R hR x, Lp.coeFn_zero H 2 μ] with a ha hz
  simpa only [zero_apply, hz, Pi.zero_apply] using ha.symm

omit [CompleteSpace H] in
/-- The identity is preserved almost everywhere. -/
theorem pointwise_field_one (R : Ω → H →L[ℂ] H)
    (hR : ∀ f : Lp H 2 μ, ∀ᵐ a ∂μ, (1 : Lp H 2 μ →L[ℂ] Lp H 2 μ) f a = R a (f a)) :
    ∀ᵐ a ∂μ, R a = 1 := by
  apply ae_operator_eq_of_forall_vectors
  intro x
  filter_upwards [pointwise_action_column μ 1 R hR x, Lp.coeFn_const 2 μ x] with a ha hc
  simpa only [one_apply_eq_self, hc, Function.const_apply] using ha.symm

omit [CompleteSpace H] in
/-- Addition of L² operators becomes addition of their fields. -/
theorem pointwise_field_add
    (T S : Lp H 2 μ →L[ℂ] Lp H 2 μ) (R Q U : Ω → H →L[ℂ] H)
    (hR : ∀ f : Lp H 2 μ, ∀ᵐ a ∂μ, T f a = R a (f a))
    (hQ : ∀ f : Lp H 2 μ, ∀ᵐ a ∂μ, S f a = Q a (f a))
    (hU : ∀ f : Lp H 2 μ, ∀ᵐ a ∂μ, (T + S) f a = U a (f a)) :
    ∀ᵐ a ∂μ, U a = R a + Q a := by
  apply ae_operator_eq_of_forall_vectors
  intro x
  filter_upwards [pointwise_action_column μ T R hR x,
    pointwise_action_column μ S Q hQ x, pointwise_action_column μ (T + S) U hU x,
    Lp.coeFn_add (T (Lp.const 2 μ x)) (S (Lp.const 2 μ x))] with a hr hq hu hadd
  simpa only [add_apply, hadd, Pi.add_apply, hr, hq] using hu.symm

omit [CompleteSpace H] in
/-- Complex scalar multiplication, in particular multiplication by `i`,
is inherited from the actual L² operators. -/
theorem pointwise_field_smul
    (c : ℂ) (T : Lp H 2 μ →L[ℂ] Lp H 2 μ) (R U : Ω → H →L[ℂ] H)
    (hR : ∀ f : Lp H 2 μ, ∀ᵐ a ∂μ, T f a = R a (f a))
    (hU : ∀ f : Lp H 2 μ, ∀ᵐ a ∂μ, (c • T) f a = U a (f a)) :
    ∀ᵐ a ∂μ, U a = c • R a := by
  apply ae_operator_eq_of_forall_vectors
  intro x
  filter_upwards [pointwise_action_column μ T R hR x,
    pointwise_action_column μ (c • T) U hU x,
    Lp.coeFn_smul c (T (Lp.const 2 μ x))] with a hr hu hsmul
  simpa only [smul_apply, hsmul, Pi.smul_apply, hr] using hu.symm

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_DiagonalFieldAdjoint
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Adjoint compatibility of the actual diagonal field

Localized inner products recover the adjoint identity almost everywhere.
Together with the algebraic laws, this supplies the raw AE relations needed
for the conull fiber-representation construction.
-/

noncomputable section
namespace KadisonSimilarity

open MeasureTheory Filter
open scoped Topology ENNReal

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- A measurable localization is symmetric for the L² inner product. -/
theorem l2Localization_inner (s : Set Ω) (hs : MeasurableSet s)
    (f g : Lp H 2 μ) :
    inner ℂ (l2Localization μ s hs f) g = inner ℂ f (l2Localization μ s hs g) := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [l2Localization_ae μ s hs f, l2Localization_ae μ s hs g]
    with a hf hg
  rw [hf, hg]
  by_cases ha : a ∈ s
  · simp only [Set.indicator_of_mem ha]
  · simp only [Set.indicator_of_notMem ha, inner_zero_left, inner_zero_right]

omit [CompleteSpace H] in
/-- The right-indicator version of the standard L² set-integral formula. -/
theorem inner_indicatorConstLp_right (f : Lp H 2 μ)
    (s : Set Ω) (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (y : H) :
    inner ℂ f (indicatorConstLp 2 hs hμs y) = ∫ a in s, inner ℂ (f a) y ∂μ := by
  rw [L2.inner_def, ← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμs) (c := y)]
    with a ha
  rw [ha]
  by_cases h : a ∈ s
  · simp only [Set.indicator_of_mem h]
  · simp only [Set.indicator_of_notMem h, inner_zero_right]

variable [IsFiniteMeasure μ]

/-- Equality of all localized inner products identifies adjoint constant
columns almost everywhere. -/
theorem diagonal_adjoint_columns
    (T : Lp H 2 μ →L[ℂ] Lp H 2 μ)
    (hT : ∀ (r : Set Ω) (hr : MeasurableSet r),
      T * l2Localization μ r hr = l2Localization μ r hr * T) (x y : H) :
    ∀ᵐ a ∂μ, inner ℂ x (T (Lp.const 2 μ y) a) =
      inner ℂ ((star T) (Lp.const 2 μ x) a) y := by
  apply ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
  · intro s _ hμs
    exact (integrableOn_Lp_of_measure_ne_top (T (Lp.const 2 μ y))
      fact_one_le_two_ennreal.elim hμs.ne).const_inner x
  · intro s _ hμs
    exact (integrableOn_Lp_of_measure_ne_top ((star T) (Lp.const 2 μ x))
      fact_one_le_two_ennreal.elim hμs.ne).inner_const y
  · intro s hs hμs
    have hcomm := congrArg (fun A : Lp H 2 μ →L[ℂ] Lp H 2 μ => A (Lp.const 2 μ y))
      (hT s hs)
    change T (l2Localization μ s hs (Lp.const 2 μ y)) =
      l2Localization μ s hs (T (Lp.const 2 μ y)) at hcomm
    calc
      (∫ a in s, inner ℂ x (T (Lp.const 2 μ y) a) ∂μ) =
          inner ℂ (indicatorConstLp 2 hs hμs.ne x) (T (Lp.const 2 μ y)) :=
        (L2.inner_indicatorConstLp_eq_setIntegral_inner ℂ _ hs x hμs.ne).symm
      _ = inner ℂ (l2Localization μ s hs (Lp.const 2 μ x)) (T (Lp.const 2 μ y)) := by
        rw [l2Localization_const]
      _ = inner ℂ (Lp.const 2 μ x) (l2Localization μ s hs (T (Lp.const 2 μ y))) :=
        l2Localization_inner μ s hs _ _
      _ = inner ℂ (Lp.const 2 μ x) (T (l2Localization μ s hs (Lp.const 2 μ y))) := by
        rw [hcomm]
      _ = inner ℂ ((star T) (Lp.const 2 μ x)) (l2Localization μ s hs (Lp.const 2 μ y)) :=
        (ContinuousLinearMap.adjoint_inner_left T _ _).symm
      _ = inner ℂ ((star T) (Lp.const 2 μ x)) (indicatorConstLp 2 hs hμs.ne y) := by
        rw [l2Localization_const]
      _ = ∫ a in s, inner ℂ ((star T) (Lp.const 2 μ x) a) y ∂μ :=
        inner_indicatorConstLp_right μ _ s hs hμs.ne y

variable [TopologicalSpace.SeparableSpace H]

/-- Adjoint compatibility follows from the original operator's localized
inner products, rather than being postulated as a field relation. -/
theorem pointwise_field_star
    (T : Lp H 2 μ →L[ℂ] Lp H 2 μ)
    (hT : ∀ (r : Set Ω) (hr : MeasurableSet r),
      T * l2Localization μ r hr = l2Localization μ r hr * T)
    (R Q : Ω → H →L[ℂ] H)
    (hR : ∀ f : Lp H 2 μ, ∀ᵐ a ∂μ, T f a = R a (f a))
    (hQ : ∀ f : Lp H 2 μ, ∀ᵐ a ∂μ, (star T) f a = Q a (f a)) :
    ∀ᵐ a ∂μ, Q a = star (R a) := by
  apply ae_operator_eq_of_forall_vectors
  intro x
  have hpair (y : H) : ∀ᵐ a ∂μ, inner ℂ (Q a x) y = inner ℂ x (R a y) := by
    filter_upwards [diagonal_adjoint_columns μ T hT x y,
      pointwise_action_column μ T R hR y,
      pointwise_action_column μ (star T) Q hQ x] with a ha hr hq
    rw [hr, hq] at ha
    exact ha.symm
  have hall : ∀ᵐ a ∂μ, ∀ n : ℕ,
      inner ℂ (Q a x) (TopologicalSpace.denseSeq H n) =
        inner ℂ x (R a (TopologicalSpace.denseSeq H n)) :=
    eventually_countable_forall.mpr fun n => hpair (TopologicalSpace.denseSeq H n)
  filter_upwards [hall] with a ha
  apply ext_inner_right ℂ
  intro y
  have heq : (fun z => inner ℂ (Q a x) z) = (fun z => inner ℂ x (R a z)) :=
    (TopologicalSpace.denseRange_denseSeq H).equalizer
      (by fun_prop) (by fun_prop) (funext ha)
  rw [congrFun heq y]
  exact (ContinuousLinearMap.adjoint_inner_left (R a) y x).symm

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_DiagonalFiberRepresentations
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Genuine representations of the diagonal commutant

For a norm-separable C-star algebra acting on a constant-fiber L² space,
commutation with measurable localizations gives genuine representations on
a conull base. All raw AE algebraic relations are derived from the actual
L² action. The original operator norm is recovered from the fiber norms.
-/

noncomputable section
namespace KadisonSimilarity

open MeasureTheory Filter
open scoped Topology ENNReal CStarAlgebra

variable {A Ω H : Type*} [CStarAlgebra A] [TopologicalSpace.SeparableSpace A]
  [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

/-- Actual diagonal-commuting representations decompose into genuine fiber
representations, with pointwise action on every L² vector and the exact
scalar norm-bound equivalence. -/
theorem exists_conull_diagonal_star_representations
    (σ : A →⋆ₐ[ℂ] (Lp H 2 μ →L[ℂ] Lp H 2 μ))
    (hσ : ∀ (b : A) (r : Set Ω) (hr : MeasurableSet r),
      σ b * l2Localization μ r hr = l2Localization μ r hr * σ b) :
    ∃ s : Set Ω, MeasurableSet s ∧ μ sᶜ = 0 ∧
      ∃ ρ : ∀ _a : s, A →⋆ₐ[ℂ] (H →L[ℂ] H),
        (∀ (b : A) (f : Lp H 2 μ),
          ∀ᵐ (a : s) ∂Measure.comap ((↑) : s → Ω) μ,
            σ b f a = ρ a b (f a)) ∧
        ∀ (b : A) (C : ℝ), 0 ≤ C →
          (‖σ b‖ ≤ C ↔ ∀ᵐ (a : s) ∂Measure.comap ((↑) : s → Ω) μ, ‖ρ a b‖ ≤ C) := by
  let F : A → Ω → H →L[ℂ] H := fun b => diagonalField μ (σ b) (hσ b)
  have hact (b : A) (f : Lp H 2 μ) : ∀ᵐ a ∂μ, σ b f a = F b a (f a) :=
    diagonalField_action μ (σ b) (hσ b) f
  have hzero : ∀ᵐ a ∂μ, F 0 a = 0 :=
    pointwise_field_zero μ _ (by simpa only [map_zero] using hact 0)
  have hone : ∀ᵐ a ∂μ, F 1 a = 1 :=
    pointwise_field_one μ _ (by simpa only [map_one] using hact 1)
  have hadd (b c : A) : ∀ᵐ a ∂μ, F (b + c) a = F b a + F c a :=
    pointwise_field_add μ (σ b) (σ c) _ _ _ (hact b) (hact c)
      (by simpa only [map_add] using hact (b + c))
  have hmul (b c : A) : ∀ᵐ a ∂μ, F (b * c) a = F b a * F c a :=
    pointwise_field_mul μ (σ b) (σ c) _ _ _ (hact b) (hact c)
      (by simpa only [map_mul] using hact (b * c))
  have hnorm (b : A) : ∀ᵐ a ∂μ, ‖F b a‖ ≤ ‖b‖ :=
    .of_forall fun a => (diagonalField_norm μ (σ b) (hσ b) a).trans
      (NonUnitalStarAlgHom.norm_apply_le σ b)
  have hstar (b : A) : ∀ᵐ a ∂μ, F (star b) a = star (F b a) :=
    pointwise_field_star μ (σ b) (hσ b) _ _ (hact b)
      (by simpa only [map_star] using hact (star b))
  have hI : ∀ᵐ a ∂μ, F (algebraMap ℂ A Complex.I) a =
      algebraMap ℂ (H →L[ℂ] H) Complex.I := by
    have hσI : σ (algebraMap ℂ A Complex.I) = Complex.I • 1 := by
      rw [Algebra.algebraMap_eq_smul_one, map_smul, map_one]
    have hi := pointwise_field_smul μ Complex.I 1 (F 1)
      (F (algebraMap ℂ A Complex.I))
      (by simpa only [map_one] using hact 1)
      (by simpa only [hσI] using
        hact (algebraMap ℂ A Complex.I))
    filter_upwards [hi, hone] with a ha ho
    simpa only [ho, Algebra.algebraMap_eq_smul_one] using ha
  obtain ⟨S, _, _, hexists, hagrees⟩ :=
    exists_dense_subring_ae_fiber_representations μ (fun _ => H)
      F hzero hone hadd hmul hnorm hstar hI
  obtain ⟨s, hsm, hsnull, ρ, hρ⟩ :=
    exists_conull_starRepresentations μ (fun _ => H) S F hexists hagrees
  have haction (b : A) (f : Lp H 2 μ) :
      ∀ᵐ (a : s) ∂Measure.comap ((↑) : s → Ω) μ, σ b f a = ρ a b (f a) := by
    have h := (ae_restrict_iff_subtype hsm).mp (ae_restrict_of_ae (hact b f))
    filter_upwards [h, hρ b] with a ha hb
    rw [hb]
    exact ha
  refine ⟨s, hsm, hsnull, ρ, haction, ?_⟩
  intro b C hC
  constructor
  · intro hb
    have hn : ∀ᵐ (a : s) ∂Measure.comap ((↑) : s → Ω) μ, ‖F b a‖ ≤ ‖σ b‖ := by
      apply (ae_restrict_iff_subtype (μ := μ)
        (p := fun a : Ω => ‖F b a‖ ≤ ‖σ b‖) hsm).mp
      exact ae_restrict_of_ae (.of_forall (diagonalField_norm μ (σ b) (hσ b)))
    filter_upwards [hρ b, hn] with a ha hn
    rw [ha]
    exact hn.trans hb
  · exact norm_le_of_conull_pointwise_action μ (σ b) s hsm hsnull
      (fun a => ρ a b) (haction b) C hC

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_UnitalizedExtension
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extension by zero is a nonunital star homomorphism. Its unitization
provides a genuine representation whose distinguished projection recovers
the original Hilbert subspace. -/

noncomputable section
namespace KadisonSimilarity

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (J : H →ₗᵢ[ℂ] K)

variable {B : Type*} [CStarAlgebra B] (σ : B →⋆ₐ[ℂ] (H →L[ℂ] H))

omit [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] in
theorem separable_unitization [TopologicalSpace.SeparableSpace B] :
    TopologicalSpace.SeparableSpace (Unitization ℂ B) :=
  (Unitization.uniformEquivProd.symm.surjective.denseRange).separableSpace
    Unitization.uniformEquivProd.symm.continuous

theorem unitalizedExtension_apply (b : Unitization ℂ B) :
    unitalizedExtension J σ b = b.fst • (1 : K →L[ℂ] K) +
      isometricExtension J (σ b.snd) := by
  change algebraMap ℂ (K →L[ℂ] K) b.fst + isometricExtension J (σ b.snd) = _
  rw [Algebra.algebraMap_eq_smul_one]

theorem unitalizedExtension_commutes (R : K →L[ℂ] K)
    (hR : ∀ b, isometricExtension J (σ b) * R = R * isometricExtension J (σ b))
    (b : Unitization ℂ B) :
    unitalizedExtension J σ b * R = R * unitalizedExtension J σ b := by
  rw [unitalizedExtension_apply, add_mul, mul_add, smul_mul_assoc,
    mul_smul_comm, one_mul, mul_one, hR]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CommonSpectralMeasurable
attribute [-instance] _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # Borel representations in the common spectral model

The common spectral construction gives representations and their L²
action. A common-conull modification supplies Borel vector evaluations
for every source element while retaining that action.
-/

namespace KadisonKastler

open MeasureTheory KadisonSimilarity

noncomputable section

variable {A B H : Type*} [CommCStarAlgebra A] [TopologicalSpace.SeparableSpace A]
  [CStarAlgebra B] [TopologicalSpace.SeparableSpace B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (D : CyclicDecompositionData π.range)

attribute [local instance] commonCyclicMeasurable commonCyclicBorel commonCyclicCountable

local instance commonCoordinateMeasurable :
    MeasurableSpace (ScalarHilbertCoordinates D.generators) := borel _
local instance commonCoordinateBorel :
    BorelSpace (ScalarHilbertCoordinates D.generators) := ⟨rfl⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CountableProjectionFamilies
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Countable projection families from separating vectors

The spatial derivation argument needs countable decomposability of the
algebra, rather than separability of the ambient Hilbert space. A
countable family of separating vectors supplies exactly this property.
-/

namespace KadisonKastler

noncomputable section

open Generator.Tracial
open scoped BigOperators

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

def HasCountableProjectionFamilies (M : VonNeumannAlgebra H) : Prop :=
  ∀ (ι : Type u) (p : ι → AlgebraProjection M),
    (∀ i, (p i).val ≠ 0) →
    Pairwise (fun i j => (p i).val * (p j).val = 0) → Countable ι

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_HilbertVariance
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Orthogonal centering of Hilbert-valued square-integrable functions

The mean is the closest constant in L2. This is the variance estimate used
after conditioning on the middle and right independent random-walk blocks.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory

variable {X K : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

def hilbertConstantL2 (μ : Measure X) [IsProbabilityMeasure μ] (v : K) : Lp K 2 μ :=
  (memLp_const v).toLp (fun _ => v)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CountableUnitaryL2
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! Isometric multiplication in L2 by a countable measurable unitary field. -/

namespace KadisonKastler

noncomputable section

open MeasureTheory

variable {X G K : Type*} [mX : MeasurableSpace X] {μ : Measure X}
  [MeasurableSpace G] [Countable G] [MeasurableSingletonClass G]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [TopologicalSpace.SeparableSpace K]

theorem countableUnitaryAction_aestronglyMeasurable
    (U : G → unitary (K →L[ℂ] K)) {c : X → G} (hc : Measurable c)
    {f : X → K} (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun x => (U (c x) : K →L[ℂ] K) (f x)) μ := by
  borelize K
  have hm : Measurable (fun p : G × K => (U p.1 : K →L[ℂ] K) p.2) :=
    measurable_from_prod_countable_right (fun g => (U g : K →L[ℂ] K).continuous.measurable)
  exact (hm.comp_aemeasurable (hc.aemeasurable.prodMk hf.aemeasurable)).aestronglyMeasurable

theorem countableUnitaryAction_memLp
    (U : G → unitary (K →L[ℂ] K)) {c : X → G} (hc : Measurable c)
    {f : X → K} (hf : MemLp f 2 μ) :
    MemLp (fun x => (U (c x) : K →L[ℂ] K) (f x)) 2 μ :=
  hf.congr_norm (countableUnitaryAction_aestronglyMeasurable U hc hf.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => (Unitary.norm_map (U (c x)) (f x)).symm)

def countableUnitaryL2 (U : G → unitary (K →L[ℂ] K)) {c : X → G} (hc : Measurable c)
    (f : Lp K 2 μ) : Lp K 2 μ :=
  (countableUnitaryAction_memLp U hc (Lp.memLp f)).toLp _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CyclicGramEquivalence
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Cyclic Hilbert identifications from matching finite Gram matrices

The pointed matrix-product reindexing identifies finite word vectors.
That identification extends from their dense linear spans to the Hilbert spaces.
-/

namespace KadisonKastler

noncomputable section

variable {I H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace H] [CompleteSpace K] in
theorem norm_linearCombination_eq_of_gram (v : I → H) (w : I → K)
    (h : ∀ i j, inner ℂ (v i) (v j) = inner ℂ (w i) (w j)) (c : I →₀ ℂ) :
    ‖Finsupp.linearCombination ℂ v c‖ = ‖Finsupp.linearCombination ℂ w c‖ := by
  have hi : inner ℂ (Finsupp.linearCombination ℂ v c) (Finsupp.linearCombination ℂ v c) =
      inner ℂ (Finsupp.linearCombination ℂ w c) (Finsupp.linearCombination ℂ w c) := by
    simp only [Finsupp.linearCombination_apply, Finsupp.sum_inner, Finsupp.inner_sum,
      inner_smul_left, inner_smul_right, h]
  have hs : ‖Finsupp.linearCombination ℂ v c‖ ^ 2 =
      ‖Finsupp.linearCombination ℂ w c‖ ^ 2 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ)]
    exact congrArg Complex.re hi
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs

/-- The Hilbert-space identification of two dense families with identical
Gram matrices, including the prescribed action on each family vector. -/
def cyclicGramEquivalence (v : I → H) (w : I → K)
    (hv : DenseRange (Finsupp.linearCombination ℂ v))
    (hw : DenseRange (Finsupp.linearCombination ℂ w))
    (h : ∀ i j, inner ℂ (v i) (v j) = inner ℂ (w i) (w j)) : H ≃ₗᵢ[ℂ] K :=
  (LinearEquiv.refl ℂ (I →₀ ℂ)).extendOfIsometry
    (Finsupp.linearCombination ℂ v) (Finsupp.linearCombination ℂ w) hv hw
    (fun c => (norm_linearCombination_eq_of_gram v w h c).symm)

theorem cyclicGramEquivalence_linearCombination (v : I → H) (w : I → K)
    (hv : DenseRange (Finsupp.linearCombination ℂ v))
    (hw : DenseRange (Finsupp.linearCombination ℂ w))
    (h : ∀ i j, inner ℂ (v i) (v j) = inner ℂ (w i) (w j)) (c : I →₀ ℂ) :
    cyclicGramEquivalence v w hv hw h (Finsupp.linearCombination ℂ v c) =
      Finsupp.linearCombination ℂ w c :=
  LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ c

theorem cyclicGramEquivalence_apply (v : I → H) (w : I → K)
    (hv : DenseRange (Finsupp.linearCombination ℂ v))
    (hw : DenseRange (Finsupp.linearCombination ℂ w))
    (h : ∀ i j, inner ℂ (v i) (v j) = inner ℂ (w i) (w j)) (i : I) :
    cyclicGramEquivalence v w hv hw h (v i) = w i := by
  simpa only [Finsupp.linearCombination_single, one_smul] using
    cyclicGramEquivalence_linearCombination v w hv hw h (Finsupp.single i 1)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixBlockSwap
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Finite permutations and block swaps of matrix units

These unitaries are finite sums of the given matrix units. No trace,
infinite tensor product, or existence premise is involved.
-/

namespace KadisonKastler

open Generator
open scoped BigOperators

noncomputable section

variable {ι A : Type*} [Fintype ι] [DecidableEq ι]
  [Ring A] [StarRing A] [_root_.Algebra ℂ A]

/-- The permutation matrix in an actual system of matrix units. -/
def matrixPermutationValue (E : MatrixUnitSystem ι A) (e : Equiv.Perm ι) : A :=
  ∑ i, E.entry (e i) i

theorem matrixPermutationValue_mul_entry (E : MatrixUnitSystem ι A)
    (e : Equiv.Perm ι) (i j : ι) :
    matrixPermutationValue E e * E.entry i j = E.entry (e i) j := by
  rw [matrixPermutationValue, Finset.sum_mul, Finset.sum_eq_single i]
  · simp only [E.mul_entry, ite_true, if_true]
  · intro k _ hki
    rw [E.mul_entry, ite_eq_right hki]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

theorem matrixPermutationValue_mul (E : MatrixUnitSystem ι A)
    (e f : Equiv.Perm ι) :
    matrixPermutationValue E e * matrixPermutationValue E f =
      matrixPermutationValue E (e * f) := by
  change matrixPermutationValue E e * (∑ i, E.entry (f i) i) = _
  rw [Finset.mul_sum]
  simp only [matrixPermutationValue_mul_entry]
  rfl

@[simp] theorem matrixPermutationValue_one (E : MatrixUnitSystem ι A) :
    matrixPermutationValue E 1 = 1 := E.total

theorem matrixPermutationValue_star (E : MatrixUnitSystem ι A)
    (e : Equiv.Perm ι) :
    star (matrixPermutationValue E e) = matrixPermutationValue E e.symm := by
  rw [matrixPermutationValue, star_sum]
  simp only [E.star_entry]
  simpa only [matrixPermutationValue, Equiv.symm_apply_apply] using
    (Equiv.sum_comp (e : ι ≃ ι) (fun j => E.entry (e.symm j) j))

/-- The finite permutation sum is an actual unitary. -/
def matrixPermutationUnitary (E : MatrixUnitSystem ι A) (e : Equiv.Perm ι) : unitary A :=
  ⟨matrixPermutationValue E e, by
    constructor <;> rw [matrixPermutationValue_star, matrixPermutationValue_mul]
    · simpa only [← Equiv.Perm.inv_def, inv_mul_cancel] using matrixPermutationValue_one E
    · simpa only [← Equiv.Perm.inv_def, mul_inv_cancel] using matrixPermutationValue_one E⟩

theorem matrixPermutationUnitary_conjugate_entry (E : MatrixUnitSystem ι A)
    (e : Equiv.Perm ι) (i j : ι) :
    (matrixPermutationUnitary E e : A) * E.entry i j *
      star (matrixPermutationUnitary E e : A) = E.entry (e i) (e j) := by
  change matrixPermutationValue E e * E.entry i j * star (matrixPermutationValue E e) = _
  rw [matrixPermutationValue_mul_entry, matrixPermutationValue_star, matrixPermutationValue,
    Finset.mul_sum, Finset.sum_eq_single (e j)]
  · simp only [Equiv.symm_apply_apply, E.mul_entry, ite_true, if_true]
  · intro k _ hkj
    rw [E.mul_entry, ite_eq_right]
    exact fun h => hkj (by simpa only [Equiv.apply_symm_apply] using congrArg e h.symm)
  · intro hj
    exact False.elim (hj (Finset.mem_univ (e j)))

/-- The unitary exchanging two equal finite tensor blocks. -/
def finiteMatrixBlockSwap (E : MatrixUnitSystem (ι × ι) A) : unitary A :=
  matrixPermutationUnitary E (Equiv.prodComm ι ι)

theorem finiteMatrixBlockSwap_value (E : MatrixUnitSystem (ι × ι) A) :
    (finiteMatrixBlockSwap E : A) = ∑ i, ∑ j, E.entry (i, j) (j, i) := by
  change matrixPermutationValue E (Equiv.prodComm ι ι) = _
  simp only [matrixPermutationValue, Fintype.sum_prod_type, Equiv.prodComm_apply]
  exact Finset.sum_comm

/-- Block swapping exchanges the two indices on each side. -/
theorem finiteMatrixBlockSwap_conjugate_entry (E : MatrixUnitSystem (ι × ι) A)
    (i j k l : ι) :
    (finiteMatrixBlockSwap E : A) * E.entry (i, j) (k, l) * star (finiteMatrixBlockSwap E : A) =
      E.entry (j, i) (l, k) :=
  matrixPermutationUnitary_conjugate_entry E (Equiv.prodComm ι ι) (i, j) (k, l)

/-- The swap belongs to the same finite matrix algebra. -/
theorem finiteMatrixBlockSwap_mem [StarModule ℂ A] (E : MatrixUnitSystem (ι × ι) A) :
    (finiteMatrixBlockSwap E : A) ∈ E.algebra := by
  rw [finiteMatrixBlockSwap_value]
  exact E.algebra.sum_mem fun i _ => E.algebra.sum_mem fun j _ => E.entry_mem _ _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProductStateCentralizer
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The centralizer of an infinite product state is irreducible

The proof uses only dense local vectors and state-preserving local swaps
which move a local observable to an independent set of sites. These are
the finite-site properties of the two-ratio tensor product in section 6.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The ambient vector functional, without any trace assumption. -/
def productVectorState (Ω : H) (T : H →L[ℂ] H) : ℂ := inner ℂ Ω (T Ω)

/-- The state centralizer identity used by a finite-site swap. -/
def ProductStateCentralizes (D : VonNeumannAlgebra H) (Ω : H) (u : H →L[ℂ] H) : Prop :=
  ∀ x ∈ D, productVectorState Ω (u * x) = productVectorState Ω (x * u)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixProductStateSwap
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Product moments put finite block swaps in the state centralizer

The finite calculation needs only the three-block product formula and
equal moments on the two blocks being exchanged. Strong density then
extends the resulting identities from local matrix algebras to their
generated von Neumann algebra.
-/

namespace KadisonKastler

open Generator Filter
open scoped BigOperators Topology

noncomputable section

section Finite

variable {ι κ A : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Ring A] [StarRing A] [_root_.Algebra ℂ A] [StarModule ℂ A]

omit [_root_.Algebra ℂ A] [StarModule ℂ A] in
theorem unitary_conjugation_mul (u : unitary A) (x y : A) :
    (u : A) * (x * y) * star (u : A) =
      ((u : A) * x * star (u : A)) * ((u : A) * y * star (u : A)) := by
  symm
  calc
    _ = (u : A) * x * (star (u : A) * u) * y * star (u : A) := by noncomm_ring
    _ = _ := by rw [Unitary.star_mul_self_of_mem u.property]; simp only [mul_one, mul_assoc]

/-- Equality on the matrix-unit coefficients implies equality on the
whole finite matrix algebra. -/
theorem matrix_functional_invariant_of_entries
    (E : MatrixUnitSystem ι A) (φ : A →ₗ[ℂ] ℂ) (u : unitary A)
    (hφ : ∀ i j, φ ((u : A) * E.entry i j * star (u : A)) = φ (E.entry i j))
    (x : A) (hx : x ∈ E.algebra) :
    φ ((u : A) * x * star (u : A)) = φ x := by
  obtain ⟨c, rfl⟩ := (E.mem_algebra x).mp hx
  simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc,
    map_sum, map_smul, hφ]

/-- Three-block product moments are invariant under swapping the two
equal-state blocks, with an arbitrary finite complement left in place. -/
theorem finiteMatrixBlockSwap_product_invariant
    (E : MatrixUnitSystem (ι × ι) A) (C : MatrixUnitSystem κ A)
    (hEC : ∀ i j k l, Commute (E.entry i j) (C.entry k l))
    (φ : A →ₗ[ℂ] ℂ) (α : ι → ι → ℂ) (β : κ → κ → ℂ)
    (hφ : ∀ i j k l r s,
      φ (E.entry (i, j) (k, l) * C.entry r s) = α i k * α j l * β r s)
    (x : A) (hx : x ∈ (E.product C hEC).algebra) :
    φ ((finiteMatrixBlockSwap E : A) * x * star (finiteMatrixBlockSwap E : A)) = φ x := by
  apply matrix_functional_invariant_of_entries (E.product C hEC) φ
    (finiteMatrixBlockSwap E) _ x hx
  rintro ⟨⟨i, j⟩, r⟩ ⟨⟨k, l⟩, s⟩
  have hc : Commute (finiteMatrixBlockSwap E : A) (C.entry r s) :=
    (E.commute_algebra_iff (C.entry r s)).mpr (fun a b => hEC a b r s)
      _ (finiteMatrixBlockSwap_mem E)
  have hfix : (finiteMatrixBlockSwap E : A) * C.entry r s *
      star (finiteMatrixBlockSwap E : A) = C.entry r s :=
    (commute_unitary_iff_star_right_conjugate (finiteMatrixBlockSwap E).property).mp hc
  change φ ((finiteMatrixBlockSwap E : A) *
      (E.entry (i, j) (k, l) * C.entry r s) * star (finiteMatrixBlockSwap E : A)) = _
  rw [unitary_conjugation_mul, finiteMatrixBlockSwap_conjugate_entry, hfix]
  change φ (E.entry (j, i) (l, k) * C.entry r s) =
    φ (E.entry (i, j) (k, l) * C.entry r s)
  rw [hφ, hφ]
  ring

/-- Product moments imply centralization on the finite joint algebra. -/
theorem finiteMatrixBlockSwap_product_centralizes
    (E : MatrixUnitSystem (ι × ι) A) (C : MatrixUnitSystem κ A)
    (hEC : ∀ i j k l, Commute (E.entry i j) (C.entry k l))
    (φ : A →ₗ[ℂ] ℂ) (α : ι → ι → ℂ) (β : κ → κ → ℂ)
    (hφ : ∀ i j k l r s,
      φ (E.entry (i, j) (k, l) * C.entry r s) = α i k * α j l * β r s)
    (x : A) (hx : x ∈ (E.product C hEC).algebra) :
    φ ((finiteMatrixBlockSwap E : A) * x) = φ (x * finiteMatrixBlockSwap E) := by
  have hu : (finiteMatrixBlockSwap E : A) ∈ (E.product C hEC).algebra :=
    (E.algebra_le_product_left C hEC) (finiteMatrixBlockSwap_mem E)
  have hi := finiteMatrixBlockSwap_product_invariant E C hEC φ α β hφ
    (x * finiteMatrixBlockSwap E) ((E.product C hEC).algebra.mul_mem hx hu)
  simpa only [mul_assoc, Unitary.mul_star_self_of_mem (finiteMatrixBlockSwap E).property,
    mul_one] using hi

omit [StarModule ℂ A] in
/-- In the product of two commuting copies, the block swap carries each
left matrix unit to the corresponding right matrix unit. -/
theorem finiteMatrixBlockSwap_conjugate_left_entry
    (E F : MatrixUnitSystem ι A)
    (hEF : ∀ i j k l, Commute (E.entry i j) (F.entry k l)) (i j : ι) :
    (finiteMatrixBlockSwap (E.product F hEF) : A) * E.entry i j *
      star (finiteMatrixBlockSwap (E.product F hEF) : A) = F.entry i j := by
  rw [← E.product_sum_left F hEF i j]
  simp only [Finset.mul_sum, Finset.sum_mul, finiteMatrixBlockSwap_conjugate_entry]
  exact E.product_sum_right F hEF i j

theorem finiteMatrixBlockSwap_conjugate_left_hom
    (E F : MatrixUnitSystem ι A)
    (hEF : ∀ i j k l, Commute (E.entry i j) (F.entry k l)) (c : Matrix ι ι ℂ) :
    (finiteMatrixBlockSwap (E.product F hEF) : A) * E.hom c *
      star (finiteMatrixBlockSwap (E.product F hEF) : A) = F.hom c := by
  rw [E.hom_apply, F.hom_apply]
  simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc,
    finiteMatrixBlockSwap_conjugate_left_entry]

/-- Independence of the remote block on matrix units implies the desired
factorization for every observable in the original finite block. -/
theorem finiteMatrixBlockSwap_independent
    (E F : MatrixUnitSystem ι A)
    (hEF : ∀ i j k l, Commute (E.entry i j) (F.entry k l))
    (φ : A →ₗ[ℂ] ℂ) (b : A)
    (hfar : ∀ i j, φ (F.entry i j * b) = φ (E.entry i j) * φ b)
    (a : A) (ha : a ∈ E.algebra) :
    φ (((finiteMatrixBlockSwap (E.product F hEF) : A) * a *
      star (finiteMatrixBlockSwap (E.product F hEF) : A)) * b) = φ a * φ b := by
  obtain ⟨c, rfl⟩ := (E.mem_algebra a).mp ha
  change φ (((finiteMatrixBlockSwap (E.product F hEF) : A) * E.hom c *
      star (finiteMatrixBlockSwap (E.product F hEF) : A)) * b) = φ (E.hom c) * φ b
  rw [finiteMatrixBlockSwap_conjugate_left_hom]
  simp only [F.hom_apply, E.hom_apply, Finset.sum_mul, smul_mul_assoc,
    map_sum, map_smul, hfar, smul_eq_mul, mul_assoc]

end Finite

section Vector

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The linear vector functional used by the finite product calculation. -/
def productVectorLinear (Ω : H) : (H →L[ℂ] H) →ₗ[ℂ] ℂ where
  toFun := productVectorState Ω
  map_add' _ _ := inner_add_right _ _ _
  map_smul' _ _ := inner_smul_right _ _ _

end Vector

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_Jordan
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# Orientation of surjective Jordan maps

This is the algebraic argument recalled in §5 of *Universal strong
Kadison–Kastler stability* (2026), following I. N. Herstein, *Jordan
homomorphisms*, Trans. Amer. Math. Soc. 81 (1956), 331–341. The target is
assumed prime explicitly; no von Neumann algebra representation is needed
for this algebraic step.
-/

namespace KadisonKastler

variable {A B : Type*} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B]

/-- Preservation of twice the Jordan product. Over the complex numbers
this is equivalent to preservation of `(x * y + y * x) / 2`. -/
def PreservesJordan (θ : A →ₗ[ℂ] B) : Prop :=
  ∀ x y, θ (x * y + y * x) = θ x * θ y + θ y * θ x

/-- The ring-theoretic primeness condition used by the orientation proof. -/
def IsPrimeAlgebra (B : Type*) [Ring B] : Prop :=
  ∀ a b : B, (∀ c : B, a * c * b = 0) → a = 0 ∨ b = 0

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SeparableAlgebraPair
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

def cstarHull (s : Set (H →L[ℂ] H)) : StarSubalgebra ℂ (H →L[ℂ] H) :=
  (StarAlgebra.adjoin ℂ s).topologicalClosure

def starAlgebraBall (A : StarSubalgebra ℂ (H →L[ℂ] H)) : Set (H →L[ℂ] H) :=
  {x | x ∈ A ∧ ‖x‖ ≤ 1}

theorem subset_cstarHull (s : Set (H →L[ℂ] H)) : s ⊆ cstarHull s :=
  (StarAlgebra.subset_adjoin ℂ s).trans (StarSubalgebra.le_topologicalClosure _)

omit [CompleteSpace H] in
/-- The bound on distance to a fixed set passes through norm closure. -/
theorem infDist_le_of_mem_closure {s t : Set (H →L[ℂ] H)} {r : ℝ}
    (h : ∀ x ∈ s, Metric.infDist x t ≤ r) {x : H →L[ℂ] H}
    (hx : x ∈ closure s) : Metric.infDist x t ≤ r :=
  closure_minimal h (isClosed_le (Metric.continuous_infDist_pt t) continuous_const) hx

structure SeparableSeeds (M N : VonNeumannAlgebra H) where
  left : Set (H →L[ℂ] H)
  right : Set (H →L[ℂ] H)
  left_countable : left.Countable
  right_countable : right.Countable
  left_mem : left ⊆ M
  right_mem : right ⊆ N

def SeparableSeeds.Extends {M N : VonNeumannAlgebra H}
    (p q : SeparableSeeds M N) (r : ℝ) : Prop :=
  p.left ⊆ q.left ∧ p.right ⊆ q.right ∧
  (∀ x ∈ starAlgebraBall (cstarHull p.left),
    Metric.infDist x (starAlgebraBall (cstarHull q.right)) ≤ r) ∧
  (∀ x ∈ starAlgebraBall (cstarHull p.right),
    Metric.infDist x (starAlgebraBall (cstarHull q.left)) ≤ r)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.TracialSplitting_SpatialTensor
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uA uB uE uF uH uK uι


section

noncomputable section

noncomputable section

open scoped ComplexOrder InnerProductSpace

open UniformSpace.Completion

noncomputable section

noncomputable section

noncomputable section

open scoped ComplexOrder InnerProductSpace

noncomputable section

open scoped TensorProduct InnerProductSpace

open UniformSpace.Completion

namespace UnitalTomsWinter

variable {H : Type uH} {K : Type uK} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

lemma completion_opNorm_le {E : Type uE} {F : Type uF} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (f : E →L[ℂ] F) : ‖f.completion‖ ≤ ‖f‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f)
  intro z
  induction z using UniformSpace.Completion.induction_on with
  | hp => apply isClosed_le <;> fun_prop
  | ih z => simpa using f.le_opNorm z

end UnitalTomsWinter

end

end

end

end

end

end

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CyclicGeneratorSpan
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Dense word-vector spans for cyclic generated algebras

A closed word span is reducing for each generator and hence for the
generated von Neumann algebra. Containing the cyclic vector makes it all
of the represented Hilbert space.
-/

namespace KadisonKastler

noncomputable section

variable {H I J : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Invariance on a spanning family passes to its closed linear span. -/
theorem invariant_closed_linearCombination_range
    (v : I → H) (T : H →L[ℂ] H)
    (h : ∀ i, T (v i) ∈ LinearMap.range (Finsupp.linearCombination ℂ v)) :
    ∀ x ∈ (LinearMap.range (Finsupp.linearCombination ℂ v)).topologicalClosure,
      T x ∈ (LinearMap.range (Finsupp.linearCombination ℂ v)).topologicalClosure := by
  let V := LinearMap.range (Finsupp.linearCombination ℂ v)
  have hV : V ≤ V.topologicalClosure.comap T.toLinearMap := by
    rintro x ⟨c, rfl⟩
    change T (Finsupp.linearCombination ℂ v c) ∈ V.topologicalClosure
    simp only [Finsupp.linearCombination_apply, map_finsuppSum, map_smul]
    apply Submodule.finsuppSum_mem
    intro i hi
    exact V.topologicalClosure.smul_mem (c i) (Submodule.le_topologicalClosure _ (h i))
  exact Submodule.topologicalClosure_minimal _ hV
    ((Submodule.isClosed_topologicalClosure V).preimage T.continuous)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_DerivationExtensionFactor
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Factoriality in Sakai's one-implementer extension

In an irreducible representation of the algebra generated by the source
and its self-adjoint spatial implementer, every central projection of the
source bicommutant commutes with all generators. It is therefore trivial.
-/

namespace KadisonKastler

noncomputable section

variable {A B H : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance derivationExtensionFactorInstance1_ra8bd29_1 : PartialOrder B := CStarAlgebra.spectralOrder B
local instance derivationExtensionFactorInstance2_ra8bd29_1 : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
/-- The norm-closed unital star algebra generated by the source and one element. -/
def NormGeneratedExtension (φ : A →⋆ₐ[ℂ] B) (d : B) : Prop :=
  ∀ C : StarSubalgebra ℂ B, IsClosed (C : Set B) →
    (∀ a, φ a ∈ C) → d ∈ C → C = ⊤

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ExponentialCommutator
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Exponentiating a bounded inner derivation -/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- The bounded commutator operator on a normed algebra. -/
def boundedCommutator (x : A) : A →L[ℂ] A :=
  ContinuousLinearMap.mul ℂ A x - (ContinuousLinearMap.mul ℂ A).flip x

omit [CompleteSpace A] in
@[simp] theorem boundedCommutator_apply (x y : A) :
    boundedCommutator x y = x * y - y * x := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FieldCoordinateCenters
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Central coordinate projections from the two actual field actions -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {X K : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
  [∀ n, NormedAddCommGroup (K n)] [∀ n, InnerProductSpace ℂ (K n)]
  [∀ n, CompleteSpace (K n)] (μ : ∀ n, Measure (X n))

local notation "L" => fun n => Lp (K n) 2 (μ n)

def HasHilbertSumFields (A : VonNeumannAlgebra (lp L 2)) : Prop :=
  ∀ T ∈ A, ∃ F : ∀ n, X n → K n →L[ℂ] K n,
    ∀ (f : lp L 2) n, T f n =ᵐ[μ n] fun x => F n x (f n x)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FourierL1Uniqueness
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Fourier uniqueness for integrable vector functions

The distribution embedding is injective. Fubini identifies its Fourier
transform with the ordinary integral Fourier transform, so a vanishing
integral transform forces the original function to vanish almost everywhere.
-/

namespace KadisonKastler

open MeasureTheory SchwartzMap FourierTransform

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]

theorem ae_zero_of_integrable_fourier_zero {f : ℝ → H} (hf : Integrable f)
    (hz : ∀ t : ℝ, 𝓕 f t = 0) : f =ᵐ[volume] 0 := by
  let hm : MemLp f 1 := memLp_one_iff_integrable.mpr hf
  let F : Lp H 1 (volume : Measure ℝ) := hm.toLp f
  have hF : 𝓕 (Lp.toTemperedDistribution F) = 0 := by
    ext g
    rw [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply]
    calc
      (∫ s, (𝓕 g) s • F s) = ∫ s, (𝓕 g) s • f s := by
        apply integral_congr_ae
        filter_upwards [hm.coeFn_toLp] with s hs
        rw [show F s = f s from hs]
      _ = ∫ s, g s • 𝓕 f s := by
        simpa only [SchwartzMap.fourier_coe, Real.fourier_eq,
          VectorFourier.fourierIntegral, LinearMap.flip_apply, innerₗ_apply_apply,
          real_inner_comm] using!
          (VectorFourier.integral_fourierIntegral_smul_eq_flip
            (μ := volume) (ν := volume) (L := innerₗ ℝ)
            Real.continuous_fourierChar (by fun_prop) g.integrable hf)
      _ = 0 := by simp [hz]
  have hdist : Lp.toTemperedDistribution F = 0 := by
    have h := congrArg (fun d : 𝓢'(ℝ, H) => 𝓕⁻ d) hF
    simpa using h
  have hzero : F = 0 := by
    apply (LinearMap.ker_eq_bot.mp
      (Lp.ker_toTemperedDistributionCLM_eq_bot (F := H) (μ := volume) (p := 1)))
    change Lp.toTemperedDistribution F = Lp.toTemperedDistribution 0
    have hz0 : Lp.toTemperedDistribution (0 : Lp H 1 (volume : Measure ℝ)) = 0 :=
      (Lp.toTemperedDistributionCLM H volume 1).map_zero
    exact hdist.trans hz0.symm
  have hae : F =ᵐ[volume] 0 := (Lp.eq_zero_iff_ae_eq_zero).mp hzero
  filter_upwards [hae, hm.coeFn_toLp] with s hs hs'
  exact hs'.symm.trans hs

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FourierLaplace
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Fourier transform of the two-sided exponential

This scalar calculation is the first half of the Cauchy-kernel character
formula needed for Poisson demodulation. It uses the existing half-line
exponential integrals and no additional published-input hypothesis.
-/

namespace KadisonKastler

open MeasureTheory
open scoped FourierTransform

noncomputable section

/-- The integrable two-sided exponential, with complex values. -/
def laplaceKernel (a t : ℝ) : ℂ := Complex.exp (-((a : ℂ) * ((|t| : ℝ) : ℂ)))

def laplaceFourierIntegrand (a ξ t : ℝ) : ℂ :=
  Complex.exp ((↑(-2 * Real.pi * t * ξ) : ℂ) * Complex.I) * laplaceKernel a t

theorem laplaceFourierIntegrand_nonpos (a ξ t : ℝ) (ht : t ≤ 0) :
    laplaceFourierIntegrand a ξ t =
      Complex.exp (((a : ℂ) - (2 * Real.pi * ξ : ℝ) * Complex.I) * t) := by
  unfold laplaceFourierIntegrand laplaceKernel
  rw [abs_of_nonpos ht, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem laplaceFourierIntegrand_nonneg (a ξ t : ℝ) (ht : 0 ≤ t) :
    laplaceFourierIntegrand a ξ t =
      Complex.exp ((-(a : ℂ) - (2 * Real.pi * ξ : ℝ) * Complex.I) * t) := by
  unfold laplaceFourierIntegrand laplaceKernel
  rw [abs_of_nonneg ht, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem laplaceFourierIntegrand_integrableOn_left {a : ℝ} (ha : 0 < a) (ξ : ℝ) :
    IntegrableOn (laplaceFourierIntegrand a ξ) (Set.Iic 0) := by
  have hpos : 0 < ((a : ℂ) - (2 * Real.pi * ξ : ℝ) * Complex.I).re := by
    simpa using ha
  apply (integrableOn_exp_mul_complex_Iic hpos 0).congr_fun
  · intro t ht
    exact (laplaceFourierIntegrand_nonpos a ξ t ht).symm
  · exact measurableSet_Iic

theorem laplaceFourierIntegrand_integrableOn_right {a : ℝ} (ha : 0 < a) (ξ : ℝ) :
    IntegrableOn (laplaceFourierIntegrand a ξ) (Set.Ioi 0) := by
  have hneg : (-(a : ℂ) - (2 * Real.pi * ξ : ℝ) * Complex.I).re < 0 := by
    simpa using (neg_lt_zero.mpr ha)
  apply (integrableOn_exp_mul_complex_Ioi hneg 0).congr_fun
  · intro t ht
    exact (laplaceFourierIntegrand_nonneg a ξ t ht.le).symm
  · exact measurableSet_Ioi

end

/-- Integrability of the two-sided exponential, obtained from the same
half-line estimates used in its transform calculation. -/
theorem integrable_laplaceKernel {a : ℝ} (ha : 0 < a) : Integrable (laplaceKernel a) := by
  have hl := laplaceFourierIntegrand_integrableOn_left ha 0
  have hr := laplaceFourierIntegrand_integrableOn_right ha 0
  have h := hl.union hr
  have he : laplaceFourierIntegrand a 0 = laplaceKernel a := by
    funext t
    simp [laplaceFourierIntegrand]
  rw [he] at h
  simpa only [Set.Iic_union_Ioi, integrableOn_univ] using h

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_GeometricCorrectionScale
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The summable error scale for multiplication correction -/

namespace KadisonKastler

open Filter Topology

noncomputable section

def correctionScale (q : ℝ) (n : ℕ) : ℝ := q * (1 / 2 : ℝ) ^ n

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_HaagerupCochains
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Matrix Hochschild identities for multiplication correction

The row-column estimates below retain all matrix levels. Associativity turns
the differential of a multiplication defect into a quadratic expression.
-/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A]

@[simp] theorem bilinearProduct_add (f g : A →ₗ[ℂ] A →ₗ[ℂ] A) {p r q : ℕ}
    (X : CStarMatrix (Fin p) (Fin r) A) (Y : CStarMatrix (Fin r) (Fin q) A) :
    bilinearProduct (f + g) X Y = bilinearProduct f X Y + bilinearProduct g X Y := by
  ext i j
  simp only [bilinearProduct_apply, LinearMap.add_apply, Finset.sum_add_distrib, CStarMatrix.add_apply]

@[simp] theorem bilinearProduct_sub (f g : A →ₗ[ℂ] A →ₗ[ℂ] A) {p r q : ℕ}
    (X : CStarMatrix (Fin p) (Fin r) A) (Y : CStarMatrix (Fin r) (Fin q) A) :
    bilinearProduct (f - g) X Y = bilinearProduct f X Y - bilinearProduct g X Y := by
  ext i j
  simp only [bilinearProduct_apply, LinearMap.sub_apply, Finset.sum_sub_distrib, CStarMatrix.sub_apply]

@[simp] theorem bilinearProduct_add_left (f : A →ₗ[ℂ] A →ₗ[ℂ] A) {p r q : ℕ}
    (X X' : CStarMatrix (Fin p) (Fin r) A) (Y : CStarMatrix (Fin r) (Fin q) A) :
    bilinearProduct f (X + X') Y = bilinearProduct f X Y + bilinearProduct f X' Y := by
  ext i j
  simp [map_add, Finset.sum_add_distrib]

@[simp] theorem bilinearProduct_add_right (f : A →ₗ[ℂ] A →ₗ[ℂ] A) {p r q : ℕ}
    (X : CStarMatrix (Fin p) (Fin r) A) (Y Y' : CStarMatrix (Fin r) (Fin q) A) :
    bilinearProduct f X (Y + Y') = bilinearProduct f X Y + bilinearProduct f X Y' := by
  ext i j
  simp [map_add, Finset.sum_add_distrib]

@[simp] theorem bilinearProduct_smul (z : ℂ) (f : A →ₗ[ℂ] A →ₗ[ℂ] A) {p r q : ℕ}
    (X : CStarMatrix (Fin p) (Fin r) A) (Y : CStarMatrix (Fin r) (Fin q) A) :
    bilinearProduct (z • f) X Y = z • bilinearProduct f X Y := by
  ext i j
  change (∑ k, z • f (X i k) (Y k j)) = z • ∑ k, f (X i k) (Y k j)
  rw [Finset.smul_sum]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_HorizontalStripGluing
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Holomorphic gluing across one horizontal line

This is the local analytic bridge for extending a bounded KMS strip
whose two boundary values agree. Rectangular integrals split along the
line; Morera's theorem then gives holomorphicity across it.
-/

namespace KadisonKastler

open Complex Set MeasureTheory
open scoped Interval

noncomputable section

theorem horizontal_rectangle_mem {a b : ℝ} {z w p : ℂ}
    (hz : a < z.im ∧ z.im < b) (hw : a < w.im ∧ w.im < b)
    (hp : p ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]]) :
    a < p.im ∧ p.im < b := by
  exact ⟨(lt_min hz.1 hw.1).trans_le hp.2.1,
    hp.2.2.trans_lt (max_lt hz.2 hw.2)⟩

/-- Continuity and holomorphicity on both sides suffice across a horizontal seam. -/
theorem differentiableOn_horizontal_strip_glue
    {f : ℂ → ℂ} {a b s : ℝ} (has : a < s) (hsb : s < b)
    (hc : ContinuousOn f {z | a < z.im ∧ z.im < b})
    (hd : ∀ z, a < z.im → z.im < b → z.im ≠ s → DifferentiableAt ℂ f z) :
    DifferentiableOn ℂ f {z | a < z.im ∧ z.im < b} := by
  have hopen : IsOpen {z : ℂ | a < z.im ∧ z.im < b} :=
    (isOpen_Ioo.preimage continuous_im)
  apply (Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn hopen).mp
  refine ⟨?_, hc⟩
  intro z w hzw
  have hz : a < z.im ∧ z.im < b := hzw ⟨left_mem_uIcc, left_mem_uIcc⟩
  have hw : a < w.im ∧ w.im < b := hzw ⟨right_mem_uIcc, right_mem_uIcc⟩
  have hrect (v q : ℂ) (hv : a < v.im ∧ v.im < b)
      (hq : a < q.im ∧ q.im < b) (hseam : v.im = s ∨ q.im = s) :
      (∫ x : ℝ in v.re..q.re, f (x + v.im * I)) -
        (∫ x : ℝ in v.re..q.re, f (x + q.im * I)) +
        I * (∫ y : ℝ in v.im..q.im, f (q.re + y * I)) -
        I * (∫ y : ℝ in v.im..q.im, f (v.re + y * I)) = 0 := by
    apply integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn f v q
      (hc.mono fun p hp => horizontal_rectangle_mem hv hq hp)
    intro p hp
    have hp' : a < p.im ∧ p.im < b :=
      ⟨(lt_min hv.1 hq.1).trans hp.2.1,
        hp.2.2.trans (max_lt hv.2 hq.2)⟩
    apply (hd p hp'.1 hp'.2 ?_).differentiableWithinAt
    intro hps
    rcases hseam with hvs | hqs
    · have hlo := hp.2.1
      have hhi := hp.2.2
      simp only [hps, hvs, min_lt_iff, lt_max_iff, lt_self_iff_false,
        false_or] at hlo hhi
      exact (lt_asymm hlo hhi)
    · have hlo := hp.2.1
      have hhi := hp.2.2
      simp only [hps, hqs, min_lt_iff, lt_max_iff, lt_self_iff_false,
        or_false] at hlo hhi
      exact (lt_asymm hlo hhi)
  have hint (r c d : ℝ) (hc' : a < c ∧ c < b) (hd' : a < d ∧ d < b) :
      IntervalIntegrable (fun y : ℝ => f (r + y * I)) volume c d := by
    apply ContinuousOn.intervalIntegrable
    apply hc.comp (by fun_prop)
    intro y hy
    change a < (r + y * I : ℂ).im ∧ (r + y * I : ℂ).im < b
    simpa only [add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re,
      mul_one, mul_zero, add_zero, zero_add] using
      And.intro ((lt_min hc'.1 hd'.1).trans_le hy.1)
        (hy.2.trans_lt (max_lt hc'.2 hd'.2))
  have h₁ := hrect z (w.re + s * I) hz (by simpa using And.intro has hsb)
    (Or.inr (by simp))
  have h₂ := hrect (z.re + s * I) w (by simpa using And.intro has hsb) hw
    (Or.inl (by simp))
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
    mul_zero, sub_zero, add_zero, add_im, mul_im, mul_one, zero_add] at h₁ h₂
  rw [← add_eq_zero_iff_eq_neg, Complex.wedgeIntegral_add_wedgeIntegral_eq]
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint w.re z.im s hz ⟨has, hsb⟩)
      (hint w.re s w.im ⟨has, hsb⟩ hw),
    ← intervalIntegral.integral_add_adjacent_intervals (hint z.re z.im s hz ⟨has, hsb⟩)
      (hint z.re s w.im ⟨has, hsb⟩ hw)]
  simp only [smul_eq_mul, mul_add]
  linear_combination h₁ + h₂

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PeriodicStripExtension
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A bounded holomorphic strip with matching boundary values is constant

The matching edges give a periodic extension. The preceding rectangular
Morera argument removes the seams, and Liouville applies to the extension.
-/

namespace KadisonKastler

open Complex Set
open scoped Topology

noncomputable section

def periodicStripExtension (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  f (z - (⌊z.im⌋ : ℂ) * I)

theorem periodicStripExtension_eq {f : ℂ → ℂ}
    (he : ∀ t : ℝ, f ((t : ℂ) + I) = f t)
    (k : ℤ) {z : ℂ} (hz : (k : ℝ) ≤ z.im ∧ z.im ≤ (k : ℝ) + 1) :
    periodicStripExtension f z = f (z - (k : ℂ) * I) := by
  by_cases hlt : z.im < (k : ℝ) + 1
  · rw [periodicStripExtension, Int.floor_eq_iff.mpr ⟨hz.1, hlt⟩]
  · have hi : z.im = ((k + 1 : ℤ) : ℝ) := by push_cast <;> linarith [hz.2]
    have hfloor : ⌊z.im⌋ = k + 1 := by rw [hi, Int.floor_intCast]
    have h₁ : z - ((k + 1 : ℤ) : ℂ) * I = (z.re : ℂ) := by
      apply Complex.ext <;> simp [hi]
    have h₂ : z - (k : ℂ) * I = (z.re : ℂ) + I := by
      apply Complex.ext <;> simp [hi]
    rw [periodicStripExtension, hfloor, h₁, h₂, he]

theorem periodicStripExtension_continuousOn_cell {f : ℂ → ℂ}
    (he : ∀ t : ℝ, f ((t : ℂ) + I) = f t)
    (hc : ContinuousOn f {z | 0 ≤ z.im ∧ z.im ≤ 1}) (k : ℤ) :
    ContinuousOn (periodicStripExtension f)
      {z | (k : ℝ) ≤ z.im ∧ z.im ≤ (k : ℝ) + 1} := by
  have hmap : MapsTo (fun z : ℂ => z - (k : ℂ) * I)
      {z | (k : ℝ) ≤ z.im ∧ z.im ≤ (k : ℝ) + 1}
      {z | 0 ≤ z.im ∧ z.im ≤ 1} := by
    intro z hz
    change 0 ≤ (z - (k : ℂ) * I).im ∧ (z - (k : ℂ) * I).im ≤ 1
    simp only [sub_im, mul_im, intCast_re, I_im, intCast_im, I_re,
      mul_one, mul_zero, add_zero]
    constructor <;> linarith [hz.1, hz.2]
  exact (hc.comp (by fun_prop) hmap).congr
    (fun z hz => periodicStripExtension_eq he k hz)

theorem periodicStripExtension_continuous {f : ℂ → ℂ}
    (he : ∀ t : ℝ, f ((t : ℂ) + I) = f t)
    (hc : ContinuousOn f {z | 0 ≤ z.im ∧ z.im ≤ 1}) :
    Continuous (periodicStripExtension f) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  let k : ℤ := ⌊z.im⌋
  have hlo : (k : ℝ) ≤ z.im := Int.floor_le _
  have hhi : z.im < (k : ℝ) + 1 := Int.lt_floor_add_one _
  have hclosed (j : ℤ) : IsClosed {w : ℂ | (j : ℝ) ≤ w.im ∧ w.im ≤ (j : ℝ) + 1} :=
    isClosed_Icc.preimage continuous_im
  have hu := (periodicStripExtension_continuousOn_cell he hc (k - 1)).union_of_isClosed
    (periodicStripExtension_continuousOn_cell he hc k) (hclosed _) (hclosed _)
  apply hu.continuousAt
  apply Filter.mem_of_superset
    ((isOpen_Ioo.preimage continuous_im).mem_nhds
      (show (k : ℝ) - 1 < z.im ∧ z.im < (k : ℝ) + 1 by constructor <;> linarith))
  intro w hw
  by_cases hwk : w.im ≤ (k : ℝ)
  · left
    change ((k - 1 : ℤ) : ℝ) ≤ w.im ∧ w.im ≤ ((k - 1 : ℤ) : ℝ) + 1
    push_cast
    constructor <;> linarith [hw.1]
  · right
    exact ⟨by linarith, hw.2.le⟩

theorem periodicStripExtension_differentiableAt_cell {f : ℂ → ℂ}
    (he : ∀ t : ℝ, f ((t : ℂ) + I) = f t)
    (hd : DifferentiableOn ℂ f {z | 0 < z.im ∧ z.im < 1})
    (k : ℤ) {z : ℂ} (hz : (k : ℝ) < z.im ∧ z.im < (k : ℝ) + 1) :
    DifferentiableAt ℂ (periodicStripExtension f) z := by
  have hm : 0 < (z - (k : ℂ) * I).im ∧ (z - (k : ℂ) * I).im < 1 := by
    simp only [sub_im, mul_im, intCast_re, I_im, intCast_im, I_re,
      mul_one, mul_zero, add_zero]
    constructor <;> linarith [hz.1, hz.2]
  have hf := (hd.differentiableAt ((isOpen_Ioo.preimage continuous_im).mem_nhds hm)).comp z
    (show DifferentiableAt ℂ (fun w : ℂ => w - (k : ℂ) * I) z by fun_prop)
  apply hf.congr_of_eventuallyEq
  filter_upwards [(isOpen_Ioo.preimage continuous_im).mem_nhds hz] with w hw
  exact periodicStripExtension_eq he k ⟨hw.1.le, hw.2.le⟩

theorem periodicStripExtension_differentiable {f : ℂ → ℂ}
    (he : ∀ t : ℝ, f ((t : ℂ) + I) = f t)
    (hc : ContinuousOn f {z | 0 ≤ z.im ∧ z.im ≤ 1})
    (hd : DifferentiableOn ℂ f {z | 0 < z.im ∧ z.im < 1}) :
    Differentiable ℂ (periodicStripExtension f) := by
  intro z
  let k : ℤ := ⌊z.im⌋
  have hlo : (k : ℝ) ≤ z.im := Int.floor_le _
  have hhi : z.im < (k : ℝ) + 1 := Int.lt_floor_add_one _
  by_cases hlt : (k : ℝ) < z.im
  · exact periodicStripExtension_differentiableAt_cell he hd k ⟨hlt, hhi⟩
  · have heq : z.im = (k : ℝ) := le_antisymm (le_of_not_gt hlt) hlo
    have hg := differentiableOn_horizontal_strip_glue
      (f := periodicStripExtension f) (a := (k : ℝ) - 1) (b := (k : ℝ) + 1)
      (s := (k : ℝ)) (by linarith) (by linarith)
      (periodicStripExtension_continuous he hc).continuousOn ?_
    · exact hg.differentiableAt
        ((isOpen_Ioo.preimage continuous_im).mem_nhds (by simp [heq]))
    · intro w hw₁ hw₂ hne
      by_cases hlow : w.im < (k : ℝ)
      · apply periodicStripExtension_differentiableAt_cell he hd (k - 1)
        push_cast
        exact ⟨hw₁, by linarith⟩
      · exact periodicStripExtension_differentiableAt_cell he hd k
          ⟨lt_of_le_of_ne (le_of_not_gt hlow) (Ne.symm hne), hw₂⟩

/-- The exact scalar uniqueness statement needed after normalizing a KMS strip. -/
theorem bounded_matching_strip_constant {f : ℂ → ℂ}
    (he : ∀ t : ℝ, f ((t : ℂ) + I) = f t)
    (hc : ContinuousOn f {z | 0 ≤ z.im ∧ z.im ≤ 1})
    (hd : DifferentiableOn ℂ f {z | 0 < z.im ∧ z.im < 1})
    (hb : ∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.im → z.im ≤ 1 → ‖f z‖ ≤ C) :
    ∀ z : ℂ, 0 ≤ z.im → z.im ≤ 1 → f z = f 0 := by
  obtain ⟨C, hC⟩ := hb
  have hbound : Bornology.IsBounded (Set.range (periodicStripExtension f)) := by
    apply (isBounded_iff_forall_norm_le).mpr
    refine ⟨C, ?_⟩
    rintro _ ⟨z, rfl⟩
    apply hC
    · simpa only [sub_im, mul_im, intCast_re, I_im, intCast_im, I_re,
        mul_one, mul_zero, add_zero] using sub_nonneg.mpr (Int.floor_le z.im)
    · simp only [sub_im, mul_im, intCast_re, I_im, intCast_im, I_re,
        mul_one, mul_zero, add_zero]
      linarith [Int.lt_floor_add_one z.im]
  intro z hz₁ hz₂
  have h := (periodicStripExtension_differentiable he hc hd).apply_eq_apply_of_bounded hbound z 0
  have hz' : periodicStripExtension f z = f z := by
    simpa using periodicStripExtension_eq (f := f) he (0 : ℤ) (z := z)
      (by simpa using And.intro hz₁ hz₂)
  rw [hz'] at h
  simpa [periodicStripExtension] using h

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_KMSScalarStrip
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The exponential determined by a scalar KMS balance equation -/

namespace KadisonKastler

open Complex

noncomputable section

/-- A positive modular frequency is uniquely determined by the ratio
of the boundary values of its bounded KMS strip. -/
theorem kms_strip_exponential {f : ℂ → ℂ} {L : ℝ} (hL : 0 ≤ L)
    (hc : ContinuousOn f {z | 0 ≤ z.im ∧ z.im ≤ 1})
    (hd : DifferentiableOn ℂ f {z | 0 < z.im ∧ z.im < 1})
    (hb : ∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.im → z.im ≤ 1 → ‖f z‖ ≤ C)
    (he : ∀ t : ℝ, f ((t : ℂ) + I) = (Real.exp (-L) : ℂ) * f t) :
    ∀ t : ℝ, f t = Complex.exp (I * (L : ℂ) * t) * f 0 := by
  let g : ℂ → ℂ := fun z => Complex.exp (-I * (L : ℂ) * z) * f z
  have hge (t : ℝ) : g ((t : ℂ) + I) = g t := by
    dsimp [g]
    rw [he, ← mul_assoc, Complex.ofReal_exp, ← Complex.exp_add]
    congr 2
    push_cast
    calc
      -I * (L : ℂ) * ((t : ℂ) + I) + -(L : ℂ) =
        -I * (L : ℂ) * t - (L : ℂ) * I ^ 2 - L := by ring
      _ = -I * (L : ℂ) * t := by rw [I_sq]; ring
  have hgc : ContinuousOn g {z | 0 ≤ z.im ∧ z.im ≤ 1} :=
    (by fun_prop : Continuous (fun z : ℂ => Complex.exp (-I * (L : ℂ) * z))).continuousOn.mul hc
  have hgd : DifferentiableOn ℂ g {z | 0 < z.im ∧ z.im < 1} :=
    (by fun_prop : Differentiable ℂ (fun z : ℂ => Complex.exp (-I * (L : ℂ) * z))).differentiableOn.mul hd
  obtain ⟨C, hC⟩ := hb
  have hgb : ∃ B : ℝ, ∀ z : ℂ, 0 ≤ z.im → z.im ≤ 1 → ‖g z‖ ≤ B := by
    refine ⟨Real.exp L * C, ?_⟩
    intro z hz₁ hz₂
    have hre : (-I * (L : ℂ) * z).re = L * z.im := by simp
    calc
      ‖g z‖ = Real.exp (L * z.im) * ‖f z‖ := by
        simp only [g, norm_mul, Complex.norm_exp, hre]
      _ ≤ Real.exp L * C := mul_le_mul
        (Real.exp_le_exp.mpr (mul_le_of_le_one_right hL hz₂)) (hC z hz₁ hz₂)
        (norm_nonneg _) (Real.exp_pos _).le
  intro t
  have hg := bounded_matching_strip_constant hge hgc hgd hgb (t : ℂ) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hinv : Complex.exp (I * (L : ℂ) * t) * Complex.exp (-I * (L : ℂ) * t) = 1 := by
    rw [← Complex.exp_add]
    rw [show I * (L : ℂ) * t + -I * (L : ℂ) * t = 0 by ring, Complex.exp_zero]
  have h := congrArg (fun w : ℂ => Complex.exp (I * (L : ℂ) * t) * w) hg
  simpa only [g, ← mul_assoc, hinv, one_mul, mul_zero, Complex.exp_zero, mul_one] using h

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_L2LinearFields
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Lifting fields of maps between different Hilbert spaces to L²

This supplies the varying synthesis maps used on a fixed dimension stratum.
Measurability is required only after evaluation on a vector.
-/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

variable {X E F : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  (μ : Measure X)

theorem aestronglyMeasurable_linearField_apply (T : X → E →L[ℂ] F)
    (hT : ∀ v, AEStronglyMeasurable (fun x => T x v) μ)
    (v : X → E) (hv : AEStronglyMeasurable v μ) :
    AEStronglyMeasurable (fun x => T x (v x)) μ := by
  have haux (w : X → E) (hw : StronglyMeasurable w) :
      AEStronglyMeasurable (fun x => T x (w x)) μ := by
    induction w, hw using StronglyMeasurable.induction with
    | @ind v s hs =>
      convert (hT v).indicator hs using 1
      all_goals try with_reducible_and_instances rfl
      funext x
      by_cases hx : x ∈ s <;> simp [hx]
    | add hf hg hfg hdisj ihf ihg =>
      convert ihf.add ihg using 1
      all_goals try with_reducible_and_instances rfl
      funext x
      simp only [Pi.add_apply, map_add]
    | lim hf hg ih hlim =>
      exact aestronglyMeasurable_of_tendsto_ae atTop ih
        (Eventually.of_forall fun x => (T x).continuous.tendsto _ |>.comp (hlim x))
  exact (haux (hv.mk v) hv.stronglyMeasurable_mk).congr
    (hv.ae_eq_mk.symm.mono fun x hx => congrArg (T x) hx)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_L2MeasurableExtension
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

include hs in
theorem ae_of_subtype_of_outside {p : X → Prop}
    (hin : ∀ᵐ x : s ∂Measure.comap ((↑) : s → X) μ, p x.val)
    (hout : ∀ x, x ∉ s → p x) : ∀ᵐ x ∂μ, p x := by
  have hi := (ae_restrict_iff' hs).mp ((ae_restrict_iff_subtype hs).mpr hin)
  filter_upwards [hi] with x hx
  by_cases hxs : x ∈ s
  · exact hx hxs
  · exact hout x hxs

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_L2PartitionCoordinates
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Evaluation of the coordinates associated with a measurable partition -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (μ : Measure X)

variable [CompleteSpace H] (s : ℕ → Set X) (hs : ∀ n, MeasurableSet (s n))
  (hd : Pairwise (fun i j => Disjoint (s i) (s j))) (hcover : ⋃ n, s n = Set.univ)

omit [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] in
include hs hcover in
theorem ae_iff_forall_partition (p : X → Prop) :
    (∀ᵐ x ∂μ, p x) ↔ ∀ n, ∀ᵐ x : s n ∂Measure.comap ((↑) : s n → X) μ, p x.val := by
  constructor
  · intro hp n
    exact (ae_restrict_iff_subtype (hs n)).mp (ae_restrict_of_ae hp)
  · intro hp
    have hn (n : ℕ) : ∀ᵐ x ∂μ, x ∈ s n → p x :=
      (ae_restrict_iff' (hs n)).mp ((ae_restrict_iff_subtype (hs n)).mpr (hp n))
    filter_upwards [eventually_countable_forall.mpr hn] with x hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (hcover.symm ▸ Set.mem_univ x)
    exact hx n hn

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_LocalLaplaceUniqueness
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Uniqueness from Laplace values on an interval about zero

This specialization is used for the finite positive measures formed from the
positive and negative parts of a modular averaging coefficient.
-/

namespace KadisonKastler

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

noncomputable section

theorem finiteMeasure_eq_of_local_laplace {μ ν : Measure ℝ}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {a : ℝ} (ha : 0 < a)
    (hμ : ∀ t ∈ Ioo (-a) a, Integrable (fun x : ℝ => Real.exp (t * x)) μ)
    (hν : ∀ t ∈ Ioo (-a) a, Integrable (fun x : ℝ => Real.exp (t * x)) ν)
    (heq : ∀ t ∈ Ioo (-a) a, mgf id μ t = mgf id ν t) : μ = ν := by
  let S : Set ℂ := {z | z.re ∈ Ioo (-a) a}
  have hμ' : Ioo (-a) a ⊆ interior (integrableExpSet id μ) := by
    apply interior_maximal hμ isOpen_Ioo
  have hν' : Ioo (-a) a ⊆ interior (integrableExpSet id ν) := by
    apply interior_maximal hν isOpen_Ioo
  have hf : AnalyticOnNhd ℂ (complexMGF id μ) S :=
    analyticOnNhd_complexMGF.mono (fun z hz => hμ' hz)
  have hg : AnalyticOnNhd ℂ (complexMGF id ν) S :=
    analyticOnNhd_complexMGF.mono (fun z hz => hν' hz)
  have hS : IsPreconnected S := (convex_Ioo (-a) a).linear_preimage Complex.reLm |>.isPreconnected
  have h0 : (0 : ℂ) ∈ S := by change -a < 0 ∧ 0 < a; constructor <;> linarith
  have hreal : ∃ᶠ t : ℝ in 𝓝[≠] 0, complexMGF id μ t = complexMGF id ν t := by
    have hi : Ioo (-a) a ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by linarith) ha
    have he : ∀ᶠ t : ℝ in 𝓝[≠] 0, t ∈ Ioo (-a) a :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds hi
    exact (he.mono fun t ht => by rw [complexMGF_ofReal, complexMGF_ofReal, heq t ht]).frequently
  have hfreq : ∃ᶠ z : ℂ in 𝓝[≠] 0, complexMGF id μ z = complexMGF id ν z := by
    rw [frequently_iff_seq_forall] at hreal ⊢
    obtain ⟨xs, hx, he⟩ := hreal
    refine ⟨fun n => (xs n : ℂ), ?_, fun n => he n⟩
    rw [tendsto_nhdsWithin_iff] at hx ⊢
    constructor
    · simpa only [Function.comp_def, Complex.ofReal_zero] using
        (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp hx.1
    · simpa using hx.2
  have he := hf.eqOn_of_preconnected_of_frequently_eq hg hS h0 hfreq
  apply Measure.ext_of_charFun
  ext t
  rw [← complexMGF_id_mul_I, ← complexMGF_id_mul_I]
  exact he (by simpa [S] using h0)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TomitaCentralizerGraph
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Centralizer vectors in the closed Tomita graph -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

theorem vectorState_star (Ω : H) (T : H →L[ℂ] H) :
    star (inner ℂ Ω (T Ω)) = inner ℂ Ω (star T Ω) := by
  change (starRingEnd ℂ) (inner ℂ Ω (T Ω)) = _
  rw [inner_conj_symm, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularizedModularGroup
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.PopaCorner.instOne _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Bounded logarithmic approximations to the modular group

The logarithmic generator of the graph resolvent is regularized at both
endpoints. Each approximation is an actual norm-continuous unitary group.
The strong limit and its modular properties are subsequent constructions.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Real scaling written through the complex scalar action. -/
def scaleSelfAdjoint (a : selfAdjoint (H →L[ℂ] H)) (t : ℝ) : selfAdjoint (H →L[ℂ] H) :=
  ⟨(t : ℂ) • a.val, by
    change star ((t : ℂ) • a.val) = (t : ℂ) • a.val
    rw [star_smul, a.property.star_eq]
    simp⟩

theorem scaleSelfAdjoint_add (a : selfAdjoint (H →L[ℂ] H)) (s t : ℝ) :
    scaleSelfAdjoint a (s + t) = scaleSelfAdjoint a s + scaleSelfAdjoint a t := by
  apply Subtype.ext
  change ((s + t : ℝ) : ℂ) • a.val = (s : ℂ) • a.val + (t : ℂ) • a.val
  rw [Complex.ofReal_add, add_smul]

/-- Exponentiation of a bounded self-adjoint generator. -/
def boundedSelfAdjointGroup (a : selfAdjoint (H →L[ℂ] H)) :
    Multiplicative ℝ →* unitary (H →L[ℂ] H) where
  toFun t := selfAdjoint.expUnitary (scaleSelfAdjoint a (Multiplicative.toAdd t))
  map_one' := by
    change selfAdjoint.expUnitary (scaleSelfAdjoint a 0) = 1
    have hzero : scaleSelfAdjoint a 0 = 0 := by apply Subtype.ext; simp [scaleSelfAdjoint]
    rw [hzero, selfAdjoint.expUnitary_zero]
  map_mul' s t := by
    change selfAdjoint.expUnitary (scaleSelfAdjoint a
      (Multiplicative.toAdd s + Multiplicative.toAdd t)) = _
    rw [scaleSelfAdjoint_add]
    apply Commute.expUnitary_add
    exact ((Commute.refl a.val).smul_left ((Multiplicative.toAdd s : ℝ) : ℂ)).smul_right
      ((Multiplicative.toAdd t : ℝ) : ℂ)

theorem boundedSelfAdjointGroup_continuous (a : selfAdjoint (H →L[ℂ] H)) :
    Continuous (fun t : ℝ => boundedSelfAdjointGroup a (Multiplicative.ofAdd t)) := by
  have hscale : Continuous (scaleSelfAdjoint a) :=
    (Complex.continuous_ofReal.smul continuous_const).subtype_mk _
  exact selfAdjoint.continuous_expUnitary.comp hscale

theorem boundedSelfAdjointGroup_stronglyContinuous (a : selfAdjoint (H →L[ℂ] H)) (x : H) :
    Continuous (fun t : ℝ =>
      (boundedSelfAdjointGroup a (Multiplicative.ofAdd t) : H →L[ℂ] H) x) :=
  (continuous_subtype_val.comp (boundedSelfAdjointGroup_continuous a)).clm_apply continuous_const

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ResolventVectorMeasure
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Scalar vector measures of the bounded Tomita resolvent

The real continuous functional calculus, tested on one Hilbert vector,
is a positive functional. Riesz representation supplies the finite measure
needed to compare the modular phases and their spectral cuts.
-/

namespace KadisonKastler

open MeasureTheory
open scoped CompactlySupported

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def resolventVectorFunctional (R : H →L[ℂ] H) (hR : IsSelfAdjoint R) (x : H) :
    C_c(spectrum ℝ R, ℝ) →ₚ[ℝ] ℝ where
  toFun f := (inner ℂ x ((cfcHom hR f.toContinuousMap) x)).re
  map_add' f g := by
    change (inner ℂ x ((cfcHom hR (f.toContinuousMap + g.toContinuousMap)) x)).re = _
    rw [map_add, add_apply, inner_add_right, Complex.add_re]
  map_smul' a f := by
    change (inner ℂ x ((cfcHom hR (a • f.toContinuousMap)) x)).re = _
    rw [map_smul, smul_apply]
    simp only [← Complex.coe_smul, inner_smul_right, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, smul_eq_mul, RingHom.id_apply]
  monotone' f g hfg := by
    have hfgn : f.toContinuousMap ≤ g.toContinuousMap := hfg
    have hp : 0 ≤ cfcHom hR (g.toContinuousMap - f.toContinuousMap) :=
      map_nonneg (cfcHom hR) (sub_nonneg.mpr hfgn)
    have hi := ((ContinuousLinearMap.nonneg_iff_isPositive _).mp hp).re_inner_nonneg_right x
    rw [map_sub, sub_apply, inner_sub_right] at hi
    change 0 ≤ (inner ℂ x (((cfcHom hR) g.toContinuousMap) x) -
      inner ℂ x (((cfcHom hR) f.toContinuousMap) x)).re at hi
    rw [Complex.sub_re] at hi
    exact sub_nonneg.mp hi

def resolventVectorMeasure (R : H →L[ℂ] H) (hR : IsSelfAdjoint R) (x : H) :
    Measure (spectrum ℝ R) := RealRMK.rieszMeasure (resolventVectorFunctional R hR x)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ResolventCyclicModel
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A cyclic spectral isometry for the bounded resolvent

Continuous spectral functions are dense in the scalar L2 space. Their
functional-calculus vectors have exactly the same norm, so the map
extends to an isometry into the original Hilbert space.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

abbrev ResolventCyclicL2 (R : H →L[ℂ] H) (hR : IsSelfAdjoint R) (x : H) :=
  Lp ℂ 2 (resolventVectorMeasure R hR x)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RealLaplaceUniqueness
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Local Laplace uniqueness for the signed averaging coefficient -/

namespace KadisonKastler

open MeasureTheory ProbabilityTheory Filter Set

noncomputable section

theorem exp_positivePart_integrable (f : ℝ → ℝ) (hf : Measurable f) (s : ℝ)
    (hi : Integrable (fun t => Real.exp (s * t) * f t)) :
    Integrable (fun t => Real.exp (s * t) * max (f t) 0) := by
  apply hi.norm.mono' (by fun_prop)
  exact Eventually.of_forall fun t => by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_mul,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (max_le (le_abs_self _) (abs_nonneg _))
      (Real.exp_pos _).le

theorem exp_density_integrable (f : ℝ → ℝ) (hf : Measurable f)
    (hf0 : ∀ t, 0 ≤ f t) (s : ℝ)
    (hi : Integrable (fun t => Real.exp (s * t) * f t)) :
    Integrable (fun t => Real.exp (s * t)) (volume.withDensity fun t => ENNReal.ofReal (f t)) := by
  apply (integrable_withDensity_iff_integrable_smul' hf.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mpr
  simpa only [ENNReal.toReal_ofReal (hf0 _), smul_eq_mul, mul_comm] using hi

theorem mgf_density (f : ℝ → ℝ) (hf : Measurable f)
    (hf0 : ∀ t, 0 ≤ f t) (s : ℝ) :
    mgf id (volume.withDensity fun t => ENNReal.ofReal (f t)) s =
      ∫ t, Real.exp (s * t) * f t := by
  rw [mgf, integral_withDensity_eq_integral_toReal_smul hf.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  exact Eventually.of_forall fun t => by simp only [ENNReal.toReal_ofReal (hf0 t),
    smul_eq_mul, id_eq, mul_comm]

/-- A real coefficient with an open interval of exponential integrability is
zero almost everywhere if all its Laplace values in that interval vanish. -/
theorem ae_zero_of_local_laplace (f : ℝ → ℝ) (hf : Measurable f)
    {a : ℝ} (ha : 0 < a)
    (hi : ∀ s ∈ Ioo (-a) a, Integrable (fun t => Real.exp (s * t) * f t))
    (hz : ∀ s ∈ Ioo (-a) a, (∫ t, Real.exp (s * t) * f t) = 0) :
    f =ᵐ[volume] 0 := by
  let p : ℝ → ℝ := fun t => max (f t) 0
  let q : ℝ → ℝ := fun t => max (-f t) 0
  have hp : Measurable p := hf.max measurable_const
  have hq : Measurable q := hf.neg.max measurable_const
  have hp0 (t) : 0 ≤ p t := le_max_right _ _
  have hq0 (t) : 0 ≤ q t := le_max_right _ _
  have hzero : (0 : ℝ) ∈ Ioo (-a) a := ⟨by linarith, ha⟩
  have hpi (s) (hs : s ∈ Ioo (-a) a) : Integrable (fun t => Real.exp (s * t) * p t) :=
    exp_positivePart_integrable f hf s (hi s hs)
  have hqi (s) (hs : s ∈ Ioo (-a) a) : Integrable (fun t => Real.exp (s * t) * q t) := by
    apply exp_positivePart_integrable (fun t => -f t) hf.neg s
    apply (hi s hs).neg.congr
    filter_upwards [] with t
    simp only [Pi.neg_apply, mul_neg]
  have hpI : Integrable p := by simpa only [zero_mul, Real.exp_zero, one_mul] using hpi 0 hzero
  have hqI : Integrable q := by simpa only [zero_mul, Real.exp_zero, one_mul] using hqi 0 hzero
  let μ := volume.withDensity (fun t => ENNReal.ofReal (p t))
  let ν := volume.withDensity (fun t => ENNReal.ofReal (q t))
  let : IsFiniteMeasure μ := isFiniteMeasure_withDensity
    ((lintegral_ofReal_ne_top_iff_integrable hp.aestronglyMeasurable
      (Eventually.of_forall hp0)).mpr hpI)
  let : IsFiniteMeasure ν := isFiniteMeasure_withDensity
    ((lintegral_ofReal_ne_top_iff_integrable hq.aestronglyMeasurable
      (Eventually.of_forall hq0)).mpr hqI)
  have hdiff (t) : f t = p t - q t := by
    dsimp [p, q]
    rcases le_total 0 (f t) with ht | ht
    · rw [max_eq_left ht, max_eq_right (neg_nonpos.mpr ht), sub_zero]
    · rw [max_eq_right ht, max_eq_left (neg_nonneg.mpr ht)]
      ring
  have hm : μ = ν := finiteMeasure_eq_of_local_laplace ha
    (fun s hs => exp_density_integrable p hp hp0 s (hpi s hs))
    (fun s hs => exp_density_integrable q hq hq0 s (hqi s hs)) (by
      intro s hs
      rw [mgf_density p hp hp0, mgf_density q hq hq0]
      have he := hz s hs
      have hf' : (fun t => Real.exp (s * t) * f t) =
          (fun t => Real.exp (s * t) * p t - Real.exp (s * t) * q t) := by
        funext t
        rw [hdiff, mul_sub]
      rw [hf', integral_sub (hpi s hs) (hqi s hs)] at he
      exact sub_eq_zero.mp he)
  have he := (withDensity_eq_iff_of_sigmaFinite hp.ennreal_ofReal.aemeasurable
    hq.ennreal_ofReal.aemeasurable).mp hm
  filter_upwards [he] with t ht
  have hpq : p t = q t := by
    have hh := congrArg ENNReal.toReal ht
    simpa only [ENNReal.toReal_ofReal (hp0 t), ENNReal.toReal_ofReal (hq0 t)] using hh
  simpa only [Pi.zero_apply, hpq, sub_self] using hdiff t

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_StripAverageKernel
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The decaying scalar kernel for modular strip averaging -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

def stripAverageKernel (a : ℝ) (z : ℂ) (t : ℝ) : ℂ :=
  Complex.exp (-(z * (t : ℂ))) / (Real.exp (a * t) + Real.exp (-a * t) : ℝ)

theorem stripAverageKernel_continuous (a : ℝ) (z : ℂ) :
    Continuous (stripAverageKernel a z) := by
  unfold stripAverageKernel
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro t
  exact_mod_cast (add_pos (Real.exp_pos (a * t)) (Real.exp_pos (-a * t))).ne'

theorem stripAverageKernel_norm (a t : ℝ) (z : ℂ) :
    ‖stripAverageKernel a z t‖ =
      Real.exp (-z.re * t) / (Real.exp (a * t) + Real.exp (-a * t)) := by
  unfold stripAverageKernel
  rw [norm_div, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (add_pos (Real.exp_pos _) (Real.exp_pos _))]
  congr 2
  simp

theorem stripAverageKernel_decay (a t : ℝ) (z : ℂ) :
    ‖stripAverageKernel a z t‖ ≤ Real.exp (-(a - |z.re|) * |t|) := by
  rw [stripAverageKernel_norm]
  have hd : 0 < Real.exp (a * t) + Real.exp (-a * t) := by positivity
  have hden : Real.exp (a * |t|) ≤ Real.exp (a * t) + Real.exp (-a * t) := by
    rcases le_total 0 t with ht | ht
    · rw [abs_of_nonneg ht]
      exact le_add_of_nonneg_right (Real.exp_pos _).le
    · rw [abs_of_nonpos ht]
      have he : a * -t = -a * t := by ring
      rw [he]
      exact le_add_of_nonneg_left (Real.exp_pos _).le
  have hnum : Real.exp (-z.re * t) ≤ Real.exp (|z.re| * |t|) := by
    apply Real.exp_le_exp.mpr
    calc
      -z.re * t ≤ |-z.re * t| := le_abs_self _
      _ = |z.re| * |t| := by rw [abs_mul, abs_neg]
  apply (div_le_iff₀ hd).mpr
  calc
    _ ≤ Real.exp (|z.re| * |t|) := hnum
    _ = Real.exp (-(a - |z.re|) * |t|) * Real.exp (a * |t|) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hden (Real.exp_pos _).le

theorem stripAverageKernel_integrable {a : ℝ} {z : ℂ} (hz : |z.re| < a) :
    Integrable (stripAverageKernel a z) := by
  apply (integrable_laplaceKernel (sub_pos.mpr hz)).norm.mono'
    (stripAverageKernel_continuous a z).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun t => by
    simpa only [laplaceKernel, Complex.norm_exp, Complex.neg_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, neg_mul] using
      stripAverageKernel_decay a t z

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_StripSineQuotient
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Removing the pole in the modular strip contour

The scalar contour step in Rieffel--Van Daele, Lemma 4.6, uses
`(exp (i φ z) f z - f 0) / sin (π z)`. Divided differences remove its
singularity at zero without assuming a residue theorem.
-/

namespace KadisonKastler

open Set Filter
open scoped Topology

noncomputable section

def stripSineSlope (z : ℂ) : ℂ :=
  dslope (fun w : ℂ => Complex.sin (Real.pi * w)) 0 z

theorem stripSineSlope_ne_zero {z : ℂ} (hz : |z.re| < 1) :
    stripSineSlope z ≠ 0 := by
  by_cases hz0 : z = 0
  · subst z
    unfold stripSineSlope
    rw [dslope_same]
    have hd := ((hasDerivAt_id (0 : ℂ)).const_mul (Real.pi : ℂ)).csin
    have he : deriv (fun w : ℂ => Complex.sin (Real.pi * w)) 0 = (Real.pi : ℂ) := by
      simpa only [id_eq, mul_zero, Complex.cos_zero, mul_one, one_mul] using hd.deriv
    rw [he]
    exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  · have hs : Complex.sin (Real.pi * z) ≠ 0 := by
      intro he
      obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp he
      have hzk : z = (k : ℂ) := by
        apply mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
        exact hk.trans (mul_comm _ _)
      have hk' : (-1 : ℝ) < k ∧ (k : ℝ) < 1 := by simpa [hzk] using abs_lt.mp hz
      have hk0 : k = 0 := by
        have h₁ : (-1 : ℤ) < k := by exact_mod_cast hk'.1
        have h₂ : k < (1 : ℤ) := by exact_mod_cast hk'.2
        omega
      exact hz0 (by simpa [hk0] using hzk)
    unfold stripSineSlope
    rw [dslope_of_ne _ hz0]
    simp only [slope, sub_zero, mul_zero, Complex.sin_zero, smul_eq_mul, vsub_eq_sub]
    exact mul_ne_zero (inv_ne_zero hz0) hs

theorem stripSineSlope_differentiable : Differentiable ℂ stripSineSlope := by
  apply differentiableOn_univ.mp
  exact (Complex.differentiableOn_dslope (mem_nhds_iff.mpr ⟨univ,
    subset_rfl, isOpen_univ, mem_univ _⟩)).mpr (by fun_prop)

def stripSineQuotient (φ : ℝ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  dslope (fun w => Complex.exp (Complex.I * φ * w) * f w) 0 z / stripSineSlope z

theorem stripSineQuotient_eq {φ : ℝ} {f : ℂ → ℂ} {z : ℂ} (hz : z ≠ 0) :
    stripSineQuotient φ f z =
      (Complex.exp (Complex.I * φ * z) * f z - f 0) / Complex.sin (Real.pi * z) := by
  unfold stripSineQuotient stripSineSlope
  rw [dslope_of_ne _ hz, dslope_of_ne _ hz]
  simp only [slope, sub_zero, mul_zero, Complex.exp_zero, one_mul, Complex.sin_zero,
    smul_eq_mul, vsub_eq_sub]
  exact mul_div_mul_left _ _ (inv_ne_zero hz)

theorem stripSineQuotient_continuousOn (φ : ℝ) (f : ℂ → ℂ)
    (hc : ContinuousOn f {z : ℂ | |z.re| ≤ 1 / 2})
    (hd : DifferentiableAt ℂ f 0) :
    ContinuousOn (stripSineQuotient φ f) {z : ℂ | |z.re| ≤ 1 / 2} := by
  apply ContinuousOn.div _ stripSineSlope_differentiable.continuous.continuousOn
    (fun z hz => stripSineSlope_ne_zero (lt_of_le_of_lt hz (by norm_num)))
  intro z hz
  by_cases h : z = 0
  · subst z
    exact (continuousAt_dslope_same.mpr ((by fun_prop :
      DifferentiableAt ℂ (fun w : ℂ => Complex.exp (Complex.I * φ * w)) 0).mul hd)).continuousWithinAt
  · exact (continuousWithinAt_dslope_of_ne h).mpr
      ((by fun_prop : Continuous (fun w : ℂ => Complex.exp (Complex.I * φ * w))).continuousWithinAt.mul (hc z hz))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_StripContourBoundary
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Boundary values of the regularized strip contour -/

namespace KadisonKastler

noncomputable section

theorem sine_strip_right (t : ℝ) :
    Complex.sin (Real.pi * ((1 / 2 : ℂ) + t * Complex.I)) =
      ((Real.exp (Real.pi * t) + Real.exp (-Real.pi * t) : ℝ) : ℂ) / 2 := by
  rw [show (Real.pi : ℂ) * ((1 / 2 : ℂ) + t * Complex.I) =
    (Real.pi : ℂ) / 2 + (Real.pi * t : ℝ) * Complex.I by push_cast; ring]
  rw [Complex.sin_add, Complex.sin_pi_div_two, Complex.cos_pi_div_two,
    one_mul, zero_mul, add_zero, Complex.cos_mul_I]
  rw [Complex.cosh]
  push_cast
  rw [neg_mul]

theorem sine_strip_left (t : ℝ) :
    Complex.sin (Real.pi * ((-1 / 2 : ℂ) + t * Complex.I)) =
      -(((Real.exp (Real.pi * t) + Real.exp (-Real.pi * t) : ℝ) : ℂ) / 2) := by
  have h := sine_strip_right (-t)
  rw [show (Real.pi : ℂ) * ((-1 / 2 : ℂ) + t * Complex.I) =
    -((Real.pi : ℂ) * ((1 / 2 : ℂ) + (-t : ℝ) * Complex.I)) by push_cast; ring,
    Complex.sin_neg, h]
  congr 2
  push_cast
  simp only [mul_neg, neg_mul, neg_neg]
  ring

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_StripKernelMass
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-- d13f23b's `MeasureTheory.integral_comp_exp` (port compat, absent from our Mathlib). -/
theorem integralCompExpCompat {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : ℝ → E) :
    ∫ x, Real.exp x • g (Real.exp x) = ∫ y in Set.Ioi 0, g y := by
  symm
  rw [← Real.range_exp, ← Set.image_univ]
  simpa using MeasureTheory.integral_image_eq_integral_abs_deriv_smul .univ
    (fun x _ ↦ (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn g

/-! # The mass of the strip contour kernel -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

theorem inverse_exp_sum (t : ℝ) :
    (Real.exp t + Real.exp (-t))⁻¹ = Real.exp t * (1 + Real.exp t ^ 2)⁻¹ := by
  rw [Real.exp_neg]
  field_simp
  ring

theorem integral_strip_real_kernel {a : ℝ} (ha : 0 < a) :
    (∫ t : ℝ, (Real.exp (a * t) + Real.exp (-a * t))⁻¹) = Real.pi / (2 * a) := by
  have hbase : (∫ t : ℝ, (Real.exp t + Real.exp (-t))⁻¹) = Real.pi / 2 := by
    simp_rw [inverse_exp_sum]
    have h := integralCompExpCompat (fun x : ℝ => (1 + x ^ 2)⁻¹)
    simpa only [smul_eq_mul, integral_Ioi_inv_one_add_sq, Real.arctan_zero,
      sub_zero] using h
  have he := Measure.integral_comp_mul_left
    (fun t : ℝ => (Real.exp t + Real.exp (-t))⁻¹) a
  rw [hbase, abs_of_pos (inv_pos.mpr ha)] at he
  convert he using 1
  · congr 1
    funext t
    rw [neg_mul]
  · simp only [smul_eq_mul]
    ring

theorem integral_stripAverageKernel_zero :
    (∫ t : ℝ, stripAverageKernel Real.pi 0 t) = (1 / 2 : ℂ) := by
  have hreal : (∫ t : ℝ, (Real.exp (Real.pi * t) + Real.exp (-Real.pi * t))⁻¹) =
      (1 / 2 : ℝ) := by
    rw [integral_strip_real_kernel Real.pi_pos]
    field_simp
  have he : (fun t => stripAverageKernel Real.pi 0 t) =
      (fun t : ℝ => (((Real.exp (Real.pi * t) + Real.exp (-Real.pi * t))⁻¹ : ℝ) : ℂ)) := by
    funext t
    simp only [stripAverageKernel, zero_mul, neg_zero, Complex.exp_zero, one_div,
      Complex.ofReal_inv]
  rw [he, integral_complex_ofReal, hreal]
  norm_num

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MinimalSpatialImplementer
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Minimum distance for bounded self-adjoint spatial implementers

The bounded family of self-adjoint implementers of the same derivation is
weak-operator compact. Its distance from the self-adjoint part of the
algebra is attained. This is the compactness step of Sakai's spatial
splitting argument (Ann. Math. 83 (1966), Lemma 2, p.274).
-/

namespace KadisonKastler

noncomputable section

open ContinuousLinearMapWOT Generator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def boundedSelfAdjointImplementers (M : VonNeumannAlgebra H) (T : H →L[ℂ] H) :
    Set (H →WOT[ℂ] H) :=
  {S | IsSelfAdjoint S.toCLM ∧ ‖S.toCLM‖ ≤ ‖T‖ ∧ S.toCLM - T ∈ M.commutant}

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MinimalResidualFamily
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The convex family of minimum-distance spatial residuals

For a minimizing pair, the residuals with no larger norm form a convex
set invariant under the unitaries of the commutant. Every member has
exactly the minimum norm. A strict norm decrease inside this set is
therefore impossible.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def boundedSpatialResiduals (M : VonNeumannAlgebra H)
    (T X : H →L[ℂ] H) (r : ℝ) : Set (H →L[ℂ] H) :=
  {C | IsSelfAdjoint C ∧ ‖C‖ ≤ r ∧ ‖X - C‖ ≤ ‖T‖ ∧ X - C - T ∈ M.commutant}

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixNearInclusion
attribute [-instance] _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Matrix unit-ball proximity and graph row estimates

The cb distance supplies a separate approximant at each matrix level.
No linear selection of those approximants is assumed.
-/

namespace KadisonKastler

open scoped WithCStarModule InnerProductSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- One direction of matrix unit-ball proximity, uniformly in the matrix size. -/
def MatrixNearInclusion (M N : VonNeumannAlgebra H) (γ : ℝ) : Prop :=
  ∀ (n : ℕ) (X : CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H)),
    (∀ i j, X i j ∈ M) → ‖X‖ ≤ 1 →
    ∃ Y : CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H),
      (∀ i j, Y i j ∈ N) ∧ ‖Y‖ ≤ 1 ∧ ‖X - Y‖ ≤ γ

namespace MatrixNearInclusion

variable {M N : VonNeumannAlgebra H} {γ η : ℝ}

local instance matrixNearOrder : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
local instance matrixNearStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _

end MatrixNearInclusion

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularPositiveCone
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The cone generated by modular quadratic vectors

The definition uses actual vectors `a J a J ξ`, finite positive combinations,
and norm closure. Its invariance is algebraic. Positivity of the reference
pairing is kept explicit here and proved for the polar Tomita conjugation
in `TomitaPositivePairing`.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

local instance instInnerProductSpaceReal_solutions : InnerProductSpace ℝ H := InnerProductSpace.complexToReal

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MultiplicationNewtonStep
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # One quadratic step in correction of multiplication

These are the concrete matrix identities used in the perturbation iteration.
The choice of a correcting cochain is a separate construction.
-/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A]

/-- The Hochschild coboundary of a linear cochain. -/
def linearCoboundary (D : A →ₗ[ℂ] A) : A →ₗ[ℂ] A →ₗ[ℂ] A where
  toFun x := (LinearMap.mul ℂ A x).comp D - D.comp (LinearMap.mul ℂ A x) +
    LinearMap.mul ℂ A (D x)
  map_add' x y := by
    ext z
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.mul_apply', map_add]
    abel
  map_smul' c x := by
    ext z
    simp [smul_sub, smul_add]

@[simp] theorem linearCoboundary_apply (D : A →ₗ[ℂ] A) (x y : A) :
    linearCoboundary D x y = x * D y - D (x * y) + D x * y := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MultiplicationCorrectionSequence
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Iterating the quadratic cochain correction

A cochain with unit complete bound and quadratic coboundary remainder
produces successive associative multiplications whose defects halve.
-/

namespace KadisonKastler

noncomputable section

variable (A : Type*) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

structure SmallAssociativeProduct (q : ℝ) where
  mul : A →ₗ[ℂ] A →ₗ[ℂ] A
  assoc : ∀ x y z, mul (mul x y) z = mul x (mul y z)
  star_mul : ∀ x y, star (mul x y) = mul (star y) (star x)
  bound : HaagerupBound (mul - LinearMap.mul ℂ A) q

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_NonunitalFiberCenter
attribute [-instance] _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Scalar centers of nonunital representation ranges

These adapters keep the range Hilbert space and its unit projection inside
one definition when a common source is restricted to a smaller algebra.
-/

namespace KadisonKastler

open KadisonSimilarity
open scoped lp

noncomputable section

variable {X A B C K : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def NonunitalFiberScalarCenter (ρ : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) : Prop :=
  ∀ a : (representationVonNeumannAlgebra (nonunitalRangeRepresentation ρ)).toStarSubalgebra,
    (∀ c, a * c = c * a) → ∃ z : ℂ, a = algebraMap ℂ _ z

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_OperatorCochainStar
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Involution symmetrization of operator-valued cochains -/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A]

def cochainSharp (D : A →ₗ[ℂ] A) : A →ₗ[ℂ] A where
  toFun x := star (D (star x))
  map_add' x y := by simp
  map_smul' c x := by simp

@[simp] theorem cochainSharp_apply (D : A →ₗ[ℂ] A) (x : A) :
    cochainSharp D x = star (D (star x)) := rfl

def bilinearSharp (f : A →ₗ[ℂ] A →ₗ[ℂ] A) : A →ₗ[ℂ] A →ₗ[ℂ] A where
  toFun x :=
    { toFun := fun y => star (f (star y) (star x))
      map_add' y z := by simp
      map_smul' c y := by simp }
  map_add' x y := by ext z; simp
  map_smul' c x := by ext z; simp

@[simp] theorem bilinearSharp_apply (f : A →ₗ[ℂ] A →ₗ[ℂ] A) (x y : A) :
    bilinearSharp f x y = star (f (star y) (star x)) := rfl

@[simp] theorem bilinearSharp_sub (f g : A →ₗ[ℂ] A →ₗ[ℂ] A) :
    bilinearSharp (f - g) = bilinearSharp f - bilinearSharp g := by
  ext x y
  simp


end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PointedWordReduction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Repeated words in commuting matrix sites

The reduction below is independent of the representation: it gathers each
site into one matrix entry and records incompatible matrix indices by zero.
-/

namespace KadisonKastler

open Generator

abbrev MatrixSiteLetter (I : Type*) := I × Fin 2 × Fin 2
abbrev MatrixSiteWord (I : Type*) := List (MatrixSiteLetter I)

namespace MatrixSiteWord

variable {I J A : Type*}

def reindex (e : I ≃ J) (w : MatrixSiteWord I) : MatrixSiteWord J :=
  w.map fun a => (e a.1, a.2.1, a.2.2)

def star (w : MatrixSiteWord I) : MatrixSiteWord I :=
  w.reverse.map fun a => (a.1, a.2.2, a.2.1)

def indices (w : MatrixSiteWord I) : List I := w.map Prod.fst

@[simp] theorem reindex_nil (e : I ≃ J) : reindex e [] = [] := rfl

@[simp] theorem reindex_cons (e : I ≃ J) (a : MatrixSiteLetter I) (w : MatrixSiteWord I) :
    reindex e (a :: w) = (e a.1, a.2.1, a.2.2) :: reindex e w := rfl

@[simp] theorem reindex_append (e : I ≃ J) (w v : MatrixSiteWord I) :
    reindex e (w ++ v) = reindex e w ++ reindex e v := by
  simp only [reindex, List.map_append]

@[simp] theorem reindex_star (e : I ≃ J) (w : MatrixSiteWord I) :
    reindex e (star w) = star (reindex e w) := by
  simp only [reindex, star, List.map_reverse, List.map_map, Function.comp_def]

variable [Ring A] [StarRing A] [_root_.Algebra ℂ A]

def eval (E : I → MatrixUnitSystem (Fin 2) A) (w : MatrixSiteWord I) : A :=
  (w.map fun a => (E a.1).entry a.2.1 a.2.2).prod

@[simp] theorem eval_nil (E : I → MatrixUnitSystem (Fin 2) A) : eval E [] = 1 := rfl

@[simp] theorem eval_cons (E : I → MatrixUnitSystem (Fin 2) A)
    (a : MatrixSiteLetter I) (w : MatrixSiteWord I) :
    eval E (a :: w) = (E a.1).entry a.2.1 a.2.2 * eval E w := rfl

@[simp] theorem eval_append (E : I → MatrixUnitSystem (Fin 2) A)
    (w v : MatrixSiteWord I) : eval E (w ++ v) = eval E w * eval E v := by
  simp only [eval, List.map_append, List.prod_append]

@[simp] theorem eval_reindex (E : J → MatrixUnitSystem (Fin 2) A)
    (e : I ≃ J) (w : MatrixSiteWord I) :
    eval E (reindex e w) = eval (E ∘ e) w := by
  simp only [eval, reindex, List.map_map, Function.comp_def]

@[simp] theorem eval_star (E : I → MatrixUnitSystem (Fin 2) A)
    (w : MatrixSiteWord I) : eval E (star w) = Star.star (eval E w) := by
  induction w with
  | nil => simp [star]
  | cons a w ih =>
    have he : star (a :: w) = star w ++ [(a.1, a.2.2, a.2.1)] := by
      simp [star, List.reverse_cons]
    rw [he, eval_append, ih]
    simp only [eval_cons, eval_nil, mul_one, star_mul, (E a.1).star_entry]

section Reduction

variable [DecidableEq I]

/-- Insert a matrix entry into a word with distinct sites. -/
def insert (a : MatrixSiteLetter I) : MatrixSiteWord I → Option (MatrixSiteWord I)
  | [] => some [a]
  | b :: w =>
    if a.1 = b.1 then
      if a.2.2 = b.2.1 then some ((a.1, a.2.1, b.2.2) :: w) else none
    else (insert a w).map (List.cons b)

/-- The canonical distinct-site reduction; `none` denotes zero. -/
def reduce : MatrixSiteWord I → Option (MatrixSiteWord I)
  | [] => some []
  | a :: w => (reduce w).bind (insert a)

def evalOption (E : I → MatrixUnitSystem (Fin 2) A)
    (w : Option (MatrixSiteWord I)) : A := w.elim 0 (eval E)

omit [DecidableEq I] in
theorem evalOption_map_cons (E : I → MatrixUnitSystem (Fin 2) A)
    (a : MatrixSiteLetter I) (w : Option (MatrixSiteWord I)) :
    evalOption E (w.map (List.cons a)) =
      (E a.1).entry a.2.1 a.2.2 * evalOption E w := by
  cases w <;> simp [evalOption]

theorem evalOption_insert (E : I → MatrixUnitSystem (Fin 2) A)
    (hE : ∀ i j, i ≠ j → ∀ a b c d,
      Commute ((E i).entry a b) ((E j).entry c d))
    (a : MatrixSiteLetter I) (w : MatrixSiteWord I) :
    evalOption E (insert a w) = (E a.1).entry a.2.1 a.2.2 * eval E w := by
  induction w with
  | nil => simp [insert, evalOption]
  | cons b w ih =>
    by_cases hij : a.1 = b.1
    · by_cases hbc : a.2.2 = b.2.1
      · simp only [insert, hij, hbc, ite_true, if_true, evalOption, Option.elim_some, eval_cons]
        rw [← mul_assoc, ← hij, (E a.1).mul_entry]
        simp only [ite_true, if_true]
      · simp only [insert, hij, hbc, ite_true, if_true, ite_false, if_false, evalOption,
          Option.elim_none, eval_cons]
        rw [← mul_assoc, ← hij, (E a.1).mul_entry]
        simp only [hbc, ite_false, if_false, zero_mul]
    · simp only [insert, hij, ite_false, if_false]
      rw [evalOption_map_cons, ih, eval_cons, ← mul_assoc,
        ← (hE a.1 b.1 hij a.2.1 a.2.2 b.2.1 b.2.2).eq, mul_assoc]

theorem evalOption_reduce (E : I → MatrixUnitSystem (Fin 2) A)
    (hE : ∀ i j, i ≠ j → ∀ a b c d,
      Commute ((E i).entry a b) ((E j).entry c d))
    (w : MatrixSiteWord I) : evalOption E (reduce w) = eval E w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    simp only [reduce]
    cases h : reduce w with
    | none =>
      simp only [h, evalOption, Option.elim_none] at ih
      simp only [Option.bind_none, evalOption, Option.elim_none, eval_cons, ← ih, mul_zero]
    | some v =>
      simp only [h, evalOption, Option.elim_some] at ih
      simp only [Option.bind_some]
      rw [evalOption_insert E hE, ih, eval_cons]

theorem indices_insert_subset (a : MatrixSiteLetter I) (w v : MatrixSiteWord I)
    (h : insert a w = some v) : ∀ i ∈ indices v, i = a.1 ∨ i ∈ indices w := by
  induction w generalizing v with
  | nil =>
    simp only [insert, Option.some.injEq] at h
    subst v
    simp [indices]
  | cons b w ih =>
    by_cases hab : a.1 = b.1
    · by_cases hbc : a.2.2 = b.2.1
      · simp only [insert, hab, hbc, ite_true, if_true, Option.some.injEq] at h
        subst v
        intro i hi
        simp only [indices, List.map_cons, List.mem_cons] at hi ⊢
        exact hi.imp (fun h => h.trans hab.symm) (fun h => Or.inr h)
      · simp [insert, hab, hbc] at h
    · simp only [insert, hab, ite_false, if_false] at h
      cases hv : insert a w with
      | none => simp [hv] at h
      | some z =>
        simp only [hv, Option.map_some, Option.some.injEq] at h
        subst v
        intro i hi
        simp only [indices, List.map_cons, List.mem_cons] at hi ⊢
        rcases hi with hi | hi
        · exact Or.inr (Or.inl hi)
        · exact (ih z hv i hi).imp id Or.inr

theorem indices_insert_nodup (a : MatrixSiteLetter I) (w v : MatrixSiteWord I)
    (hw : (indices w).Nodup) (h : insert a w = some v) : (indices v).Nodup := by
  induction w generalizing v with
  | nil =>
    simp only [insert, Option.some.injEq] at h
    subst v
    simp [indices]
  | cons b w ih =>
    have hw' : b.1 ∉ indices w ∧ (indices w).Nodup := by
      simpa only [indices, List.map_cons, List.nodup_cons] using hw
    by_cases hab : a.1 = b.1
    · by_cases hbc : a.2.2 = b.2.1
      · simp only [insert, hab, hbc, ite_true, if_true, Option.some.injEq] at h
        subst v
        simpa only [indices, List.map_cons, List.nodup_cons, hab] using hw
      · simp [insert, hab, hbc] at h
    · simp only [insert, hab, ite_false, if_false] at h
      cases hv : insert a w with
      | none => simp [hv] at h
      | some z =>
        simp only [hv, Option.map_some, Option.some.injEq] at h
        subst v
        apply List.nodup_cons.mpr
        constructor
        · intro hb
          rcases indices_insert_subset a w z hv b.1 hb with hb | hb
          · exact hab hb.symm
          · exact hw'.1 hb
        · exact ih z hw'.2 hv

theorem indices_reduce_nodup (w v : MatrixSiteWord I) (h : reduce w = some v) :
    (indices v).Nodup := by
  induction w generalizing v with
  | nil =>
    simp only [reduce, Option.some.injEq] at h
    subst v
    exact List.nodup_nil
  | cons a w ih =>
    simp only [reduce] at h
    cases hw : reduce w with
    | none => simp [hw] at h
    | some z =>
      simp only [hw, Option.bind_some] at h
      exact indices_insert_nodup a z v (ih z hw) h

end Reduction

end MatrixSiteWord

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PointedFiniteBlock
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Full matrix blocks on finitely many product sites

The index type records one binary matrix index at each site. Distinct
sites commute, so their ordered products form a full matrix system.
This is the finite algebraic construction needed for the product stages.
-/

namespace KadisonKastler

open Generator

noncomputable section

variable {I : Type*}

abbrev MatrixSiteBlockIndex : List I → Type
  | [] => Unit
  | _ :: l => Fin 2 × MatrixSiteBlockIndex l

instance matrixSiteBlockIndexFintype : (l : List I) → Fintype (MatrixSiteBlockIndex l)
  | [] => inferInstanceAs (Fintype Unit)
  | _ :: l => by
    letI := matrixSiteBlockIndexFintype l
    exact inferInstanceAs (Fintype (Fin 2 × MatrixSiteBlockIndex l))

instance matrixSiteBlockIndexDecidableEq : (l : List I) →
    DecidableEq (MatrixSiteBlockIndex l)
  | [] => inferInstanceAs (DecidableEq Unit)
  | _ :: l => by
    letI := matrixSiteBlockIndexDecidableEq l
    exact inferInstanceAs (DecidableEq (Fin 2 × MatrixSiteBlockIndex l))

def matrixSiteBlockZero : (l : List I) → MatrixSiteBlockIndex l
  | [] => ()
  | _ :: l => (0, matrixSiteBlockZero l)

def matrixSiteBlockMapEquiv {J : Type*} (f : I → J) :
    (l : List I) → MatrixSiteBlockIndex l ≃ MatrixSiteBlockIndex (l.map f)
  | [] => Equiv.refl _
  | _ :: l => (Equiv.refl (Fin 2)).prodCongr (matrixSiteBlockMapEquiv f l)

def matrixSiteBlockIndexOfFunction : (l : List I) → (I → Fin 2) → MatrixSiteBlockIndex l
  | [], _ => ()
  | i :: l, f => (f i, matrixSiteBlockIndexOfFunction l f)

theorem matrixSiteBlockIndexOfFunction_congr (l : List I) {f g : I → Fin 2}
    (h : ∀ i ∈ l, f i = g i) :
    matrixSiteBlockIndexOfFunction l f = matrixSiteBlockIndexOfFunction l g := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    exact Prod.ext (h i (by simp)) (ih (fun j hj => h j (List.mem_cons_of_mem _ hj)))

theorem matrixSiteBlockIndexOfFunction_surjective (l : List I) (hl : l.Nodup) :
    Function.Surjective (matrixSiteBlockIndexOfFunction l) := by
  classical
  induction l with
  | nil => intro r; cases r; exact ⟨fun _ => 0, rfl⟩
  | cons i l ih =>
    intro r
    obtain ⟨f, hf⟩ := ih (List.nodup_cons.mp hl).2 r.2
    refine ⟨Function.update f i r.1, Prod.ext ?_ ?_⟩
    · change Function.update f i r.1 i = r.1
      exact Function.update_self _ _ _
    apply Eq.trans (matrixSiteBlockIndexOfFunction_congr l ?_) hf
    intro j hj
    exact Function.update_of_ne (fun h : j = i => (List.nodup_cons.mp hl).1 (h ▸ hj)) _ _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PointedLocalMatrix
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFiniteBoundedWord _root_.OAI.HochschildPatching.instFiniteLinearLabel _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The four-dimensional pointed matrix state

Left and right matrix multiplication act on the Hilbert space of two by
two matrices. The square root of the diagonal density is cyclic for
both actions. An orthonormal basis beginning at that vector makes the
reference vector the zero-coordinate vacuum used by the infinite product.
-/

namespace KadisonKastler

noncomputable section

abbrev PointedLocalHilbert := EuclideanSpace ℂ (Fin 4)

def pointedLocalVacuum : PointedLocalHilbert := EuclideanSpace.single 0 1

abbrev PointedRawHilbert := EuclideanSpace ℂ (Fin 2 × Fin 2)

def pointedRawLeft (i j : Fin 2) : PointedRawHilbert →L[ℂ] PointedRawHilbert :=
  LinearMap.toContinuousLinearMap
    { toFun x := WithLp.toLp 2 (fun p => if p.1 = i then x (j, p.2) else 0)
      map_add' x y := by ext p; by_cases h : p.1 = i <;> simp [h]
      map_smul' c x := by ext p; simp }

@[simp] theorem pointedRawLeft_apply (i j : Fin 2) (x : PointedRawHilbert)
    (p : Fin 2 × Fin 2) : pointedRawLeft i j x p = if p.1 = i then x (j, p.2) else 0 := rfl

def pointedRawRight (i j : Fin 2) : PointedRawHilbert →L[ℂ] PointedRawHilbert :=
  LinearMap.toContinuousLinearMap
    { toFun x := WithLp.toLp 2 (fun p => if p.2 = i then x (p.1, j) else 0)
      map_add' x y := by ext p; by_cases h : p.2 = i <;> simp [h]
      map_smul' c x := by ext p; simp }

@[simp] theorem pointedRawRight_apply (i j : Fin 2) (x : PointedRawHilbert)
    (p : Fin 2 × Fin 2) : pointedRawRight i j x p = if p.2 = i then x (p.1, j) else 0 := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PointedMatrixSum
attribute [-instance] _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Tensor products of pointed matrix-site systems

The two site families act in the two tensor legs. Finite words split into
their two subwords, and their vector moments multiply. Cyclicity follows
from the dense tensor-product orbit; separation follows by the same
argument for the commutants. No modular or infinite-product input is used.
-/

namespace KadisonKastler

open Generator UnitalTomsWinter
open scoped TensorProduct

noncomputable section

universe u

def sumLeftList {I J : Type*} (l : List (I ⊕ J)) : List I :=
  l.filterMap (fun x => match x with | .inl i => some i | .inr _ => none)

def sumRightList {I J : Type*} (l : List (I ⊕ J)) : List J :=
  l.filterMap (fun x => match x with | .inl _ => none | .inr j => some j)

theorem sumLeftList_nodup {I J : Type*} {l : List (I ⊕ J)}
    (h : l.Nodup) : (sumLeftList l).Nodup := by
  apply List.Nodup.filterMap _ h
  intro a b i ha hb
  cases a <;> cases b <;> simp_all

theorem sumRightList_nodup {I J : Type*} {l : List (I ⊕ J)}
    (h : l.Nodup) : (sumRightList l).Nodup := by
  apply List.Nodup.filterMap _ h
  intro a b i ha hb
  cases a <;> cases b <;> simp_all

theorem sumList_scalar_prod {I J : Type*} (a : I → ℂ) (b : J → ℂ)
    (l : List (I ⊕ J)) :
    (l.map (Sum.elim a b)).prod =
      ((sumLeftList l).map a).prod * ((sumRightList l).map b).prod := by
  induction l with
  | nil => simp [sumLeftList, sumRightList]
  | cons x l ih =>
    cases x <;> simp [sumLeftList, sumRightList] at ih ⊢
    all_goals rw [ih]; ring

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PointedPowerConfigurations
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Configuration coordinates for a pointed countable Hilbert product

A configuration records the finitely many sites outside the reference
vector. Splitting off one site gives a finite Hilbert sum of identical
tail spaces, with an explicit action on every orthonormal basis vector.
-/

namespace KadisonKastler

open Generator
open scoped BigOperators lp

noncomputable section

abbrev PointedPowerConfiguration := ℕ →₀ Fin 4
abbrev PointedPowerHilbert := ℓ²(PointedPowerConfiguration, ℂ)

def pointedPowerBasis (f : PointedPowerConfiguration) : PointedPowerHilbert :=
  lp.single 2 f 1

def pointedPowerVacuum : PointedPowerHilbert := pointedPowerBasis 0

@[simp] theorem norm_pointedPowerBasis (f : PointedPowerConfiguration) :
    ‖pointedPowerBasis f‖ = 1 := by
  simp only [pointedPowerBasis, lp.norm_single (by norm_num : (0 : ENNReal) < 2), norm_one]

@[simp] theorem norm_pointedPowerVacuum : ‖pointedPowerVacuum‖ = 1 :=
  norm_pointedPowerBasis 0

def pointedPowerHilbertBasis : HilbertBasis PointedPowerConfiguration ℂ PointedPowerHilbert :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)

@[simp] theorem pointedPowerHilbertBasis_apply (f : PointedPowerConfiguration) :
    pointedPowerHilbertBasis f = pointedPowerBasis f := by
  exact (pointedPowerHilbertBasis.repr_symm_single f).symm

abbrev PointedPowerTail (i : ℕ) := {f : PointedPowerConfiguration // f i = 0}
abbrev PointedPowerTailHilbert (i : ℕ) := ℓ²(PointedPowerTail i, ℂ)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PointedSitesTransport
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Spatial transport of pointed matrix products

Conjugating all site operators by one Hilbert-space equivalence preserves
cyclicity, separation and every finite product-state moment.
-/

namespace KadisonKastler

open UnitalTomsWinter

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem matrixUnit_algebra_map
    (E : Generator.MatrixUnitSystem (Fin 2) (H →L[ℂ] H))
    (f : (H →L[ℂ] H) →⋆ₐ[ℂ] (K →L[ℂ] K)) :
    E.algebra.map f = (E.map f).algebra := by
  apply le_antisymm
  · apply StarSubalgebra.map_le_iff_le_comap.mpr
    apply (E.algebra_le_iff _).mpr
    intro i j
    exact (E.map f).entry_mem i j
  · apply ((E.map f).algebra_le_iff _).mpr
    intro i j
    exact ⟨E.entry i j, E.entry_mem i j, rfl⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RemoteSiteDoubling
attribute [-instance] _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Interleaving two site families beyond a finite prefix -/

namespace KadisonKastler

/-- The left copy starts beyond the prefix, which belongs to the right copy. -/
def remoteNatDoubling (n : ℕ) : (ℕ ⊕ ℕ) ≃ ℕ :=
  (Equiv.sumComm ℕ ℕ).trans
    ((Equiv.sumCongr (finSumNatEquiv n).symm (Equiv.refl ℕ)).trans
      ((Equiv.sumAssoc (Fin n) ℕ ℕ).trans
        ((Equiv.sumCongr (Equiv.refl (Fin n)) Equiv.natSumNatEquivNat).trans
          (finSumNatEquiv n))))

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_StateScalingAlgebra
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Algebraic operations on state-scaling operators

The balance identity is the bounded-operator form of a modular eigenvector.
Its products, adjoints and centralizer compressions are proved directly.
-/

namespace KadisonKastler

open Generator

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {Ω : H}

def StateScales (M : VonNeumannAlgebra H) (Ω : H) (r : ℝ)
    (a : H →L[ℂ] H) : Prop :=
  ∀ b ∈ M, productVectorState Ω (b*a) = (r : ℂ)*productVectorState Ω (a*b)

namespace StateScales

variable {r s : ℝ} {a b : H →L[ℂ] H}

theorem mul (ha : StateScales M Ω r a) (hb : StateScales M Ω s b)
    (ham : a ∈ M) (hbm : b ∈ M) : StateScales M Ω (r*s) (a*b) := by
  intro x hx
  calc
    _ = productVectorState Ω ((x*a)*b) := by rw [mul_assoc]
    _ = (s : ℂ)*productVectorState Ω (b*(x*a)) := hb _ (M.mul_mem hx ham)
    _ = (s : ℂ)*productVectorState Ω ((b*x)*a) := by rw [mul_assoc]
    _ = (s : ℂ)*((r : ℂ)*productVectorState Ω (a*(b*x))) :=
      congrArg ((s : ℂ)*·) (ha _ (M.mul_mem hbm hx))
    _ = _ := by rw [Complex.ofReal_mul]; simp only [mul_assoc] <;> ring

theorem conjugate_state (x : H →L[ℂ] H) :
    star (productVectorState Ω x) = productVectorState Ω (star x) := by
  change (starRingEnd ℂ) (inner ℂ Ω (x Ω)) = inner ℂ Ω ((star x) Ω)
  rw [inner_conj_symm,ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]

theorem adjoint (ha : StateScales M Ω r a) (hr : r ≠ 0) :
    StateScales M Ω r⁻¹ (star a) := by
  intro x hx
  have hh := congrArg star (ha (star x) (M.toStarSubalgebra.star_mem' hx))
  rw [conjugate_state,star_mul,star_star,star_mul,conjugate_state,star_mul,
    star_star] at hh
  rw [show star (r : ℂ) = (r : ℂ) from Complex.conj_ofReal r] at hh
  rw [Complex.ofReal_inv]
  calc
    _ = (r : ℂ)⁻¹*((r : ℂ)*productVectorState Ω (x*star a)) := by
      rw [← mul_assoc,inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hr),one_mul]
    _ = _ := by rw [← show productVectorState Ω (star a*x) =
      (r : ℂ)*productVectorState Ω (x*star a) from by simpa only [mul_comm] using hh]

theorem initial_centralizes (ha : StateScales M Ω r a) (ham : a ∈ M) (hr : r ≠ 0) :
    ProductStateCentralizes M Ω (star a*a) := by
  have hh := (ha.adjoint hr).mul ha (M.toStarSubalgebra.star_mem' ham) ham
  rw [inv_mul_cancel₀ hr] at hh
  intro x hx
  simpa only [Complex.ofReal_one,one_mul] using (hh x hx).symm

theorem final_centralizes (ha : StateScales M Ω r a) (ham : a ∈ M) (hr : r ≠ 0) :
    ProductStateCentralizes M Ω (a*star a) := by
  have hh := ha.mul (ha.adjoint hr) ham (M.toStarSubalgebra.star_mem' ham)
  rw [mul_inv_cancel₀ hr] at hh
  intro x hx
  simpa only [Complex.ofReal_one,one_mul] using (hh x hx).symm

end StateScales

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_WeakFieldKernel
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Kernel projections of measurable operator fields

Cesàro averages of a positive contraction converge strongly to its kernel
projection. Applied pointwise, this proves measurability of the projection
without using a measurable selection or Borel functional calculus input.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Topology BigOperators CStarAlgebra

noncomputable section

variable {D H : Type*} [MeasurableSpace D] {μ : Measure D}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace WeakOperatorRepresentative

local instance kernelTargetOrder : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
local instance kernelTargetStarOrder : StarOrderedRing (H →L[ℂ] H) := CStarAlgebra.spectralOrderedRing _

omit [CompleteSpace H] in
theorem starProjection_congr (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (h : U = V) :
    U.starProjection = V.starProjection := by
  subst V
  rfl

end WeakOperatorRepresentative

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_WeakFieldSpectralSupport
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Spectral support inside measurable fields

The pointwise support of a continuous positive part is a measurable field.
This connects the constructed kernel projection with the concrete spectral
splittings already used in finite-factor arguments.
-/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

variable {D H : Type*} [MeasurableSpace D] {μ : MeasureTheory.Measure D}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace WeakOperatorRepresentative

/-- The full concrete operator algebra. -/
def fullOperatorAlgebra : VonNeumannAlgebra H where
  toStarSubalgebra := ⊤
  centralizer_centralizer' := Set.Subset.antisymm (Set.subset_univ _)
    Set.subset_centralizer_centralizer

end WeakOperatorRepresentative

end

end KadisonKastler

end OAI
end


