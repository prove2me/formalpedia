-- Prove2me | Definitions.Def_Q260K012
-- name    : Q260K012
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T04:42:18.057199+00:00
-- url     : https://prove2.me/theorems/c5a08f64-e3ba-4528-b0de-cd1c4461850a
-- title:
--   Definitions bundle Q260K012 of the split of OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 220 declarations of OpenAI's Lean: 92 definitions, 10 inductive types or structures, 2 instances and 116 theorems. The definitions and types are `OAI.KadisonKastler.BoundedWeakAlgebraMap`, `OAI.KadisonKastler.CentralPairDecomposition`, `OAI.KadisonKastler.CoherentVectorCore`, `OAI.KadisonKastler.CoherentVectorCore.linearMap`, `OAI.KadisonKastler.CoherentVectorCore.operator`, `OAI.KadisonKastler.CommonCenterSeparableStability`, `OAI.KadisonKastler.CuntzFamily.liftedTwoBlockUnitary`, `OAI.KadisonKastler.FaithfulTracialState.comapStarAlgEquiv`, `OAI.KadisonKastler.FiniteVectorTrace`, `OAI.KadisonKastler.FrequencyDefectBound`, `OAI.KadisonKastler.FrequencySmoothing`, `OAI.KadisonKastler.FrequencySmoothing.smooth`, `OAI.KadisonKastler.FullMatrixCorner.amplifiedAlgebra`, `OAI.KadisonKastler.FullMatrixCorner.blockElement`, `OAI.KadisonKastler.FullMatrixCorner.finiteBlock`, `OAI.KadisonKastler.FullMatrixCorner.finiteBlockHom`, `OAI.KadisonKastler.FullMatrixCorner.finiteCompression`, `OAI.KadisonKastler.FullMatrixCorner.finiteSignedGroup`, `OAI.KadisonKastler.FullMatrixCorner.finiteSignedRepresentation`, `OAI.KadisonKastler.FullMatrixCorner.matrixEntry`, `OAI.KadisonKastler.FullMatrixCorner.regroupedColumns`, `OAI.KadisonKastler.FullMatrixCorner.regroupingIsometry`, `OAI.KadisonKastler.FullMatrixCorner.regroupingOperator`, `OAI.KadisonKastler.FullMatrixCorner.scalarBlockHom`, `OAI.KadisonKastler.GraphRowApproximation`, `OAI.KadisonKastler.HaagerupBound.toContinuousBilinear`, `OAI.KadisonKastler.IsModularStateGroup`, `OAI.KadisonKastler.LocalProductSwaps`, `OAI.KadisonKastler.MatrixOrbitIndex`, `OAI.KadisonKastler.ModularActionCocycle`, `OAI.KadisonKastler.ModularActionCocycle.gauge`, `OAI.KadisonKastler.ModularActionCocycle.regularField`, `OAI.KadisonKastler.ModularActionCocycle.symm`, `OAI.KadisonKastler.NonsingularAction.leftOnProduct`, `OAI.KadisonKastler.NonsingularAction.rightOnProduct`, `OAI.KadisonKastler.NormalizingFamily`, `OAI.KadisonKastler.PointedLocalMatrixData`, `OAI.KadisonKastler.PublishedHardyMultiplierEvaluation`, `OAI.KadisonKastler.PublishedMultiplicationCorrection`, `OAI.KadisonKastler.PublishedRealDiagonalDecomposition` and 62 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `KadisonKastler_AlgebraCocycleRepresentatives`, `KadisonKastler_AmplifiedAlgebra`, `KadisonKastler_BaireSelectionHulls`, `KadisonKastler_Basic`, `KadisonKastler_CanonicalAmplification`, `KadisonKastler_CocycleCoreTransport`, `KadisonKastler_CommonCenterReduction`, `KadisonKastler_CompleteLinearLimits`, `KadisonKastler_ConcreteTraceTransfer`, `KadisonKastler_ConcreteTraceUniqueness`, `KadisonKastler_ConjugateFactor`, `KadisonKastler_CornerCuntzFamily`, `KadisonKastler_CornerUnitary`, `KadisonKastler_CyclicOrbitRestriction`, `KadisonKastler_FiniteBlockCompression`, `KadisonKastler_FiniteBlockExtension`, `KadisonKastler_FiniteCornerGroups`, `KadisonKastler_FrequencyActionAlignment`, `KadisonKastler_FrequencyNest`, `KadisonKastler_FrequencySmoothing`, `KadisonKastler_HaagerupContinuous`, `KadisonKastler_InfiniteCornerInflation`, `KadisonKastler_InvariantOperatorMean`, `KadisonKastler_MatrixAveraging`, `KadisonKastler_MatrixCornerConjugation`, `KadisonKastler_MatrixOrbitSampleLaw`, `KadisonKastler_MatrixProductStateSwap`, `KadisonKastler_MatrixVonNeumann`, `KadisonKastler_ModularActionCocycle`, `KadisonKastler_ModularSiteEigen`, `KadisonKastler_ModularStateAction`, `KadisonKastler_NonsingularBoundary`, `KadisonKastler_NormalizerTopology`, `KadisonKastler_PairedRepresentations`, `KadisonKastler_ParameterizedBoundaryMean`, `KadisonKastler_PointedFiniteBlock`, `KadisonKastler_PointedLocalMatrix`, `KadisonKastler_PointedSiteBalance`, `KadisonKastler_PositiveFrequencyAlgebra`, `KadisonKastler_PreparedGraphRows`, `KadisonKastler_ProductBoundaryLifts`, `KadisonKastler_ProductInvariantIntegrals`, `KadisonKastler_ProductInvariantL2`, `KadisonKastler_ProductMatrixStages`, `KadisonKastler_ProductStateCentralizer`, `KadisonKastler_PublishedCentralDecomposition`, `KadisonKastler_PublishedCorrection`, `KadisonKastler_PublishedHardyEvaluation`, `KadisonKastler_PublishedNestDistance`, `KadisonKastler_PublishedRegularDiagonal`, `KadisonKastler_PublishedSimpleDerivation`, `KadisonKastler_RandomWalkPathAction`, `KadisonKastler_ReducingRestriction`, `KadisonKastler_RegularCommutantPackets`, `KadisonKastler_RegularCoreAlgebra`, `KadisonKastler_RegularCoreCharacters`, `KadisonKastler_RegularCoreCommutant`, `KadisonKastler_RegularCoreFields`, `KadisonKastler_RegularCoreHilbertSum`, `KadisonKastler_RegularCoreOperators`, `KadisonKastler_RegularCoreRepresentation`, `KadisonKastler_RepresentedCorner`, `KadisonKastler_RowVectorEstimate`, `KadisonKastler_ScalarWeakLimit`, `KadisonKastler_SequentialConjugacyTests`, `KadisonKastler_ShiftBoundarySpace`, `KadisonKastler_ShiftInvariantSigma`, `KadisonKastler_SignedMatrixRefinement`, `KadisonKastler_SimultaneousRowFamily`, `KadisonKastler_SpatialAssociatorAlgebra`, `KadisonKastler_SpatialAssociatorTransport`, `KadisonKastler_SpatialConjugacyTransport`, `KadisonKastler_SpatialProduct`, `KadisonKastler_SpatialSlice`, `KadisonKastler_SpatialSliceRecovery`, `KadisonKastler_SwappedBoundaryMean`, `KadisonKastler_TracialCauchySchwarz`, `KadisonKastler_TwoRatioFiniteSites`, `KadisonKastler_TwoRatioReindex`, `KadisonKastler_VectorCoreField`, `KadisonKastler_WeakMapCompact`, `KadisonKastler_WeakRowAction`, `TracialSplitting_SpatialTensor`.
--
--   **Imports.** It imports the published bundle `Def_StrongKadisonKastler`; the bundles `Q260K001`, `Q260K002`, `Q260K003`, `Q260K004` and `Q260K005` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q260K017`, `Q260K018`, `Q260K019` and `Q260K020`; the statements `OAI.KadisonKastler.Conjugates.regularTensor`, `OAI.KadisonKastler.FrequencySmoothing.continuous_smooth`, `OAI.KadisonKastler.FrequencySmoothing.norm_product_sub_one_le`, `OAI.KadisonKastler.MatrixNearInclusion.spatialProduct`, `OAI.KadisonKastler.StateScales.spatialRight`, `OAI.KadisonKastler.concrete_ucp_starEquiv_of_published`, `OAI.KadisonKastler.concrete_ucp_unitary_of_published`, `OAI.KadisonKastler.conjugated_representation_comparison`, `OAI.KadisonKastler.constructed_complete_closeness_of_paired_factor`, `OAI.KadisonKastler.exists_bounded_conjugacy_from_centralPair`, `OAI.KadisonKastler.exists_continuous_unital_transfer_of_traceDense`, `OAI.KadisonKastler.exists_finite_bimodular_covariance_families`, `OAI.KadisonKastler.exists_measurable_diagonal_unitary_on_set`, `OAI.KadisonKastler.exists_near_starEquiv_of_traceDense_unitary_images`, `OAI.KadisonKastler.kkDistance_generated_restriction_le`, `OAI.KadisonKastler.kkDistance_spatialProduct_le_of_matrixNearInclusion`, `OAI.KadisonKastler.paired_switch_commutator`, `OAI_KadisonKastler_publishedMultiplicationCorrection`, `OAI.KadisonKastler.publishedRealNestDistance`, `OAI.KadisonKastler.publishedSimpleDerivationInner`, `OAI.KadisonKastler.regularCore_central_fourier_field`, `OAI.KadisonKastler.regularCore_constant_central_scalar`, `OAI.KadisonKastler.regularCore_fixed_corner_commute_translations`, `OAI.KadisonKastler.regularCore_not_factor_of_trivial`, `OAI_KadisonKastler_spatialField_constant_of_two_shifts`, `OAI.KadisonKastler.traceHull_mem_ball` and `OAI.KadisonKastler.unitary_transfer_bound_of_traceDense`; the proofs of `OAI.KadisonKastler.Conjugates.regularTensor`, `OAI.KadisonKastler.FrequencySmoothing.continuous_smooth`, `OAI.KadisonKastler.blockAlgebraDecomposition_coordinate_transport`, `OAI.KadisonKastler.commutator_mem_of_small_expUnitary_normalizes`, `OAI.KadisonKastler.concrete_ucp_unitary_of_published`, `OAI.KadisonKastler.exists_matrixGraphRow_cost_le_480`, `OAI.KadisonKastler.exists_small_normalizer_log`, `OAI.KadisonKastler.kkDistance_generated_restriction_le`, `OAI.KadisonKastler.multiplication_correction_of_quadratic_cochains`, `OAI.KadisonKastler.nearConjugacy_of_matrixPair_preparation`, `OAI.KadisonKastler.paired_switch_commutator`, `OAI.KadisonKastler.publishedRealNestDistance`, `OAI.KadisonKastler.spatialTransportAlgebra_trans`, `OAI.KadisonKastler.traceHull_mem_ball`, `OAI.KadisonKastler.transported_algebra_field_decompose`, `OAI.KadisonKastler.transported_commutant_fields_of_field_inclusion` and `OAI.KadisonKastler.unitaryConjugateAlgebra_isII1`.
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
import Mathlib.Analysis.Normed.Operator.NNNorm
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
import Mathlib.Analysis.SpecialFunctions.Exponential
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
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Set.Pairwise.Chain
import Mathlib.Data.Sym.Card
import Mathlib.GroupTheory.FreeGroup.Basic
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
import Mathlib.MeasureTheory.Function.LocallyIntegrable
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
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.Trim
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
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
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.Star
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.StarSubalgebra
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
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Topology.Maps.Proper.Basic
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
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_StrongKadisonKastler
import Definitions.Def_Q260K001
import Definitions.Def_Q260K002
import Definitions.Def_Q260K003
import Definitions.Def_Q260K004
import Definitions.Def_Q260K005

section
-- module Solutions.OAIQ075_KS.KadisonKastler_Basic
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.PopaCorner.instOne _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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

theorem unitBall_bounded (M : VonNeumannAlgebra H) : Bornology.IsBounded (unitBall M) :=
  isBounded_iff_forall_norm_le.mpr ⟨1, fun _ hx => hx.2⟩

@[simp] theorem kkDistance_self (M : VonNeumannAlgebra H) : kkDistance M M = 0 :=
  Metric.hausdorffDist_self_zero

theorem unitaryConj_mul (v w : unitary (H →L[ℂ] H)) (x : H →L[ℂ] H) :
    unitaryConj (v * w) x = unitaryConj v (unitaryConj w x) := by
  simp [unitaryConj, mul_assoc]

@[simp] theorem conjugates_one (M : VonNeumannAlgebra H) : Conjugates 1 M M := by
  simp [Conjugates]

theorem Conjugates.symm {M N : VonNeumannAlgebra H} {v : unitary (H →L[ℂ] H)}
    (hv : Conjugates v M N) : Conjugates (star v) N M := by
  change unitaryConj (star v) '' (N : Set (H →L[ℂ] H)) = (M : Set (H →L[ℂ] H))
  rw [← hv, ← Set.image_comp]
  simp only [Function.comp_def, unitaryConj_star_unitaryConj, Set.image_id']

theorem Conjugates.trans {M N P : VonNeumannAlgebra H}
    {v w : unitary (H →L[ℂ] H)} (hv : Conjugates v M N) (hw : Conjugates w N P) :
    Conjugates (w * v) M P := by
  change unitaryConj (w * v) '' (M : Set (H →L[ℂ] H)) = (P : Set (H →L[ℂ] H))
  simp_rw [unitaryConj_mul]
  rw [← Set.image_image, hv, hw]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_NonsingularBoundary
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Nonsingular boundary actions and simultaneous representatives

The action preserves null sets, not necessarily the measure. Countability
allows all the identities used in the boundary argument to hold on one
invariant conull set. The final definition isolates the exact unitary
coefficient property in Björklund, arXiv:1406.0763, Theorem 2.1 and
Remark 2.2, expressed as a property of the unitary coefficients.
-/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

variable {G D : Type*} [Group G] [MeasurableSpace D]

variable {μ : Measure D} [SFinite μ]

/-- The exact double-ergodicity property with unitary coefficients used
below. It is the bounded-map specialization of Björklund's Theorem 2.1,
Remark 2.2 (arXiv:1406.0763), for a symmetric Poisson boundary. -/
def UnitaryDoubleErgodic (α : NonsingularAction G D μ) : Prop :=
  ∀ (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] [TopologicalSpace.SeparableSpace K]
    (σ : G →* unitary (K →L[ℂ] K)) (f : D × D → K),
    AEStronglyMeasurable f (μ.prod μ) →
    (∃ C : ℝ, ∀ᵐ x ∂μ.prod μ, ‖f x‖ ≤ C) →
    (∀ g, ∀ᵐ x ∂μ.prod μ, f (α.diagonal.toPerm g x) = (σ g : K →L[ℂ] K) (f x)) →
    ∃ v : K, (∀ g, (σ g : K →L[ℂ] K) v = v) ∧ f =ᵐ[μ.prod μ] fun _ => v

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_AlgebraCocycleRepresentatives
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrixAlgebraEquiv_apply _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.spatialTransportEquiv_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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

/-- Regard an ambient unitary contained in an algebra as a unitary of it. -/
def unitaryInAlgebra (M : VonNeumannAlgebra H) (u : unitary (H →L[ℂ] H))
    (hu : (u : H →L[ℂ] H) ∈ M) : unitary (Algebra M) :=
  ⟨⟨u, hu⟩, by
    constructor
    · apply Subtype.ext
      exact Unitary.star_mul_self_of_mem u.property
    · apply Subtype.ext
      exact Unitary.mul_star_self_of_mem u.property⟩

@[simp]
theorem unitaryInAlgebra_coe (M : VonNeumannAlgebra H) (u : unitary (H →L[ℂ] H))
    (hu : (u : H →L[ℂ] H) ∈ M) :
    (unitaryInAlgebra M u hu : Algebra M).val = (u : H →L[ℂ] H) := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RepresentedCorner
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Concrete compression to a common closed subspace

The corner acts on the subspace itself. Its operators are characterized by
membership of their extension by zero in the original von Neumann algebra.
This constructs the actual corner and proves that a common compression does
not increase Kadison--Kastler distance.
-/

namespace KadisonKastler

open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (E : Submodule ℂ H) [CompleteSpace E]

@[simp] theorem cornerExtension_one : cornerExtension E 1 = E.starProjection := by
  ext x
  rfl

theorem cornerExtension_mul (T S : E →L[ℂ] E) :
    cornerExtension E (T * S) = cornerExtension E T * cornerExtension E S := by
  ext x
  simp only [mul_apply_eq_comp, cornerExtension_apply,
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]

section Star

variable [CompleteSpace H]

theorem cornerExtension_star (T : E →L[ℂ] E) :
    cornerExtension E (star T) = star (cornerExtension E T) := by
  simp only [cornerExtension, LinearMap.coe_mk, AddHom.coe_mk,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_comp,
    Submodule.adjoint_subtypeL, Submodule.adjoint_orthogonalProjectionOnto,
    ContinuousLinearMap.comp_assoc]

end Star

/-- Coefficients of extension are coefficients on the projected vectors. -/
theorem inner_cornerExtension (T : E →L[ℂ] E) (x y : H) :
    inner ℂ y (cornerExtension E T x) =
      inner ℂ (E.orthogonalProjectionOnto y) (T (E.orthogonalProjectionOnto x)) := by
  exact (E.inner_orthogonalProjectionOnto_eq_of_mem_right
    (T (E.orthogonalProjectionOnto x)) y).symm

def cornerExtensionWOT (T : E →WOT[ℂ] E) : H →WOT[ℂ] H :=
  ContinuousLinearMapWOT.ofCLM (cornerExtension E T.toCLM)

variable [CompleteSpace H]

theorem continuous_cornerExtensionWOT : Continuous (cornerExtensionWOT E) := by
  apply ContinuousLinearMapWOT.continuous_iff.mpr
  intro x y
  change Continuous (fun T : E →WOT[ℂ] E => inner ℂ y (cornerExtension E T.toCLM x))
  simp only [inner_cornerExtension]
  exact ContinuousLinearMapWOT.continuous_inner_apply continuous_id _ _

/-- The algebra of the concrete corner; its identity extends to the given
orthogonal projection in the ambient algebra. -/
def representedCornerAlgebra (M : VonNeumannAlgebra H) (hp : E.starProjection ∈ M) :
    StarSubalgebra ℂ (E →L[ℂ] E) where
  carrier := {T | cornerExtension E T ∈ M}
  zero_mem' := by change cornerExtension E 0 ∈ M; simp
  one_mem' := by
    change cornerExtension E 1 ∈ M
    simpa only [cornerExtension_one] using hp
  add_mem' {T S} hT hS := by
    change cornerExtension E (T + S) ∈ M
    rw [map_add]
    exact M.add_mem hT hS
  mul_mem' {T S} hT hS := by
    change cornerExtension E (T * S) ∈ M
    rw [cornerExtension_mul]
    exact M.mul_mem hT hS
  algebraMap_mem' c := by
    change cornerExtension E (algebraMap ℂ (E →L[ℂ] E) c) ∈ M
    rw [Algebra.algebraMap_eq_smul_one, map_smul, cornerExtension_one]
    exact M.smul_mem hp c
  star_mem' {T} hT := by
    change cornerExtension E (star T) ∈ M
    rw [cornerExtension_star]
    exact star_mem hT

theorem representedCornerAlgebra_wotClosed (M : VonNeumannAlgebra H)
    (hp : E.starProjection ∈ M) :
    Generator.WOTClosed (representedCornerAlgebra E M hp) := by
  exact (Generator.Tracial.vonNeumann_wotClosed M).preimage
    (continuous_cornerExtensionWOT E)

/-- Compression of a von Neumann algebra to the range of one of its
projections, represented on that range. -/
def representedCorner (M : VonNeumannAlgebra H) (hp : E.starProjection ∈ M) :
    VonNeumannAlgebra E :=
  Generator.vonNeumannOfWOTClosed (representedCornerAlgebra E M hp)
    (representedCornerAlgebra_wotClosed E M hp)

@[simp] theorem mem_representedCorner (M : VonNeumannAlgebra H)
    (hp : E.starProjection ∈ M) (T : E →L[ℂ] E) :
    T ∈ representedCorner E M hp ↔ cornerExtension E T ∈ M := Iff.rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CornerUnitary
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Extending a corner unitary by the identity

A unitary on a closed subspace extends to a unitary on the ambient Hilbert
space, acting as the identity on the orthogonal complement. Its displacement
from the identity is exactly the displacement in the corner.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (E : Submodule ℂ H) [CompleteSpace E]

@[simp] theorem starProjection_mul_cornerExtension (T : E →L[ℂ] E) :
    E.starProjection * cornerExtension E T = cornerExtension E T := by
  rw [← cornerExtension_one E, ← cornerExtension_mul, one_mul]

@[simp] theorem cornerExtension_mul_starProjection (T : E →L[ℂ] E) :
    cornerExtension E T * E.starProjection = cornerExtension E T := by
  rw [← cornerExtension_one E, ← cornerExtension_mul, mul_one]

@[simp] theorem complement_mul_cornerExtension (T : E →L[ℂ] E) :
    (1 - E.starProjection) * cornerExtension E T = 0 := by
  rw [sub_mul, one_mul, starProjection_mul_cornerExtension, sub_self]

@[simp] theorem cornerExtension_mul_complement (T : E →L[ℂ] E) :
    cornerExtension E T * (1 - E.starProjection) = 0 := by
  rw [mul_sub, mul_one, cornerExtension_mul_starProjection, sub_self]

variable [CompleteSpace H]

theorem corner_starProjection_star : star E.starProjection = E.starProjection := by
  rw [← cornerExtension_one E, ← cornerExtension_star]
  exact congrArg (cornerExtension E) (star_one (R := E →L[ℂ] E))

omit [CompleteSpace H] in
theorem corner_complement_sq :
    (1 - E.starProjection) * (1 - E.starProjection) = 1 - E.starProjection := by
  have hp : E.starProjection * E.starProjection = E.starProjection := by
    simpa only [cornerExtension_one] using
      starProjection_mul_cornerExtension E (1 : E →L[ℂ] E)
  rw [mul_sub, sub_mul, sub_mul, one_mul, mul_one, one_mul, hp, sub_self, sub_zero]

theorem cornerExtension_add_complement_mem_unitary (v : unitary (E →L[ℂ] E)) :
    cornerExtension E (v : E →L[ℂ] E) + (1 - E.starProjection) ∈
      unitary (H →L[ℂ] H) := by
  have hstar : star (1 - E.starProjection) = 1 - E.starProjection := by
    rw [star_sub, star_one, corner_starProjection_star]
  apply Unitary.mem_iff.mpr
  constructor
  · rw [star_add, hstar, ← cornerExtension_star, add_mul, mul_add, mul_add,
      ← cornerExtension_mul, Unitary.star_mul_self_of_mem v.property,
      cornerExtension_one, cornerExtension_mul_complement,
      complement_mul_cornerExtension, corner_complement_sq]
    abel
  · rw [star_add, hstar, ← cornerExtension_star, add_mul, mul_add, mul_add,
      ← cornerExtension_mul, Unitary.mul_star_self_of_mem v.property,
      cornerExtension_one, cornerExtension_mul_complement,
      complement_mul_cornerExtension, corner_complement_sq]
    abel

/-- The unitary equal to `v` on `E` and to the identity on `Eᗮ`. -/
def cornerUnitary (v : unitary (E →L[ℂ] E)) : unitary (H →L[ℂ] H) :=
  ⟨cornerExtension E (v : E →L[ℂ] E) + (1 - E.starProjection),
    cornerExtension_add_complement_mem_unitary E v⟩

@[simp] theorem coe_cornerUnitary (v : unitary (E →L[ℂ] E)) :
    (cornerUnitary E v : H →L[ℂ] H) =
      cornerExtension E (v : E →L[ℂ] E) + (1 - E.starProjection) := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_InfiniteCornerInflation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Inflation through countably many matrix corners

The hypotheses are the algebraic matrix-unit relations and the strong sum
of their diagonal projections. They give an actual Hilbert direct-sum
decomposition. A corner operator is then applied on each summand; in
particular a corner unitary inflates with no loss in displacement.
-/

namespace KadisonKastler

open scoped BigOperators Topology
open Filter

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (E : Submodule ℂ H) [CompleteSpace E]

namespace FullMatrixCorner

variable {E} (F : FullMatrixCorner E)

def matrixEntry (T : H →L[ℂ] H) (i j : ℕ) : E →L[ℂ] E :=
  (F.column i).toContinuousLinearMap.adjoint.comp
    (T.comp (F.column j).toContinuousLinearMap)

end FullMatrixCorner

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CornerCuntzFamily
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Common isometries from countable matrix units

Regrouping the countably many matrix summands gives the finite Cuntz
families used to identify matrix unit balls with ordinary unit balls.
The isometries belong to every von Neumann algebra containing the matrix
units, by their explicit strong-sum formula.
-/

namespace KadisonKastler

open Filter
open scoped BigOperators Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {E : Submodule ℂ H} [CompleteSpace E]

namespace FullMatrixCorner

variable (F : FullMatrixCorner E)

theorem eq_of_inner_columns {x y : H}
    (h : ∀ k z, inner ℂ (F.column k z) x = inner ℂ (F.column k z) y) : x = y := by
  apply F.coordinates.injective
  apply lp.ext
  funext k
  apply ext_inner_left ℂ
  intro z
  have hx := F.coordinates.inner_map_map (F.column k z) x
  have hy := F.coordinates.inner_map_map (F.column k z) y
  rw [F.coordinates_column, lp.inner_single_left] at hx hy
  exact hx.trans ((h k z).trans hy.symm)

variable {n : Type*} (e : n × ℕ ≃ ℕ)

def regroupedColumns (i : n) (k : ℕ) : E →ₗᵢ[ℂ] H := F.column (e (i, k))

theorem regroupedColumns_orthogonal (i : n) :
    OrthogonalFamily ℂ (fun _ : ℕ => E) (F.regroupedColumns e i) := by
  intro k l hkl
  apply F.columns_orthogonal
  intro h
  exact hkl (congrArg Prod.snd (e.injective h))

/-- The isometry sending matrix summand `k` to summand `e (i,k)`. -/
def regroupingIsometry (i : n) : H →ₗᵢ[ℂ] H :=
  (F.regroupedColumns_orthogonal e i).linearIsometry.comp F.coordinates.toLinearIsometry

@[simp] theorem regroupingIsometry_column (i : n) (k : ℕ) (x : E) :
    F.regroupingIsometry e i (F.column k x) = F.column (e (i, k)) x := by
  change (F.regroupedColumns_orthogonal e i).linearIsometry
    (F.coordinates (F.column k x)) = _
  rw [F.coordinates_column, OrthogonalFamily.linearIsometry_apply_single]
  rfl

def regroupingOperator (i : n) : H →L[ℂ] H :=
  (F.regroupingIsometry e i).toContinuousLinearMap

@[simp] theorem regroupingOperator_column (i : n) (k : ℕ) (x : E) :
    F.regroupingOperator e i (F.column k x) = F.column (e (i, k)) x :=
  F.regroupingIsometry_column e i k x

variable [DecidableEq n]

theorem adjoint_regrouping_column (i j : n) (k : ℕ) (x : E) :
    star (F.regroupingOperator e i) (F.column (e (j, k)) x) =
      if i = j then F.column k x else 0 := by
  apply F.eq_of_inner_columns
  intro l y
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
    F.regroupingOperator_column]
  simp only [column_apply]
  rw [F.inner_columns]
  by_cases hij : i = j
  · subst j
    by_cases hlk : l = k
    · subst k
      simp [F.inner_columns]
    · have hh : e (i, l) ≠ e (i, k) := fun h => hlk (congrArg Prod.snd (e.injective h))
      simp [hh, F.inner_columns, hlk]
  · have hh : e (i, l) ≠ e (j, k) := fun h => hij (congrArg Prod.fst (e.injective h))
    simp [hh, hij]

end FullMatrixCorner

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_AmplifiedAlgebra
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A concrete infinite amplification

The amplification of a corner algebra is the commutant of its diagonally
represented commutant. Its matrix entries are exactly the operators in the
corner algebra. This construction uses the actual countable matrix units.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {E : Submodule ℂ H} [CompleteSpace E]

namespace FullMatrixCorner

variable (F : FullMatrixCorner E)

theorem entry_column (i j k : ℕ) (x : E) :
    F.entry i j (F.column k x) = if j = k then F.column i x else 0 := by
  change (F.entry i j * F.entry k 0) x = _
  rw [F.mul_entry]
  split_ifs <;> rfl

/-- The concrete amplification in the coordinates supplied by `F`. -/
def amplifiedAlgebra (M : VonNeumannAlgebra E) : VonNeumannAlgebra H where
  toStarSubalgebra := StarSubalgebra.centralizer ℂ
    (F.inflateHom '' (M.commutant : Set (E →L[ℂ] E)))
  centralizer_centralizer' := by
    let S := F.inflateHom '' (M.commutant : Set (E →L[ℂ] E))
    change (S ∪ star S).centralizer.centralizer.centralizer = (S ∪ star S).centralizer
    exact Set.centralizer_centralizer_centralizer _

end FullMatrixCorner

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BaireSelectionHulls
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Measurable hulls of finite-prefix images

For a continuous Baire-space parametrization, measurable hulls permit
successive prefix choices outside one null set. This is the measure-specific
selection construction needed for the published unitary selector.
-/

namespace KadisonKastler

open MeasureTheory Set Filter
open scoped Topology

noncomputable section

@[simp] theorem bairePrefixCylinder_nil : bairePrefixCylinder [] = Set.univ := by
  ext a
  simp [bairePrefixCylinder]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CanonicalAmplification
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Spatial transport and the canonical infinite amplification

Transport into the initial coordinate preserves the unit balls and their
Hausdorff distance. The abstract diagonal action obtained from the matrix
units is exactly the coordinatewise action on the Hilbert direct sum.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem mem_spatialTransportAlgebra (e : H ≃ₗᵢ[ℂ] K) (M : VonNeumannAlgebra H)
    (T : K →L[ℂ] K) :
    T ∈ spatialTransportAlgebra e M ↔ e.conjStarAlgEquiv.symm T ∈ M := by
  constructor
  · rintro ⟨S, hS, rfl⟩
    change e.conjStarAlgEquiv.symm (e.conjStarAlgEquiv S) ∈ M
    rw [StarAlgEquiv.symm_apply_apply]
    exact hS
  · intro hT
    exact ⟨e.conjStarAlgEquiv.symm T, hT, e.conjStarAlgEquiv.apply_symm_apply T⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PairedRepresentations
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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

variable {R : Type*}
  [Ring R]
  [_root_.Algebra ℂ R]

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

/-- The diagonal pair of two star representations. -/
def pairedRepresentation (ρ θ : A →⋆ₐ[ℂ] B) :
    A →⋆ₐ[ℂ] CStarMatrix (Fin 2) (Fin 2) B :=
  (diagonalStarAlgHom (Fin 2)).comp
    { AlgHom.pi ![ρ.toAlgHom, θ.toAlgHom] with
      map_star' x := by
        ext i
        fin_cases i <;> simp
        · exact map_star ρ x
        · exact map_star θ x }

@[simp]
theorem pairedRepresentation_apply (ρ θ : A →⋆ₐ[ℂ] B) (x : A) :
    pairedRepresentation ρ θ x = blockDiagonal (ρ x) (θ x) := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixAveraging
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.MatrixSiteWord.eval_append _root_.OAI.KadisonKastler.MatrixSiteWord.eval_cons _root_.OAI.KadisonKastler.MatrixSiteWord.eval_nil _root_.OAI.KadisonKastler.MatrixSiteWord.eval_reindex _root_.OAI.KadisonKastler.MatrixSiteWord.eval_star _root_.OAI.KadisonKastler.conjugatedMatrixUnits_entry _root_.OAI.KadisonKastler.matrixPermutationValue_one _root_.OAI.KadisonKastler.spatialMatrixUnits_entry _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Averaging over a concrete finite matrix algebra

Signed permutation matrices give a finite unitary group whose commutant
is exactly the commutant of the matrix-unit system. Its uniform average
preserves the original scalar derivation bound.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {ι A : Type*} [Fintype ι] [DecidableEq ι]
variable [Ring A]
  [StarRing A]
  [_root_.Algebra ℂ A]
  [StarModule ℂ A]

theorem matrixUnitSignedRepresentation_mem (E : Generator.MatrixUnitSystem ι A)
    (g : SignedPermutation ι) : (matrixUnitSignedRepresentation E g : A) ∈ E.algebra :=
  ⟨(signedPermutationHom g : Matrix ι ι ℂ), rfl⟩

theorem matrixUnitSignedRepresentation_inr (E : Generator.MatrixUnitSystem ι A)
    (σ : Equiv.Perm ι) :
    (matrixUnitSignedRepresentation E (SemidirectProduct.inr σ) : A) =
      E.hom (Matrix.permMatrixHom (R := ℂ) σ) := by
  change E.hom (signedPermutationHom (SemidirectProduct.inr σ) : Matrix ι ι ℂ) = _
  congr 1
  simp [signedPermutationHom, permutationHom, permutationUnitary]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TracialCauchySchwarz
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# Cauchy–Schwarz for the faithful tracial two-norm

The imaginary-part condition on positive squares gives the Hermitian
symmetry of the trace pairing by polarization. The existing algebraic
inner-product core then supplies Cauchy–Schwarz, without changing the
ambient C*-algebra norm.
-/

namespace KadisonKastler

noncomputable section

universe u

variable {B : Type u} [CStarAlgebra B]

/-- A positive complex-linear trace commutes with the involution. -/
theorem FaithfulTracialState.map_star (τ : FaithfulTracialState B) (x : B) :
    τ.toLinearMap (star x) = star (τ.toLinearMap x) := by
  simpa only [star_one, one_mul, mul_one] using (τ.star_pair_symm x 1).symm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ConcreteTraceTransfer
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Strong trace transfer in a concrete finite representation

A finite vector-functional formula for the trace is enough: weak
compactness of the positive operator ball and faithfulness prove the
uniform two-norm-to-strong implication. No transfer theorem is assumed.
-/

namespace KadisonKastler

open Filter
open scoped Topology BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

local instance concreteTraceOrder_rdab73d_1 : PartialOrder (Algebra M) := CStarAlgebra.spectralOrder _
local instance concreteTracePreorder_rdab73d_1 : Preorder (Algebra M) := (CStarAlgebra.spectralOrder _).toPreorder
local instance concreteTraceLE_rdab73d_1 : LE (Algebra M) := (CStarAlgebra.spectralOrder _).toLE
local instance concreteTraceStarOrder_rdab73d_1 : StarOrderedRing (Algebra M) := CStarAlgebra.spectralOrderedRing _
/-- A finite vector-functional formula, used below for the factor trace. -/
def FiniteVectorTrace (τ : FaithfulTracialState (Algebra M)) : Prop :=
  ∃ (n : ℕ) (ξ η : Fin n → H), ∀ a : Algebra M,
    τ.toLinearMap a = ∑ i, inner ℂ (η i) ((a : H →L[ℂ] H) (ξ i))

theorem FiniteVectorTrace.tendsto {τ : FaithfulTracialState (Algebra M)}
    (hτ : FiniteVectorTrace τ) {J : Type*} {l : Filter J}
    (a : J → Algebra M) (b : Algebra M)
    (h : ∀ ξ η, Tendsto (fun j => inner ℂ η ((a j : H →L[ℂ] H) ξ)) l
      (𝓝 (inner ℂ η ((b : H →L[ℂ] H) ξ)))) :
    Tendsto (fun j => τ.toLinearMap (a j)) l (𝓝 (τ.toLinearMap b)) := by
  obtain ⟨n, ξ, η, hrep⟩ := hτ
  simp_rw [hrep]
  exact tendsto_finsetSum Finset.univ (fun i _ => h (ξ i) (η i))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCoreOperators
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

/-- Multiplication of `L²` vectors by a measurable unitary field. -/
def regularUnitaryFieldApply (μ : Measure D) (U : D → unitary (H →L[ℂ] H))
    (hU : ∀ x, AEStronglyMeasurable (fun t => (U t : H →L[ℂ] H) x) μ)
    (f : Lp H 2 μ) : Lp H 2 μ :=
  ((Lp.memLp f).congr_norm
    (aestronglyMeasurable_field_apply (fun t => (U t : H →L[ℂ] H)) hU f
      (Lp.aestronglyMeasurable f))
    (Eventually.of_forall (fun t => (Unitary.norm_map (U t) (f t)).symm))).toLp _

theorem regularUnitaryFieldApply_ae (μ : Measure D)
    (U : D → unitary (H →L[ℂ] H))
    (hU : ∀ x, AEStronglyMeasurable (fun t => (U t : H →L[ℂ] H) x) μ)
    (f : Lp H 2 μ) :
    regularUnitaryFieldApply μ U hU f =ᵐ[μ] fun t => (U t : H →L[ℂ] H) (f t) :=
  MemLp.coeFn_toLp _

theorem norm_regularUnitaryFieldApply (μ : Measure D)
    (U : D → unitary (H →L[ℂ] H))
    (hU : ∀ x, AEStronglyMeasurable (fun t => (U t : H →L[ℂ] H) x) μ)
    (f : Lp H 2 μ) : ‖regularUnitaryFieldApply μ U hU f‖ = ‖f‖ := by
  have he : ∀ᵐ t ∂μ, ‖regularUnitaryFieldApply μ U hU f t‖ = ‖f t‖ :=
    (regularUnitaryFieldApply_ae μ U hU f).mono
      (fun t ht => by rw [ht, Unitary.norm_map])
  exact le_antisymm (Lp.norm_le_norm_of_ae_le (he.mono (fun _ h => h.le)))
    (Lp.norm_le_norm_of_ae_le (he.mono (fun _ h => h.ge)))

/-- The gauge operator as a genuine unitary on the regular Hilbert space. -/
def regularUnitaryField (μ : Measure D) (U : D → unitary (H →L[ℂ] H))
    (hU : ∀ x, AEStronglyMeasurable (fun t => (U t : H →L[ℂ] H) x) μ)
    (hUs : ∀ x, AEStronglyMeasurable (fun t => (star (U t) : H →L[ℂ] H) x) μ) :
    unitary (Lp H 2 μ →L[ℂ] Lp H 2 μ) :=
  Unitary.linearIsometryEquiv.symm
    { toFun := regularUnitaryFieldApply μ U hU
      invFun := regularUnitaryFieldApply μ (fun t => star (U t)) hUs
      map_add' f g := by
        apply Lp.ext
        filter_upwards [regularUnitaryFieldApply_ae μ U hU (f + g),
          regularUnitaryFieldApply_ae μ U hU f,
          regularUnitaryFieldApply_ae μ U hU g,
          Lp.coeFn_add f g,
          Lp.coeFn_add (regularUnitaryFieldApply μ U hU f)
            (regularUnitaryFieldApply μ U hU g)] with t hfg hf hg ha hb
        rw [hfg, ha, hb]
        simp only [Pi.add_apply]
        rw [hf, hg, map_add]
      map_smul' c f := by
        simp only [RingHom.id_apply]
        apply Lp.ext
        filter_upwards [regularUnitaryFieldApply_ae μ U hU (c • f),
          regularUnitaryFieldApply_ae μ U hU f, Lp.coeFn_smul c f,
          Lp.coeFn_smul c (regularUnitaryFieldApply μ U hU f)] with t hc hf ha hb
        rw [hc, ha, hb]
        simp only [Pi.smul_apply]
        rw [hf, map_smul]
      norm_map' := norm_regularUnitaryFieldApply μ U hU
      left_inv f := by
        apply Lp.ext
        filter_upwards [regularUnitaryFieldApply_ae μ (fun t => star (U t)) hUs
            (regularUnitaryFieldApply μ U hU f), regularUnitaryFieldApply_ae μ U hU f]
          with t hs hf
        rw [hs, hf]
        exact congrArg (fun R : H →L[ℂ] H => R (f t))
          (Unitary.star_mul_self_of_mem (U t).property)
      right_inv f := by
        apply Lp.ext
        filter_upwards [regularUnitaryFieldApply_ae μ U hU
            (regularUnitaryFieldApply μ (fun t => star (U t)) hUs f),
          regularUnitaryFieldApply_ae μ (fun t => star (U t)) hUs f]
          with t hU hUs
        rw [hU, hUs]
        exact congrArg (fun R : H →L[ℂ] H => R (f t))
          (Unitary.mul_star_self_of_mem (U t).property) }

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCoreRepresentation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

/-- Right translation of actual `L²` classes. -/
def regularTranslateApply (s : ℝ) (f : RegularCoreHilbert H) : RegularCoreHilbert H :=
  Lp.compMeasurePreserving (fun t : ℝ => t + s) (measurePreserving_add_right volume s) f

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
theorem regularTranslateApply_ae (s : ℝ) (f : RegularCoreHilbert H) :
    regularTranslateApply s f =ᵐ[volume] fun t => f (t + s) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_add_right volume s)

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
theorem regularTranslateApply_add (s t : ℝ) (f : RegularCoreHilbert H) :
    regularTranslateApply s (regularTranslateApply t f) = regularTranslateApply (s + t) f := by
  apply Lp.ext
  filter_upwards [regularTranslateApply_ae s (regularTranslateApply t f),
    (measurePreserving_add_right volume s).quasiMeasurePreserving.ae_eq_comp
      (regularTranslateApply_ae t f), regularTranslateApply_ae (s + t) f]
    with a hs ht hst
  simp only [Function.comp_def] at ht
  rw [hs, ht, hst, add_assoc]

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
theorem regularTranslateApply_zero (f : RegularCoreHilbert H) :
    regularTranslateApply 0 f = f := by
  apply Lp.ext
  filter_upwards [regularTranslateApply_ae 0 f] with t ht
  simpa only [add_zero] using ht

def regularTranslationEquiv (s : ℝ) : RegularCoreHilbert H ≃ₗᵢ[ℂ] RegularCoreHilbert H where
  __ := Lp.compMeasurePreservingₗᵢ ℂ
    (fun t : ℝ => t + s) (measurePreserving_add_right volume s)
  invFun := regularTranslateApply (-s)
  left_inv f := by
    change regularTranslateApply (-s) (regularTranslateApply s f) = f
    rw [regularTranslateApply_add, neg_add_cancel, regularTranslateApply_zero]
  right_inv f := by
    change regularTranslateApply s (regularTranslateApply (-s) f) = f
    rw [regularTranslateApply_add, add_neg_cancel, regularTranslateApply_zero]

/-- The concrete right-translation unitary `ρ_s ξ(t)=ξ(t+s)`. -/
def regularRightTranslation : Multiplicative ℝ →* unitary
    (RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) where
  toFun s := Unitary.linearIsometryEquiv.symm (regularTranslationEquiv s.toAdd)
  map_one' := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro f
    change regularTranslateApply (H := H) 0 f = f
    exact regularTranslateApply_zero f
  map_mul' s t := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro f
    change regularTranslateApply (s.toAdd + t.toAdd) f =
      regularTranslateApply s.toAdd (regularTranslateApply t.toAdd f)
    exact (regularTranslateApply_add s.toAdd t.toAdd f).symm

theorem regularRightTranslation_apply_ae (s : Multiplicative ℝ) (f : RegularCoreHilbert H) :
    (regularRightTranslation (H := H) s : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f =ᵐ[volume]
      fun t => f (t + s.toAdd) :=
  regularTranslateApply_ae s.toAdd f

/-- Constant operators commute with translations. -/
theorem regularConstant_commute_translation (T : H →L[ℂ] H) (s : Multiplicative ℝ) :
    Commute (regularConstantHom volume T)
      (regularRightTranslation (H := H) s : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) := by
  change regularConstantHom volume T *
      (regularRightTranslation (H := H) s : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) =
    (regularRightTranslation (H := H) s : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) *
      regularConstantHom volume T
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [regularConstantHom_apply_ae volume T
      ((regularRightTranslation (H := H) s : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f),
    regularRightTranslation_apply_ae s f,
    regularRightTranslation_apply_ae s (regularConstantHom volume T f),
    (measurePreserving_add_right volume s.toAdd).quasiMeasurePreserving.ae_eq_comp
      (regularConstantHom_apply_ae volume T f)] with t hc ht htc hct
  simp only [Function.comp_def] at hct
  change regularConstantHom volume T
      ((regularRightTranslation (H := H) s : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f) t =
    ((regularRightTranslation (H := H) s : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      (regularConstantHom volume T f)) t
  rw [hc, ht, htc, hct]

/-- The constant copy of a unitary as an actual unitary on `L²`. -/
def regularConstantUnitary : unitary (H →L[ℂ] H) →* unitary
    (RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) :=
  (Unitary.map (StarMonoidHom.ofClass (regularConstantHom (H := H) volume))).toMonoidHom

variable (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))

/-- Multiplication by `U_t`, as a unitary on the regular Hilbert space. -/
def regularGauge : unitary (RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) :=
  regularUnitaryField volume (fun t => U (Multiplicative.ofAdd t))
    (fun x => (hU x).aestronglyMeasurable) (regularGroup_star_measurable U hU)

/-- The regular embedding `π(x) = gauge* · constant(x) · gauge`. -/
def regularCoreEmbedding : (H →L[ℂ] H) →⋆ₐ[ℂ]
    (RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) :=
  ((Unitary.conjStarAlgAut ℂ _ (star (regularGauge U hU))).toStarAlgHom).comp
    (regularConstantHom volume)

/-- The common regular action `U_s ⊗ ρ_s`, without any fixed-point premise. -/
def regularCoreAction : Multiplicative ℝ →* unitary
    (RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) where
  toFun s := regularConstantUnitary (U s) * regularRightTranslation (H := H) s
  map_one' := by simp only [map_one, one_mul]
  map_mul' s t := by
    simp only [map_mul]
    have hc : Commute (regularRightTranslation (H := H) s)
        (regularConstantUnitary (U t)) := by
      change regularRightTranslation (H := H) s * regularConstantUnitary (U t) =
        regularConstantUnitary (U t) * regularRightTranslation (H := H) s
      apply Subtype.ext
      change (regularRightTranslation (H := H) s :
          RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) *
          regularConstantHom volume (U t : H →L[ℂ] H) =
        regularConstantHom volume (U t : H →L[ℂ] H) *
          (regularRightTranslation (H := H) s : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      exact (regularConstant_commute_translation (U t : H →L[ℂ] H) s).symm.eq
    exact (hc.mul_mul_mul_comm (regularConstantUnitary (U s))
      (regularRightTranslation (H := H) t)).symm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularActionCocycle
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Unitary cocycles between represented modular actions

These are the cocycles occurring in the change-of-state theorem. The
construction of a cocycle from two faithful states is a separate step.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

structure ModularActionCocycle (M : VonNeumannAlgebra H)
    (U V : Multiplicative ℝ →* unitary (H →L[ℂ] H)) where
  value : Multiplicative ℝ → unitary (H →L[ℂ] H)
  mem : ∀ s, (value s : H →L[ℂ] H) ∈ M
  continuous : ∀ x, Continuous (fun t : ℝ => (value (Multiplicative.ofAdd t) : H →L[ℂ] H) x)
  continuous_star : ∀ x, Continuous
    (fun t : ℝ => (star (value (Multiplicative.ofAdd t)) : H →L[ℂ] H) x)
  value_mul : ∀ s t, (value (s * t) : H →L[ℂ] H) =
    (value s : H →L[ℂ] H) * unitaryConj (U s) (value t : H →L[ℂ] H)
  action : ∀ s a, a ∈ M → unitaryConj (V s) a =
    unitaryConj (value s) (unitaryConj (U s) a)

namespace ModularActionCocycle

variable {M : VonNeumannAlgebra H}
  {U V : Multiplicative ℝ →* unitary (H →L[ℂ] H)}
  (c : ModularActionCocycle M U V)

theorem star_unitaryConj (u : unitary (H →L[ℂ] H)) (a : H →L[ℂ] H) :
    star (unitaryConj u a) = unitaryConj u (star a) := by
  simp only [unitaryConj, star_mul, star_star, mul_assoc]

def symm : ModularActionCocycle M V U where
  value s := star (c.value s)
  mem s := star_mem (c.mem s)
  continuous := c.continuous_star
  continuous_star x := by simpa only [Unitary.coe_star, star_star] using c.continuous x
  value_mul s t := by
    have h := congrArg star (c.value_mul s t)
    rw [star_mul, star_unitaryConj] at h
    change star (c.value (s * t) : H →L[ℂ] H) =
      star (c.value s : H →L[ℂ] H) * unitaryConj (V s) (star (c.value t : H →L[ℂ] H))
    rw [c.action s _ (star_mem (c.mem t)), h]
    simp only [unitaryConj, ← mul_assoc,
      Unitary.star_mul_self_of_mem (c.value s).property, one_mul]
  action s a ha := by
    have h := congrArg (unitaryConj (star (c.value s))) (c.action s a ha)
    rw [unitaryConj_star_unitaryConj] at h
    exact h.symm

def regularField (t : ℝ) : unitary (H →L[ℂ] H) :=
  c.value (Multiplicative.ofAdd (-t))

theorem regularField_measurable (x : H) :
    AEStronglyMeasurable (fun t => (c.regularField t : H →L[ℂ] H) x) volume :=
  ((c.continuous x).comp continuous_neg).aestronglyMeasurable

theorem regularField_star_measurable (x : H) :
    AEStronglyMeasurable (fun t => (star (c.regularField t) : H →L[ℂ] H) x) volume :=
  ((c.continuous_star x).comp continuous_neg).aestronglyMeasurable

end ModularActionCocycle

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCoreCharacters
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

/-- The multiplication unitary `Q_a ξ(t) = exp(i a t) ξ(t)`. -/
def regularCharacterUnitary (a : ℝ) :
    unitary (RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) :=
  regularUnitaryField volume (regularCharacterFiber (H := H) a)
    (regularCharacterFiber_measurable a) (regularCharacterFiber_star_measurable a)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SequentialConjugacyTests
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Sequential tests for the measurable conjugacy relation

Each represented algebra on a separable Hilbert space has an actual
sequence of contractions whose range is strongly dense in its unit ball.
Conjugacy is exactly two countable families of finite-vector tests.
-/

namespace KadisonKastler

open Filter TopologicalSpace
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

structure StrongUnitBallTestSequence (M : VonNeumannAlgebra H) where
  op : ℕ → H →L[ℂ] H
  mem : ∀ n, op n ∈ unitBall M
  dense : ∀ x ∈ unitBall M, ∃ T : ℕ → H →L[ℂ] H,
    (∀ n, T n ∈ Set.range op) ∧ ∀ ξ, Tendsto (fun n => T n ξ) atTop (𝓝 (x ξ))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCoreFields
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Bounded field multiplication and constant translation-fixed fields

Bounded measurable operator fields act on the actual vector-valued `L²`
space. Finite-measure indicator tests recover their coefficients, so this
action is faithful modulo almost-everywhere equality. A decomposable
operator commuting with every real translation is a constant operator.
No decomposability assertion for an arbitrary operator is assumed here.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Topology ENNReal

noncomputable section

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem regularField_memLp (μ : Measure X) (F : X → H →L[ℂ] H)
    (hF : ∀ ξ, AEStronglyMeasurable (fun t => F t ξ) μ)
    (C : ℝ) (hC : ∀ᵐ t ∂μ, ‖F t‖ ≤ C) (f : Lp H 2 μ) :
    MemLp (fun t => F t (f t)) 2 μ := by
  apply ((Lp.memLp f).norm.const_mul C).mono'
    (aestronglyMeasurable_field_apply F hF f (Lp.aestronglyMeasurable f))
  filter_upwards [hC] with t ht
  exact ((F t).le_opNorm _).trans (mul_le_mul_of_nonneg_right ht (norm_nonneg _))

def regularFieldApply (μ : Measure X) (F : X → H →L[ℂ] H)
    (hF : ∀ ξ, AEStronglyMeasurable (fun t => F t ξ) μ)
    (C : ℝ) (hC : ∀ᵐ t ∂μ, ‖F t‖ ≤ C) (f : Lp H 2 μ) : Lp H 2 μ :=
  (regularField_memLp μ F hF C hC f).toLp _

omit [CompleteSpace H] in
theorem regularFieldApply_ae (μ : Measure X) (F : X → H →L[ℂ] H)
    (hF : ∀ ξ, AEStronglyMeasurable (fun t => F t ξ) μ)
    (C : ℝ) (hC : ∀ᵐ t ∂μ, ‖F t‖ ≤ C) (f : Lp H 2 μ) :
    regularFieldApply μ F hF C hC f =ᵐ[μ] fun t => F t (f t) :=
  MemLp.coeFn_toLp _

omit [CompleteSpace H] in
theorem norm_regularFieldApply_le (μ : Measure X) (F : X → H →L[ℂ] H)
    (hF : ∀ ξ, AEStronglyMeasurable (fun t => F t ξ) μ)
    (C : ℝ) (hC : ∀ᵐ t ∂μ, ‖F t‖ ≤ C) (f : Lp H 2 μ) :
    ‖regularFieldApply μ F hF C hC f‖ ≤ C * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [regularFieldApply_ae μ F hF C hC f, hC] with t ht hnorm
  rw [ht]
  exact ((F t).le_opNorm _).trans (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _))

/-- Multiplication by an essentially bounded, strongly measurable
operator field, as a genuine bounded operator. -/
def regularFieldOperator (μ : Measure X) (F : X → H →L[ℂ] H)
    (hF : ∀ ξ, AEStronglyMeasurable (fun t => F t ξ) μ)
    (C : ℝ) (hC : ∀ᵐ t ∂μ, ‖F t‖ ≤ C) : Lp H 2 μ →L[ℂ] Lp H 2 μ :=
  LinearMap.mkContinuous
    { toFun := regularFieldApply μ F hF C hC
      map_add' f g := by
        apply Lp.ext
        filter_upwards [regularFieldApply_ae μ F hF C hC (f + g),
          regularFieldApply_ae μ F hF C hC f, regularFieldApply_ae μ F hF C hC g,
          Lp.coeFn_add f g,
          Lp.coeFn_add (regularFieldApply μ F hF C hC f)
            (regularFieldApply μ F hF C hC g)] with t hfg hf hg ha hb
        rw [hfg, hb, ha]
        simp only [Pi.add_apply]
        rw [hf, hg, map_add]
      map_smul' c f := by
        simp only [RingHom.id_apply]
        apply Lp.ext
        filter_upwards [regularFieldApply_ae μ F hF C hC (c • f),
          regularFieldApply_ae μ F hF C hC f, Lp.coeFn_smul c f,
          Lp.coeFn_smul c (regularFieldApply μ F hF C hC f)] with t hc hf ha hb
        rw [hc, hb, ha]
        simp only [Pi.smul_apply]
        rw [hf, map_smul] }
    C (norm_regularFieldApply_le μ F hF C hC)

omit [CompleteSpace H] in
theorem regularFieldOperator_represents (μ : Measure X) (F : X → H →L[ℂ] H)
    (hF : ∀ ξ, AEStronglyMeasurable (fun t => F t ξ) μ)
    (C : ℝ) (hC : ∀ᵐ t ∂μ, ‖F t‖ ≤ C) :
    RepresentsOperatorField μ F (regularFieldOperator μ F hF C hC) :=
  regularFieldApply_ae μ F hF C hC

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PublishedRegularDiagonal
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Published spectral and diagonal decomposition inputs

The two inputs are kept separate. Blackadar, *Operator Algebras* (2006),
I.7.4.5--7 and I.7.4.10 (printed pp.35--37), gives the spectral-commutant
consequence of Stone's theorem: the commutant of multiplication by
`exp(i a t)`, for all real `a`, commutes with every bounded Borel multiplier.
Here the generator is multiplication by the coordinate `t`.

III.1.6.2--3 (printed pp.253--254) gives the diagonal-commutant decomposition
on the standard trivial field over the real line. Its conclusion is only
the existence of a measurable bounded operator field representing an
operator. Neither input asserts a core or fixed-point identification.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The actual multiplication operator associated to a bounded Borel
scalar function on the real line. -/
def regularScalarMultiplier (φ : ℝ → ℂ) (hφ : Measurable φ)
    (C : ℝ) (hC : ∀ t, ‖φ t‖ ≤ C) :
    RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H :=
  regularFieldOperator volume (fun t => φ t • (1 : H →L[ℂ] H))
    (fun ξ => hφ.aestronglyMeasurable.smul_const ξ) C
    (Filter.Eventually.of_forall fun t => by
      apply le_trans _ (hC t)
      apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
      intro ξ
      simp only [smul_apply, one_apply_eq_self, norm_smul]
      exact le_rfl)

/-- Stone's spectral-commutant theorem, restricted to the concrete
character multiplication group on the real line. -/
def PublishedRealSpectralCommutant : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
    ∀ T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H,
      (∀ a : ℝ, Commute T (regularCharacterUnitary (H := H) a :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)) →
      ∀ (φ : ℝ → ℂ) (hφ : Measurable φ) (C : ℝ) (hC : ∀ t, ‖φ t‖ ≤ C),
        Commute T (regularScalarMultiplier (H := H) φ hφ C hC)

/-- The diagonal-commutant decomposition theorem on a separable constant
Hilbert field over Lebesgue measure. -/
def PublishedRealDiagonalDecomposition : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H],
    ∀ T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H,
      (∀ (φ : ℝ → ℂ) (hφ : Measurable φ) (C : ℝ) (hC : ∀ t, ‖φ t‖ ≤ C),
        Commute T (regularScalarMultiplier (H := H) φ hφ C hC)) →
      ∃ F : ℝ → H →L[ℂ] H,
        (∀ ξ, AEStronglyMeasurable (fun t => F t ξ) volume) ∧
        (∀ᵐ t ∂volume, ‖F t‖ ≤ ‖T‖) ∧ RepresentsOperatorField volume F T

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FrequencyNest
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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

/-- Multiplication by the indicator of a measurable subset of the line. -/
def regularIndicatorProjection (s : Set ℝ) (hs : MeasurableSet s) :
    RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H :=
  regularScalarMultiplier (s.indicator fun _ => (1 : ℂ))
    (measurable_const.indicator hs) 1 (by
      intro t
      by_cases ht : t ∈ s <;> simp [ht])

omit [CompleteSpace H] in
theorem regularIndicatorProjection_apply_ae (s : Set ℝ) (hs : MeasurableSet s)
    (f : RegularCoreHilbert H) :
    regularIndicatorProjection s hs f =ᵐ[volume] s.indicator f := by
  filter_upwards [regularFieldOperator_represents volume
    (fun t => (s.indicator (fun _ => (1 : ℂ))) t • (1 : H →L[ℂ] H))
    (fun ξ => (measurable_const.indicator hs).aestronglyMeasurable.smul_const ξ)
    1 (show ∀ᵐ t : ℝ, ‖(s.indicator (fun _ => (1 : ℂ))) t • (1 : H →L[ℂ] H)‖ ≤ 1 from
      Filter.Eventually.of_forall fun t => by
        by_cases ht : t ∈ s
        · simp only [Set.indicator_of_mem ht, one_smul]
          exact ContinuousLinearMap.norm_id_le
        · simp [ht]) f] with t ht
  change regularIndicatorProjection s hs f t = _ at ht
  rw [ht]
  by_cases h : t ∈ s <;> simp [h]

omit [CompleteSpace H] in
theorem regularIndicatorProjection_mul_of_subset (s t : Set ℝ)
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hst : s ⊆ t) :
    regularIndicatorProjection (H := H) s hs * regularIndicatorProjection t ht =
      regularIndicatorProjection s hs := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [regularIndicatorProjection_apply_ae s hs
      (regularIndicatorProjection t ht f),
    regularIndicatorProjection_apply_ae t ht f,
    regularIndicatorProjection_apply_ae s hs f] with x h₁ h₂ h₃
  change regularIndicatorProjection s hs (regularIndicatorProjection t ht f) x =
    regularIndicatorProjection s hs f x
  rw [h₁, h₃]
  by_cases hx : x ∈ s
  · simp only [Set.indicator_of_mem hx]
    rw [h₂, Set.indicator_of_mem (hst hx)]
  · simp only [Set.indicator_of_notMem hx]

theorem regularIndicatorProjection_isStarProjection (s : Set ℝ) (hs : MeasurableSet s) :
    IsStarProjection (regularIndicatorProjection (H := H) s hs) := by
  refine ⟨regularIndicatorProjection_mul_of_subset s s hs hs Set.Subset.rfl, ?_⟩
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro f g
  change inner ℂ (regularIndicatorProjection s hs f) g =
    inner ℂ f (regularIndicatorProjection s hs g)
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [regularIndicatorProjection_apply_ae s hs f,
    regularIndicatorProjection_apply_ae s hs g] with x hf hg
  rw [hf, hg]
  by_cases hx : x ∈ s <;> simp [hx]

/-- The positive-frequency cut of the actual `L²` Fourier transform. -/
def regularFrequencyProjection (a : ℝ) :
    RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H :=
  (Lp.fourierTransformₗᵢ ℝ H).symm.conjStarAlgEquiv
    (regularIndicatorProjection (Set.Ioi (a / (2 * Real.pi))) measurableSet_Ioi)

theorem regularFrequencyProjection_isStarProjection (a : ℝ) :
    IsStarProjection (regularFrequencyProjection (H := H) a) :=
  (regularIndicatorProjection_isStarProjection (H := H)
    (Set.Ioi (a / (2 * Real.pi))) measurableSet_Ioi).map
      (Lp.fourierTransformₗᵢ ℝ H).symm.conjStarAlgEquiv

/-- Reindexing the upper cuts produces an increasing real-indexed nest. -/
def regularFrequencyNest (a : ℝ) :
    RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H := regularFrequencyProjection (-a)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_InvariantOperatorMean
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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

attribute [local instance] OAI.KadisonKastler.ScalarInvariantMean.invariantMeanFamilyStarOrder
/-- The orbit family of an operator under an actual unitary representation. -/
def conjugationFamily (U : G →* unitary (H →L[ℂ] H)) (T : H →L[ℂ] H) :
    G →ᵇ (H →L[ℂ] H) :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun g => unitaryConj (U g) T) ‖T‖ (fun _ => (norm_unitaryConj _ _).le)

@[simp] theorem conjugationFamily_apply (U : G →* unitary (H →L[ℂ] H))
    (T : H →L[ℂ] H) (g : G) : conjugationFamily U T g = unitaryConj (U g) T := rfl

end ScalarInvariantMean

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PublishedNestDistance
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The published nest distance input and its invariant approximant

William Arveson, *Interpolation problems in nest algebras*, J. Functional
Analysis 20 (1975), 208–233, Theorem 1.1, p.212, with the finite-chain
reduction in its proof and Lemma 1, p.209. We retain only its upper distance
bound for a real-indexed increasing family of orthogonal projections.
Adjoining strong limits, zero and identity does not change the algebra
or the upper bound. No analytic multiplier or perturbation conclusion
is included in the published input.
-/

namespace KadisonKastler

noncomputable section

universe u

/-- The approximation consequence of Arveson's nest distance formula,
with explicit slack instead of a nearest-point assertion. -/
def PublishedRealNestDistance : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
    ∀ (P : ℝ → H →L[ℂ] H), (∀ a, IsStarProjection (P a)) →
      (∀ a b, a ≤ b → P a * P b = P a) →
      ∀ (T : H →L[ℂ] H) (δ η : ℝ), 0 ≤ δ → 0 < η →
      (∀ a, ‖(1 - P a) * T * P a‖ ≤ δ) →
      ∃ S : H →L[ℂ] H, PreservesProjectionNest P S ∧ ‖S - T‖ < δ + η

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCoreHilbertSum
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Scalar Hilbert coordinates on the regular representation

A scalar Hilbert basis of `L²(ℝ)` gives an actual Hilbert direct-sum
decomposition of `L²(ℝ,H)`. Constant operators act on each summand by
their original action on `H`.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace ENNReal

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- An elementary scalar-vector tensor, as a continuous bilinear map. -/
def regularTensorVector :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] H →L[ℂ] RegularCoreHilbert H :=
  ((ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] H →L[ℂ] H).flip.compLpL₂
    2 (volume : Measure ℝ)).flip

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ReducingRestriction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Restriction to a reducing subspace and finite coefficients

The restriction of a star algebra to a closed invariant subspace is an
actual star homomorphism. Extending a corner unitary by the identity
preserves the coefficients of its conjugation on that subspace.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (K : Submodule ℂ H) [CompleteSpace K]

omit [CompleteSpace H] in
theorem cornerCompression_coe_of_invariant (T : H →L[ℂ] H)
    (hT : ∀ x ∈ K, T x ∈ K) (x : K) :
    (cornerCompression K T x : H) = T x := by
  change K.starProjection (T x) = T x
  exact Submodule.starProjection_eq_self_iff.mpr (hT x x.property)

omit [CompleteSpace H] in
theorem cornerCompression_mul_of_invariant (T S : H →L[ℂ] H)
    (hS : ∀ x ∈ K, S x ∈ K) :
    cornerCompression K (T * S) = cornerCompression K T * cornerCompression K S := by
  apply ContinuousLinearMap.ext
  intro x
  change K.orthogonalProjectionOnto (T (S x)) =
    K.orthogonalProjectionOnto (T (cornerCompression K S x : H))
  rw [cornerCompression_coe_of_invariant K S hS x]

theorem cornerCompression_star (T : H →L[ℂ] H) :
    cornerCompression K (star T) = star (cornerCompression K T) := by
  simp only [cornerCompression, LinearMap.coe_mk, AddHom.coe_mk,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_comp,
    Submodule.adjoint_subtypeL, Submodule.adjoint_orthogonalProjectionOnto,
    ContinuousLinearMap.comp_assoc]

/-- Restriction to a closed subspace invariant under the given star algebra. -/
def reducingRestriction (A : StarSubalgebra ℂ (H →L[ℂ] H))
    (hA : ∀ a : A, ∀ x ∈ K, (a : H →L[ℂ] H) x ∈ K) :
    A →⋆ₐ[ℂ] (K →L[ℂ] K) where
  toFun a := cornerCompression K a.val
  map_zero' := map_zero (cornerCompression K)
  map_one' := by
    apply ContinuousLinearMap.ext
    intro x
    change K.orthogonalProjectionOnto (x : H) = x
    exact K.orthogonalProjectionOnto_mem_subspace_eq_self x
  map_add' a b := map_add (cornerCompression K) a.val b.val
  map_mul' a b := cornerCompression_mul_of_invariant K a.val b.val (hA b)
  commutes' c := by
    apply ContinuousLinearMap.ext
    intro x
    change K.orthogonalProjectionOnto (c • (x : H)) = c • x
    rw [map_smul, K.orthogonalProjectionOnto_mem_subspace_eq_self]
  map_star' a := cornerCompression_star K a.val

@[simp] theorem reducingRestriction_coe_apply (A : StarSubalgebra ℂ (H →L[ℂ] H))
    (hA : ∀ a : A, ∀ x ∈ K, (a : H →L[ℂ] H) x ∈ K)
    (a : A) (x : K) :
    (reducingRestriction K A hA a x : H) = (a : H →L[ℂ] H) x :=
  cornerCompression_coe_of_invariant K a.val (hA a) x

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.TracialSplitting_SpatialTensor
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.leftTensorVector_apply _root_.OAI.KadisonKastler.norm_tensorVector_apply _root_.OAI.KadisonKastler.rightTensorSlice_apply _root_.OAI.KadisonKastler.spatialIsometry_tmul _root_.OAI.KadisonKastler.spatialMap_id _root_.OAI.KadisonKastler.spatialMap_tmul _root_.OAI.KadisonKastler.spatialMatrixUnits_entry _root_.OAI.KadisonKastler.tensorVectorSlice_apply _root_.OAI.KadisonKastler.tensorVector_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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

lemma spatialTensorOp_norm_le (S : H →L[ℂ] H) (T : K →L[ℂ] K) :
    ‖spatialTensorOp S T‖ ≤ ‖S‖ * ‖T‖ :=
  (completion_opNorm_le (TensorProduct.mapL S T)).trans (TensorProduct.norm_mapL_le S T)

end UnitalTomsWinter

noncomputable section

namespace Pureness

open UnitalTomsWinter

open scoped TensorProduct InnerProductSpace

variable {A : Type uA} {B : Type uB} {H : Type uH} {K : Type uK} [CStarAlgebra A] [CStarAlgebra B]

variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable (α : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (β : B →⋆ₐ[ℂ] (K →L[ℂ] K))

lemma spatialLeftRight_commute (a : A) (b : B) :
    Commute (spatialLeftHom (K := K) α a) (spatialRightHom (H := H) β b) := by
  change spatialTensorOp (α a) 1 * spatialTensorOp 1 (β b) =
    spatialTensorOp 1 (β b) * spatialTensorOp (α a) 1
  rw [← spatialTensorOp_mul,← spatialTensorOp_mul]
  simp

end Pureness

end

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
-- module Solutions.OAIQ075_KS.KadisonKastler_SpatialProduct
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The concrete spatial tensor product used in the fixed-factor reduction

The spatial von Neumann algebra is the bicommutant of the bounded tensor
operators. Vector slices act on the completed tensor Hilbert space.
-/

namespace KadisonKastler

open UnitalTomsWinter
open scoped TensorProduct InnerProductSpace

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The spatial von Neumann tensor product in the given representations. -/
def spatialProductAlgebra (M : VonNeumannAlgebra H) (D : VonNeumannAlgebra K) :
    VonNeumannAlgebra (SpatialHilbert H K) :=
  generatedVonNeumannAlgebra
    ((M.toStarSubalgebra.map spatialLeft) ⊔ (D.toStarSubalgebra.map spatialRight))

theorem spatialLeft_mem_product (M : VonNeumannAlgebra H) (D : VonNeumannAlgebra K)
    {x : H →L[ℂ] H} (hx : x ∈ M) :
    spatialLeft (K := K) x ∈ spatialProductAlgebra M D := by
  let A : StarSubalgebra ℂ (SpatialHilbert H K →L[ℂ] SpatialHilbert H K) :=
    M.toStarSubalgebra.map (spatialLeft (H := H) (K := K))
  let B : StarSubalgebra ℂ (SpatialHilbert H K →L[ℂ] SpatialHilbert H K) :=
    D.toStarSubalgebra.map (spatialRight (H := H) (K := K))
  apply subset_generatedVonNeumannAlgebra (A ⊔ B)
  have hx' : spatialLeft (K := K) x ∈ A := ⟨x, hx, rfl⟩
  exact (show A ≤ A ⊔ B from le_sup_left) hx'

theorem spatialRight_mem_product (M : VonNeumannAlgebra H) (D : VonNeumannAlgebra K)
    {x : K →L[ℂ] K} (hx : x ∈ D) :
    spatialRight (H := H) x ∈ spatialProductAlgebra M D := by
  let A : StarSubalgebra ℂ (SpatialHilbert H K →L[ℂ] SpatialHilbert H K) :=
    M.toStarSubalgebra.map (spatialLeft (H := H) (K := K))
  let B : StarSubalgebra ℂ (SpatialHilbert H K →L[ℂ] SpatialHilbert H K) :=
    D.toStarSubalgebra.map (spatialRight (H := H) (K := K))
  apply subset_generatedVonNeumannAlgebra (A ⊔ B)
  have hx' : spatialRight (H := H) x ∈ B := ⟨x, hx, rfl⟩
  exact (show B ≤ A ⊔ B from le_sup_right) hx'

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SpatialAssociatorTransport
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Tensoring Hilbert-space identifications

An isometric equivalence in either Hilbert tensor leg lifts to the
completed tensor product. Conjugation by this equivalence transports
both the bounded tensor operators and their generated spatial algebras.
-/

namespace KadisonKastler

open UnitalTomsWinter
open scoped TensorProduct

noncomputable section

variable {H K H' K' : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
  [NormedAddCommGroup K'] [InnerProductSpace ℂ K']

variable [CompleteSpace H] [CompleteSpace K] [CompleteSpace H'] [CompleteSpace K']

/-- Transport commutes with taking the generated concrete von Neumann algebra. -/
theorem spatialTransport_generated
    (f : H ≃ₗᵢ[ℂ] H') (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    spatialTransportAlgebra f (generatedVonNeumannAlgebra S) =
      generatedVonNeumannAlgebra (S.map f.conjStarAlgEquiv.toStarAlgHom) := by
  apply SetLike.coe_injective
  change f.conjStarAlgEquiv '' (generatedVonNeumannAlgebra S : Set (H →L[ℂ] H)) =
    (generatedVonNeumannAlgebra (S.map f.conjStarAlgEquiv.toStarAlgHom) :
      Set (H' →L[ℂ] H'))
  rw [generatedVonNeumannAlgebra_coe, generatedVonNeumannAlgebra_coe]
  change f.conjStarAlgEquiv '' Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))) =
    Set.centralizer (Set.centralizer (f.conjStarAlgEquiv '' (S : Set (H →L[ℂ] H))))
  rw [centralizer_image_spatial, centralizer_image_spatial]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCoreAlgebra
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The concrete regular core and its first fixed-point inclusion

The tensor algebra is the commutant of the constant copy of `P'` on
`L²(ℝ,H)`. The regular core is the von Neumann algebra generated by the
concrete regular embedding and translations. Its generators lie in the
tensor algebra and are fixed by the common regular action. This proves
the first fixed-point inclusion without a crossed-product assumption.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))

/-- The actual generating set of the regular core. -/
def regularCoreGenerators (P : VonNeumannAlgebra H) :
    Set (RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) :=
  regularCoreEmbedding U hU '' (P : Set (H →L[ℂ] H)) ∪
    Set.range (fun s => (regularRightTranslation (H := H) s :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H))

/-- The von Neumann algebra generated by the regular representation. -/
def regularCoreAlgebra (P : VonNeumannAlgebra H) :
    VonNeumannAlgebra (RegularCoreHilbert H) :=
  generatedVonNeumannAlgebra (StarAlgebra.adjoin ℂ (regularCoreGenerators U hU P))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CocycleCoreTransport
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Concrete core isomorphisms from unitary cocycles -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}
  {U V : Multiplicative ℝ →* unitary (H →L[ℂ] H)}

namespace ModularActionCocycle

variable (c : ModularActionCocycle M U V)

def gauge : unitary (RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) :=
  regularUnitaryField volume c.regularField c.regularField_measurable c.regularField_star_measurable

end ModularActionCocycle

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixVonNeumann
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The concrete von Neumann algebra of finite matrices

The commutant of the diagonal copy of `M'` consists exactly of the
operators all of whose matrix entries lie in `M`. This identifies it with
the usual C⋆-matrix algebra, including the represented normalized trace.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

/-- Pull a faithful tracial state back along a star-algebra equivalence. -/
def FaithfulTracialState.comapStarAlgEquiv {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    (τ : FaithfulTracialState B) (e : A ≃⋆ₐ[ℂ] B) : FaithfulTracialState A where
  toLinearMap := τ.toLinearMap.comp e.toAlgEquiv.toLinearMap
  map_one := by
    change τ.toLinearMap (e 1) = 1
    rw [_root_.map_one, τ.map_one]
  positive x := by
    change 0 ≤ (τ.toLinearMap (e (star x * x))).re
    rw [_root_.map_mul e, StarHomClass.map_star e]
    exact τ.positive _
  positive_im x := by
    change (τ.toLinearMap (e (star x * x))).im = 0
    rw [_root_.map_mul e, StarHomClass.map_star e]
    exact τ.positive_im _
  faithful x hx := by
    change τ.toLinearMap (e (star x * x)) = 0 at hx
    rw [_root_.map_mul e, StarHomClass.map_star e] at hx
    have he := congrArg e.symm (τ.faithful _ hx)
    simpa only [e.symm_apply_apply, _root_.map_zero] using he
  tracial x y := by
    change τ.toLinearMap (e (x * y)) = τ.toLinearMap (e (y * x))
    rw [_root_.map_mul e, _root_.map_mul e]
    exact τ.tracial _ _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PublishedCorrection
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# The published multiplication-correction input

`PublishedMultiplicationCorrection` is the application of Ricard--Roydor,
*A non-commutative Amir--Cambern theorem for von Neumann algebras and
nuclear C*-algebras*, J. Funct. Anal. 267 (2014), Proposition 3.2
(arXiv:1108.1970v2), to associative, involution-compatible products on a
concrete von Neumann algebra. It is an explicit hypothesis, not an axiom.

The downstream theorem constructs the corrected star-algebra equivalence
and proves the `32e` complete bound. Surjectivity of the original map and
spatial implementation are treated separately.
-/

namespace KadisonKastler

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance instPartialOrderSubtypeContinuousLinearMapComplexIdMemStarSubalgebraAlgebra (M : VonNeumannAlgebra H) : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _

local instance instStarOrderedRingSubtypeContinuousLinearMapComplexIdMemStarSubalgebraAlgebra (M : VonNeumannAlgebra H) : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _

/-- The precise published input used for correction. No normality is
required of the perturbed multiplication or of the correcting map. -/
def PublishedMultiplicationCorrection (M : VonNeumannAlgebra H) : Prop :=
  ∀ m : Algebra M →ₗ[ℂ] Algebra M →ₗ[ℂ] Algebra M,
    (∀ x y z, m (m x y) z = m x (m y z)) →
    (∀ x y, star (m x y) = m (star y) (star x)) →
    ∀ q : ℝ, 0 ≤ q → q ≤ 1 / 11 →
      HaagerupBound (m - LinearMap.mul ℂ (Algebra M)) q →
      ∃ L : Algebra M ≃ₗ[ℂ] Algebra M,
        (∀ x y, L (m x y) = L x * L y) ∧
        (∀ x, L (star x) = star (L x)) ∧
        CompletelyBoundedBy (L.toLinearMap - LinearMap.id) (10 * q)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CommonCenterReduction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Removing the common-center premise

Center alignment reduces unrestricted separable stability to stability
for algebras with a common center, with explicit tolerance estimates.
-/

namespace KadisonKastler

open TopologicalSpace

noncomputable section

universe u

/-- Strong stability for algebras with a common center, uniform over
separable Hilbert-space representations. -/
def CommonCenterSeparableStability : Prop :=
  ∀ a : ℝ, 0 < a → ∃ δ : ℝ, 0 < δ ∧
    ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] [SeparableSpace H], ∀ M N : VonNeumannAlgebra H,
        concreteCenter M = concreteCenter N →
        kkDistance M N < δ → NearConjugacy M N a

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CompleteLinearLimits
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Scalar and limit consequences of complete bounds -/

namespace KadisonKastler

noncomputable section

open Filter Topology

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- The row-column bound includes the scalar bilinear bound. -/
theorem HaagerupBound.apply_norm_le {f : A →ₗ[ℂ] A →ₗ[ℂ] A} {c : ℝ}
    (hf : HaagerupBound f c) (x y : A) : ‖f x y‖ ≤ c * ‖x‖ * ‖y‖ := by
  have h := hf 1 1 1 (scalarMatrixCopy x) (scalarMatrixCopy y)
  have he : bilinearProduct f (scalarMatrixCopy x) (scalarMatrixCopy y) =
      scalarMatrixCopy (f x y) := by
    ext i j
    simp only [bilinearProduct_apply, scalarMatrixCopy_apply, Fin.sum_univ_one]
  simpa only [he, scalarMatrixCopy_norm] using h

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ConcreteTraceUniqueness
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

section Positive

variable [PartialOrder B] [StarOrderedRing B]

theorem FaithfulTracialState.nonneg (τ : FaithfulTracialState B) {x : B} (hx : 0 ≤ x) :
    0 ≤ (τ.toLinearMap x).re := by
  have h := τ.positive (CFC.sqrt x)
  rwa [(CFC.sqrt_nonneg x).isSelfAdjoint.star_eq, CFC.sqrt_mul_sqrt_self x hx] at h

end Positive

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ConjugateFactor
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.ScalarInvariantMean.conjugationFamily_apply _root_.OAI.KadisonKastler.matrixAlgebraEquiv_apply _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.spatialTransportEquiv_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Factor transport and composition for a conjugated neighbor -/

namespace KadisonKastler

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The inner automorphism restricted to the original algebra. -/
def unitaryConjugateHom (w : unitary (H →L[ℂ] H)) (N : VonNeumannAlgebra H) :
    Algebra N →⋆ₐ[ℂ] Algebra (unitaryConjugateAlgebra w N) :=
  ((Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) w).toStarAlgHom.comp
    N.toStarSubalgebra.subtype).codRestrict
      (unitaryConjugateAlgebra w N).toStarSubalgebra (fun x => ⟨x.val, x.property, rfl⟩)

@[simp]
theorem unitaryConjugateHom_apply (w : unitary (H →L[ℂ] H))
    (N : VonNeumannAlgebra H) (x : Algebra N) :
    (unitaryConjugateHom w N x : H →L[ℂ] H) = unitaryConj w x := rfl

theorem unitaryConjugateHom_bijective (w : unitary (H →L[ℂ] H))
    (N : VonNeumannAlgebra H) : Function.Bijective (unitaryConjugateHom w N) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply (Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) w).injective
    exact congrArg Subtype.val hxy
  · intro y
    obtain ⟨x, hx, hxy⟩ := y.property
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

/-- Exact star-algebra equivalence with the conjugated concrete algebra. -/
def unitaryConjugateEquiv (w : unitary (H →L[ℂ] H)) (N : VonNeumannAlgebra H) :
    Algebra N ≃⋆ₐ[ℂ] Algebra (unitaryConjugateAlgebra w N) :=
  StarAlgEquiv.ofBijective (unitaryConjugateHom w N) (unitaryConjugateHom_bijective w N)

@[simp]
theorem unitaryConjugateEquiv_apply (w : unitary (H →L[ℂ] H))
    (N : VonNeumannAlgebra H) (x : Algebra N) :
    (unitaryConjugateEquiv w N x : H →L[ℂ] H) = unitaryConj w x := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteBlockExtension
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Finite blocks of a countable amplification

Finite operator matrices act on the first finitely many matrix summands.
Their extension is an isometric nonunital star homomorphism. These are the
bounded approximants used for the infinite-amplification gap estimate.
-/

namespace KadisonKastler

open scoped BigOperators CStarAlgebra

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {E : Submodule ℂ H} [CompleteSpace E]

namespace FullMatrixCorner

variable (F : FullMatrixCorner E)

def blockElement (i j : ℕ) (T : E →L[ℂ] E) : H →L[ℂ] H :=
  F.entry i 0 * cornerExtension E T * F.entry 0 j

theorem blockElement_mul (i j k l : ℕ) (T U : E →L[ℂ] E) :
    F.blockElement i j T * F.blockElement k l U =
      if j = k then F.blockElement i l (T * U) else 0 := by
  have hc : cornerExtension E T * (F.entry 0 j * F.entry k 0) * cornerExtension E U =
      if j = k then cornerExtension E (T * U) else 0 := by
    rw [F.mul_entry]
    split_ifs
    · rw [F.zero_zero, cornerExtension_mul_starProjection, ← cornerExtension_mul]
    · simp
  calc
    _ = F.entry i 0 *
        (cornerExtension E T * (F.entry 0 j * F.entry k 0) * cornerExtension E U) *
          F.entry 0 l := by unfold blockElement; noncomm_ring
    _ = _ := by rw [hc]; split_ifs <;> simp [blockElement]

theorem blockElement_star (i j : ℕ) (T : E →L[ℂ] E) :
    star (F.blockElement i j T) = F.blockElement j i (star T) := by
  simp only [blockElement, star_mul, F.star_entry, ← cornerExtension_star, mul_assoc]

def finiteBlock {n : ℕ} (X : CStarMatrix (Fin n) (Fin n) (E →L[ℂ] E)) : H →L[ℂ] H :=
  ∑ i : Fin n, ∑ j : Fin n, F.blockElement i j (X i j)

theorem finiteBlock_mul {n : ℕ}
    (X Y : CStarMatrix (Fin n) (Fin n) (E →L[ℂ] E)) :
    F.finiteBlock (X * Y) = F.finiteBlock X * F.finiteBlock Y := by
  let f : Fin n → Fin n → (E →L[ℂ] E) := fun i j => X i j
  let g : Fin n → Fin n → (E →L[ℂ] E) := fun i j => Y i j
  change (∑ i : Fin n, ∑ j : Fin n, F.blockElement i j (∑ k : Fin n, f i k * g k j)) =
    (∑ i : Fin n, ∑ j : Fin n, F.blockElement i j (f i j)) *
      (∑ i : Fin n, ∑ j : Fin n, F.blockElement i j (g i j))
  simp only [Finset.sum_mul, Finset.mul_sum, F.blockElement_mul]
  have he (j k : Fin n) : ((j : ℕ) = k) ↔ j = k := Fin.val_inj
  simp_rw [he]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
  have hs (i j : Fin n) : F.blockElement i j (∑ k : Fin n, f i k * g k j) =
      ∑ k : Fin n, F.blockElement i j (f i k * g k j) := by
    simp only [blockElement, map_sum, Finset.mul_sum, Finset.sum_mul]
  simp_rw [hs]
  calc
    _ = ∑ j : Fin n, ∑ i : Fin n, ∑ k : Fin n,
        F.blockElement i j (f i k * g k j) := Finset.sum_comm
    _ = ∑ j : Fin n, ∑ k : Fin n, ∑ i : Fin n,
        F.blockElement i j (f i k * g k j) := by
      apply Finset.sum_congr rfl
      intro j _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

def finiteBlockHom (n : ℕ) : CStarMatrix (Fin n) (Fin n) (E →L[ℂ] E) →⋆ₙₐ[ℂ]
    (H →L[ℂ] H) where
  toFun := F.finiteBlock
  map_zero' := by simp [finiteBlock, blockElement]
  map_add' X Y := by simp [finiteBlock, blockElement, mul_add, add_mul, Finset.sum_add_distrib]
  map_mul' := F.finiteBlock_mul
  map_smul' c X := by simp [finiteBlock, blockElement, Finset.smul_sum]
  map_star' X := by
    simp only [finiteBlock, star_sum, F.blockElement_star, CStarMatrix.star_apply]
    rw [Finset.sum_comm]

end FullMatrixCorner

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PublishedSimpleDerivation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Sakai's inner-derivation theorem, in its needed unital form

S. Sakai, *Derivations of simple C*-algebras II*, Bulletin de la Société
Mathématique de France 99 (1971), 259--263, §2, unnumbered theorem on p.260,
together with the unital specialization explained in §1 on p.259.
DOI: 10.24033/bsmf.1719. The only input is innerness of bounded derivations
of a simple unital C-star algebra. Self-adjointness of an implementer is
derived below, not included in that input.
-/

namespace KadisonKastler

noncomputable section

universe u

/-- The published theorem, with no separability assumption. -/
def PublishedSimpleDerivationInner : Prop :=
  ∀ (A : Type u) [CStarAlgebra A] [Nontrivial A], CStarSimple A →
    ∀ D : A →L[ℂ] A,
      (∀ x y, D (x * y) = D x * y + x * D y) →
      ∃ a : A, ∀ x, D x = a * x - x * a

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SpatialConjugacyTransport
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Transporting an implementer through Hilbert coordinates -/

namespace KadisonKastler

noncomputable section

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

@[simp] theorem spatialTransportAlgebra_symm (e : H ≃ₗᵢ[ℂ] K)
    (M : VonNeumannAlgebra H) :
    spatialTransportAlgebra e.symm (spatialTransportAlgebra e M) = M := by
  ext T
  rw [mem_spatialTransportAlgebra, mem_spatialTransportAlgebra]
  change e.conjStarAlgEquiv.symm (e.conjStarAlgEquiv T) ∈ M ↔ T ∈ M
  rw [StarAlgEquiv.symm_apply_apply]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PublishedCentralDecomposition
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

structure CentralPairDecomposition (M N : VonNeumannAlgebra H)
    (A B C : StarSubalgebra ℂ (H →L[ℂ] H)) (hAC : A ≤ C) (hBC : B ≤ C) where
  stratum : ℕ → MeasuredHilbertStratum.{u}
  coordinates : H ≃ₗᵢ[ℂ] lp (fun n => (stratum n).space) 2
  leftBlock : ∀ n, VonNeumannAlgebra (stratum n).space
  rightBlock : ∀ n, VonNeumannAlgebra (stratum n).space
  leftBlocks : BlockAlgebraDecomposition leftBlock (spatialTransportAlgebra coordinates M)
  rightBlocks : BlockAlgebraDecomposition rightBlock (spatialTransportAlgebra coordinates N)
  representation : ∀ n, (stratum n).X → C →⋆ₐ[ℂ] ((stratum n).K →L[ℂ] (stratum n).K)
  representation_measurable : ∀ n (c : C) (ξ : (stratum n).K),
    Measurable (fun x => representation n x c ξ)
  leftFields : ∀ n, OperatorFieldDecomposition (stratum n).μ
    (fun x => generatedVonNeumannAlgebra
      ((representation n x).comp (StarSubalgebra.inclusion hAC)).range) (leftBlock n)
  rightFields : ∀ n, OperatorFieldDecomposition (stratum n).μ
    (fun x => generatedVonNeumannAlgebra
      ((representation n x).comp (StarSubalgebra.inclusion hBC)).range) (rightBlock n)
  factors : ∀ n, ∀ᵐ x ∂(stratum n).μ,
    ScalarCenter (generatedVonNeumannAlgebra
      ((representation n x).comp (StarSubalgebra.inclusion hAC)).range) ∧
    ScalarCenter (generatedVonNeumannAlgebra
      ((representation n x).comp (StarSubalgebra.inclusion hBC)).range)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CyclicOrbitRestriction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Faithful cyclic restriction to a vector orbit

A separating vector remains separating after restriction to its closed
orbit, where it is cyclic by construction. The concrete reducing map
retains the commutant-corner identification.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (M : VonNeumannAlgebra H) (ξ : H)

abbrev cyclicOrbitSpace := vectorOrbitClosure M.toStarSubalgebra ξ

def cyclicOrbitVector : cyclicOrbitSpace M ξ := ⟨ξ, mem_vectorOrbitClosure _ _⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteBlockCompression
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Contractive finite compressions of the countable amplification -/

namespace KadisonKastler

open Filter
open scoped BigOperators CStarAlgebra Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {E : Submodule ℂ H} [CompleteSpace E]

namespace FullMatrixCorner

variable (F : FullMatrixCorner E)

attribute [local instance] OAI.KadisonKastler.FullMatrixCorner.compressionOperatorStarOrder
def finiteCompression (n : ℕ) (T : H →L[ℂ] H) :
    CStarMatrix (Fin n) (Fin n) (E →L[ℂ] E) := fun i j => F.matrixEntry T i j

end FullMatrixCorner

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteCornerGroups
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFiniteBoundedWord _root_.OAI.HochschildPatching.instFiniteLinearLabel _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Finite signed groups in a countable matrix corner

Each finite group acts on the first finitely many matrix summands and as
the identity on their orthogonal complement.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {E : Submodule ℂ H} [CompleteSpace E]

namespace FullMatrixCorner

variable (F : FullMatrixCorner E)

theorem blockElement_scalar (i j : ℕ) (z : ℂ) :
    F.blockElement i j (z • (1 : E →L[ℂ] E)) = z • F.entry i j := by
  rw [blockElement, map_smul, mul_smul_comm, smul_mul_assoc,
    cornerExtension_one, ← F.zero_zero, F.mul_entry, ite_eq_left rfl, F.mul_entry, ite_eq_left rfl]

/-- The scalar finite-block representation before adjoining the complement. -/
def scalarBlockHom (n : ℕ) : CStarMatrix (Fin n) (Fin n) ℂ →⋆ₙₐ[ℂ] (H →L[ℂ] H) :=
  (F.finiteBlockHom n).comp
    (CStarMatrix.mapₙₐ (StarAlgHom.ofId ℂ (E →L[ℂ] E)).toNonUnitalStarAlgHom)

theorem scalarBlockHom_apply {n : ℕ} (a : CStarMatrix (Fin n) (Fin n) ℂ) :
    F.scalarBlockHom n a = ∑ i : Fin n, ∑ j : Fin n, a i j • F.entry i j := by
  change (∑ i : Fin n, ∑ j : Fin n,
    F.blockElement i j (algebraMap ℂ (E →L[ℂ] E) (a i j))) = _
  simp only [Algebra.algebraMap_eq_smul_one, F.blockElement_scalar]

/-- The actual ambient representation of the finite signed-permutation group. -/
def finiteSignedRepresentation (n : ℕ) : SignedPermutation (Fin n) →*
    unitary (H →L[ℂ] H) :=
  (cornerUnitaryExtension (A := CStarMatrix (Fin n) (Fin n) ℂ)
    (B := H →L[ℂ] H) (F.scalarBlockHom n)).comp (signedCStarRepresentation n)

/-- Its range is a finite subgroup of the ambient unitary group. -/
def finiteSignedGroup (n : ℕ) : Subgroup (unitary (H →L[ℂ] H)) :=
  (F.finiteSignedRepresentation n).range

instance finiteSignedGroup_finite (n : ℕ) : Finite (F.finiteSignedGroup n) :=
  (Set.finite_range _).to_subtype

end FullMatrixCorner

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_NormalizerTopology
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

/-- The normalizers of a concrete von Neumann algebra as an actual subgroup. -/
def normalizerGroup (P : VonNeumannAlgebra H) : Subgroup (unitary (H →L[ℂ] H)) where
  carrier := {v | Conjugates v P P}
  one_mem' := conjugates_one P
  mul_mem' hv hw := hw.trans hv
  inv_mem' hv := by
    change Conjugates _ P P
    simpa only [← Unitary.star_eq_inv] using hv.symm

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]

/-- Uniformly bounded families all of whose values normalize the algebra. -/
def NormalizingFamily (P : VonNeumannAlgebra H) :=
  {V : unitary (G →ᵇ (H →L[ℂ] H)) // ∀ g, unitaryFamilyEval V g ∈ normalizerGroup P}

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PositiveFrequencyAlgebra
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The concrete algebra of positive-frequency multipliers -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Decomposable operators preserving the actual positive-frequency cut.
Commutation with characters is included so the published causal multiplier
theorem applies after Fourier conjugation. -/
def positiveFrequencyAlgebra : Subalgebra ℂ
    (RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) where
  carrier := {T | (∀ s : ℝ, Commute T (regularCharacterUnitary (H := H) s :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)) ∧
    regularFrequencyProjection 0 * T * regularFrequencyProjection 0 =
      T * regularFrequencyProjection 0}
  zero_mem' := by simp [Commute, SemiconjBy]
  one_mem' := by
    refine ⟨fun _ => Commute.one_left _, ?_⟩
    simpa only [mul_one, one_mul] using
      (regularFrequencyProjection_isStarProjection (H := H) 0).isIdempotentElem.eq
  add_mem' := by
    rintro A B ⟨hA, hAP⟩ ⟨hB, hBP⟩
    exact ⟨fun s => (hA s).add_left (hB s), by
      simp only [mul_add, add_mul, hAP, hBP]⟩
  mul_mem' := by
    rintro A B ⟨hA, hAP⟩ ⟨hB, hBP⟩
    refine ⟨fun s => (hA s).mul_left (hB s), ?_⟩
    let P : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H := regularFrequencyProjection 0
    change P * (A * B) * P = (A * B) * P
    change P * A * P = A * P at hAP
    change P * B * P = B * P at hBP
    calc
      _ = P * A * (B * P) := by simp only [mul_assoc]
      _ = P * A * (P * B * P) := congrArg (fun Z => P * A * Z) hBP.symm
      _ = (P * A * P) * B * P := by simp only [mul_assoc]
      _ = (A * P) * B * P := by rw [hAP]
      _ = A * (P * B * P) := by simp only [mul_assoc]
      _ = A * (B * P) := congrArg (fun Z => A * Z) hBP
      _ = _ := by simp only [mul_assoc]
  algebraMap_mem' z := by
    refine ⟨fun s => ?_, ?_⟩
    · change algebraMap ℂ _ z * _ = _ * algebraMap ℂ _ z
      rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, mul_smul_comm,
        one_mul, mul_one]
    · simp only [Algebra.algebraMap_eq_smul_one, mul_smul_comm,
        smul_mul_assoc, mul_one, one_mul,
        (regularFrequencyProjection_isStarProjection (H := H) 0).isIdempotentElem.eq]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PublishedHardyEvaluation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Published evaluation of causal Fourier multipliers

Kalle M. Mikkola, *Fourier multipliers for L² functions with values in
nonseparable Hilbert spaces and operator-valued Hᵖ boundary functions*,
Ann. Acad. Sci. Fenn. Math. 33 (2008), 121–130, Proposition 1.3 and
Theorem 1.5, pp.123–124. The Poisson representation is the Hardy-space
representation theorem cited in the proof of Corollary 1.7, p.125:
Rosenblum–Rovnyak, *Hardy Classes and Operator Theory* (1985),
Theorem 4.8B, p.90.

We retain only evaluation at one point, on the concrete algebra of
positive-frequency-preserving multiplication operators. Conjugation by
the Fourier transform identifies it with the causal translation-invariant
operators of Proposition 1.3 (a reflection interchanges Fourier signs).
That proposition gives the algebra representation; Theorem 1.5 identifies
the boundary field, and Poisson representation identifies its evaluation.
No holomorphic function space, norm estimate, perturbation conclusion or
choice of analytic approximant is included in this input.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

universe u

/-- The point-evaluation consequence of the published Hardy multiplier
representation. The domain and the Poisson integral are concrete. -/
def PublishedHardyMultiplierEvaluation : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H],
    ∀ (t r : ℝ), 0 < r →
      ∃ ev : positiveFrequencyAlgebra (H := H) →ₐ[ℂ] (H →L[ℂ] H),
        ∀ (F : ℝ → H →L[ℂ] H)
          (hF : ∀ x, AEStronglyMeasurable (fun s => F s x) volume)
          (C : ℝ) (hC : ∀ᵐ s, ‖F s‖ ≤ C)
          (T : positiveFrequencyAlgebra (H := H)),
          RepresentsOperatorField volume F T.val →
          ∀ hr : 0 < r, ev T = measurablePoissonAverage F hF C hC t r hr

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FrequencySmoothing
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Actual smoothing from quantitative frequency-cut defects

The boundary approximants are constructed by the published nest distance
theorem and the proved invariant averaging. The smoothing operators are
their actual Poisson integrals; their inverse and algebra estimates use
the published Hardy evaluation, with no additional analytic identities.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance frequencySmoothingOrder_rdab73d_1 (M : VonNeumannAlgebra H) : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance frequencySmoothingStarOrder_rdab73d_1 (M : VonNeumannAlgebra H) : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _
/-- The precise output of frequency-nest approximation for a contraction
field. The approximation is on the common original Hilbert space. -/
structure FrequencySmoothing (F : ℝ → H →L[ℂ] H) (δ : ℝ) where
  boundary : ℝ → H →L[ℂ] H
  measurable : ∀ x, AEStronglyMeasurable (fun t => boundary t x) volume
  bounded : ∀ᵐ t, ‖boundary t‖ ≤ 1 + 2 * δ
  close : ∀ᵐ t, ‖boundary t - F t‖ ≤ 2 * δ
  preserves : PreservesProjectionNest (regularFrequencyNest (H := H))
    (regularFieldOperator volume boundary measurable (1 + 2 * δ) bounded)

namespace FrequencySmoothing

local instance frequencySmoothingOrder_rdab73d_2 (M : VonNeumannAlgebra H) : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance frequencySmoothingStarOrder_rdab73d_2 (M : VonNeumannAlgebra H) : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _
variable {F G : ℝ → H →L[ℂ] H} {δ : ℝ}

/-- Positive-height smoothing after removing the scalar modulation. -/
def smooth (A : FrequencySmoothing F δ) (t r : ℝ) (hr : 0 < r) : H →L[ℂ] H :=
  demodulatedPoissonAverage A.boundary A.measurable (1 + 2 * δ) A.bounded t r hr

end FrequencySmoothing

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FrequencyActionAlignment
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Common modular actions from the actual frequency defects

The tolerance is fixed before the Hilbert space, the factors and their
actions. The pointwise normalizers are selected with no regularity claim;
the discrete real invariant mean then produces one small change of position.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def FrequencyDefectBound (W : ℝ → unitary (H →L[ℂ] H))
    (hW : ∀ x, Continuous (fun t => (W t : H →L[ℂ] H) x)) (δ : ℝ) : Prop :=
  ∀ a, ‖(1 - regularFrequencyNest (H := H) a) *
    regularFieldOperator volume (modulatedUnitaryField W)
      (fun x => (modulatedUnitaryField_continuous W hW x).aestronglyMeasurable) 1
      (Filter.Eventually.of_forall (norm_modulatedUnitaryField_le_one W)) *
      regularFrequencyNest (H := H) a‖ ≤ δ

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_HaagerupContinuous
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The ordinary continuous bilinear map underlying a row-column bound -/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- No continuity premise is required in the published correction theorem:
it follows directly from the scalar part of its Haagerup estimate. -/
def HaagerupBound.toContinuousBilinear {f : A →ₗ[ℂ] A →ₗ[ℂ] A} {c : ℝ}
    (hf : HaagerupBound f c) (hc : 0 ≤ c) : A →L[ℂ] A →L[ℂ] A :=
  let inner (x : A) : A →L[ℂ] A := (f x).mkContinuous (c * ‖x‖) (hf.apply_norm_le x)
  let outer : A →ₗ[ℂ] A →L[ℂ] A :=
    { toFun := inner
      map_add' x y := by ext z; exact congrArg (fun D : A →ₗ[ℂ] A => D z) (f.map_add x y)
      map_smul' r x := by ext z; exact congrArg (fun D : A →ₗ[ℂ] A => D z) (f.map_smul r x) }
  outer.mkContinuous c (fun x => ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg hc (norm_nonneg x)) (hf.apply_norm_le x))

@[simp] theorem HaagerupBound.toContinuousBilinear_apply
    {f : A →ₗ[ℂ] A →ₗ[ℂ] A} {c : ℝ} (hf : HaagerupBound f c) (hc : 0 ≤ c) (x y : A) :
    hf.toContinuousBilinear hc x y = f x y := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixCornerConjugation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Independent unitary actions on an off-diagonal corner

Two orthogonal isometries identify the ambient algebra with its two-by-two
amplification. Block-diagonal conjugations then act independently on the
two sides of an off-diagonal coefficient. Convexity extends this action
to multiplication by small contractions.
-/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A]

def twoBlockUnitary (u v : unitary A) : unitary (CStarMatrix (Fin 2) (Fin 2) A) :=
  ⟨blockDiagonal (u : A) (v : A), by
    constructor <;> ext i j
    all_goals
      simp only [CStarMatrix.mul_apply, CStarMatrix.star_apply, Fin.sum_univ_two]
      fin_cases i <;> fin_cases j <;>
        simp [blockDiagonal, diagonalStarAlgHom_apply, u.property.1, u.property.2,
          v.property.1, v.property.2]⟩

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace CuntzFamily

variable (S : CuntzFamily (Fin 2) H)

def liftedTwoBlockUnitary (u v : unitary (H →L[ℂ] H)) : unitary (H →L[ℂ] H) :=
  Unitary.map (StarMonoidHom.ofClass S.matrixEquiv.symm) (twoBlockUnitary u v)

end CuntzFamily

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixOrbitSampleLaw
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

/-- The actual finite sample space for one left and one right unitary. -/
abbrev MatrixOrbitIndex (d : ℕ) := SignedPermutation (Fin d) × SignedPermutation (Fin d)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProductStateCentralizer
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

/-- The two finite-site properties sufficient for the product-state argument.
No centralizer irreducibility or core-type conclusion is a field here. -/
structure LocalProductSwaps (D : VonNeumannAlgebra H) (Ω : H) where
  localAlgebra : ℕ → StarSubalgebra ℂ (H →L[ℂ] H)
  local_le : ∀ n, localAlgebra n ≤ D.toStarSubalgebra
  dense : DenseRange (fun p : Σ n, localAlgebra n => (p.2 : H →L[ℂ] H) Ω)
  independent_swap : ∀ (k : ℕ) (a : localAlgebra k) (n : ℕ),
    ∃ u : unitary (H →L[ℂ] H), (u : H →L[ℂ] H) ∈ D ∧
      ProductStateCentralizes D Ω u ∧
      ∀ b : localAlgebra n,
        productVectorState Ω (unitaryConj u a * b) =
          productVectorState Ω a * productVectorState Ω b

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixProductStateSwap
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

section Vector

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Centralization on a dense star algebra extends to its actual
bicommutant. This uses the proved unbounded strong-density theorem. -/
theorem productStateCentralizes_generated
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (Ω : H) (u : H →L[ℂ] H)
    (hS : ∀ x ∈ S, productVectorState Ω (u * x) = productVectorState Ω (x * u)) :
    ProductStateCentralizes (generatedVonNeumannAlgebra S) Ω u := by
  classical
  intro x hx
  have hx' : x ∈ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))) := by
    change x ∈ (generatedVonNeumannAlgebra S : Set (H →L[ℂ] H)) at hx
    rwa [generatedVonNeumannAlgebra_coe] at hx
  obtain ⟨a, ha⟩ := Generator.bicommutant_exists_strong_net S x hx'
  have hl : Tendsto (fun d => productVectorState Ω (u * (a d : H →L[ℂ] H))) atTop
      (𝓝 (productVectorState Ω (u * x))) := by
    change Tendsto (fun d => inner ℂ Ω (u ((a d : H →L[ℂ] H) Ω))) atTop
      (𝓝 (inner ℂ Ω (u (x Ω))))
    exact (continuous_const.inner continuous_id).continuousAt.tendsto.comp
      (u.continuous.continuousAt.tendsto.comp (ha Ω))
  have hr : Tendsto (fun d => productVectorState Ω ((a d : H →L[ℂ] H) * u)) atTop
      (𝓝 (productVectorState Ω (x * u))) := by
    change Tendsto (fun d => inner ℂ Ω ((a d : H →L[ℂ] H) (u Ω))) atTop
      (𝓝 (inner ℂ Ω (x (u Ω))))
    exact (continuous_const.inner continuous_id).continuousAt.tendsto.comp (ha (u Ω))
  exact tendsto_nhds_unique (hl.congr (fun d => hS _ (a d).property)) hr

/-- Stage-by-stage finite centralization supplies centralization on the
von Neumann algebra generated by the increasing local algebras. -/
theorem productStateCentralizes_of_local
    (S : ℕ → StarSubalgebra ℂ (H →L[ℂ] H)) (hmono : Monotone S)
    (Ω : H) (u : H →L[ℂ] H)
    (hS : ∀ n x, x ∈ S n → productVectorState Ω (u * x) = productVectorState Ω (x * u)) :
    ProductStateCentralizes (generatedVonNeumannAlgebra (⨆ n, S n)) Ω u := by
  apply productStateCentralizes_generated
  intro x hx
  have hx' : x ∈ ((⨆ n, S n : StarSubalgebra ℂ (H →L[ℂ] H)) : Set (H →L[ℂ] H)) := hx
  rw [StarSubalgebra.coe_iSup_of_directed hmono.directed_le] at hx'
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx'
  exact hS n x hn

end Vector

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProductMatrixStages
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Deriving the product-state argument from finite matrix data

A remote copy of a finite tensor block has identical matrix moments.
Every other finite block embeds in the product of these two blocks and
a finite complement. These are finite tensor-product statements; no
centralizer irreducibility or crossed-product conclusion is assumed.
-/

namespace KadisonKastler

open Generator

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Finite data obtained by moving a block to unused sites of the same
types. Complements witness the product formula on every finite stage. -/
structure RemoteProductBlock (s : ℕ → ℕ)
    (E : ∀ n, MatrixUnitSystem (Fin (s n)) (H →L[ℂ] H)) (Ω : H) (k n : ℕ) where
  copy : MatrixUnitSystem (Fin (s k)) (H →L[ℂ] H)
  copy_mem : copy.algebra ≤
    (generatedVonNeumannAlgebra (⨆ j, (E j).algebra)).toStarSubalgebra
  commutes : ∀ i j a b, Commute ((E k).entry i j) (copy.entry a b)
  independent : ∀ i j (b : (E n).algebra),
    productVectorState Ω (copy.entry i j * b) =
      productVectorState Ω ((E k).entry i j) * productVectorState Ω b
  complement : ∀ m, ∃ (r : ℕ) (C : MatrixUnitSystem (Fin r) (H →L[ℂ] H))
      (hc : ∀ i j a b, Commute (((E k).product copy commutes).entry i j) (C.entry a b)),
    (E m).algebra ≤ (((E k).product copy commutes).product C hc).algebra ∧
    ∃ β : Fin r → Fin r → ℂ, ∀ i j a b c d,
      productVectorState Ω (((E k).product copy commutes).entry (i, j) (a, b) *
        C.entry c d) = productVectorState Ω ((E k).entry i a) *
          productVectorState Ω ((E k).entry j b) * β c d

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SpatialSlice
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Concrete vector slices of the spatial von Neumann product -/

namespace KadisonKastler

open UnitalTomsWinter
open scoped TensorProduct InnerProductSpace

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- A first-leg commutant element commutes with the entire actual product. -/
theorem spatialLeft_commutes_product (M : VonNeumannAlgebra H) (D : VonNeumannAlgebra K)
    (a : H →L[ℂ] H) (ha : a ∈ M.commutant)
    (T : SpatialHilbert H K →L[ℂ] SpatialHilbert H K) (hT : T ∈ spatialProductAlgebra M D) :
    spatialLeft a * T = T * spatialLeft a := by
  let B : StarSubalgebra ℂ (SpatialHilbert H K →L[ℂ] SpatialHilbert H K) :=
    (M.toStarSubalgebra.map (spatialLeft (H := H) (K := K))) ⊔
      (D.toStarSubalgebra.map (spatialRight (H := H) (K := K)))
  have hB : B ≤ StarSubalgebra.centralizer ℂ {spatialLeft (K := K) a} := by
    apply sup_le
    · rintro _ ⟨x, hx, rfl⟩
      rw [StarSubalgebra.mem_centralizer_iff]
      intro g hg
      have hg' : g = spatialLeft (K := K) a := Set.mem_singleton_iff.mp hg
      subst g
      constructor
      · change spatialLeft (K := K) a * spatialLeft (K := K) x =
          spatialLeft (K := K) x * spatialLeft (K := K) a
        simpa only [map_mul] using (congrArg (spatialLeft (K := K))
          (VonNeumannAlgebra.mem_commutant_iff.mp ha x hx)).symm
      · change star (spatialLeft (K := K) a) * spatialLeft (K := K) x =
          spatialLeft (K := K) x * star (spatialLeft (K := K) a)
        rw [← map_star]
        have hs := VonNeumannAlgebra.mem_commutant_iff.mp
          (M.commutant.toStarSubalgebra.star_mem' ha) x hx
        simpa only [map_mul] using (congrArg (spatialLeft (K := K)) hs).symm
    · rintro _ ⟨x, hx, rfl⟩
      rw [StarSubalgebra.mem_centralizer_iff]
      intro g hg
      have hg' : g = spatialLeft (K := K) a := Set.mem_singleton_iff.mp hg
      subst g
      constructor
      · exact (Pureness.spatialLeftRight_commute (StarAlgHom.id ℂ (H →L[ℂ] H))
          (StarAlgHom.id ℂ (K →L[ℂ] K)) a x).eq
      · rw [← map_star]
        exact (Pureness.spatialLeftRight_commute (StarAlgHom.id ℂ (H →L[ℂ] H))
          (StarAlgHom.id ℂ (K →L[ℂ] K)) (star a) x).eq
  have hLa : spatialLeft (K := K) a ∈ Set.centralizer (B : Set _) := by
    intro x hx
    have hx' := hB hx
    rw [StarSubalgebra.mem_centralizer_iff] at hx'
    exact (hx' _ (Set.mem_singleton _)).1.symm
  change T ∈ generatedVonNeumannAlgebra B at hT
  change T ∈ (generatedVonNeumannAlgebra B : Set _) at hT
  rw [generatedVonNeumannAlgebra_coe] at hT
  exact hT _ hLa

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SpatialSliceRecovery
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Recovering the first tensor leg from scalar opposite slices

Polarization proves the relative-commutant identity needed for the fixed
product factor. No spatial tensor commutation theorem is added as an input.
-/

namespace KadisonKastler

open UnitalTomsWinter
open scoped TensorProduct InnerProductSpace

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace H] [CompleteSpace K] in
/-- Pure-tensor inner products determine a vector in the completed tensor product. -/
theorem spatialTensor_vector_ext {v w : SpatialHilbert H K}
    (h : ∀ (x : H) (η : K),
      inner ℂ (((x ⊗ₜ[ℂ] η : H ⊗[ℂ] K) : SpatialHilbert H K)) v =
      inner ℂ (((x ⊗ₜ[ℂ] η : H ⊗[ℂ] K) : SpatialHilbert H K)) w) : v = w := by
  apply ext_inner_left ℂ
  intro z
  induction z using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih z =>
    induction z using OAI.tensorInductionOn with
    | tmul x η => exact h x η
    | add a b ha hb =>
      simpa only [UniformSpace.Completion.coe_add, inner_add_left] using congrArg₂ (· + ·) ha hb

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TwoRatioReindex
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Reindexing the extra family of lambda sites

Even and odd lambda sites absorb a second countable family. Mu sites
are unchanged. This is the explicit state-preserving bijection used in
the pointed infinite tensor-product absorption argument.
-/

namespace KadisonKastler

noncomputable section

/-- Interleave the original and extra lambda families, leaving mu sites
in their original order. -/
def lambdaAbsorptionSiteEquiv : (TwoRatioSite ⊕ ℕ) ≃ TwoRatioSite :=
  (Equiv.sumAssoc ℕ ℕ ℕ).trans
    ((Equiv.sumCongr (Equiv.refl ℕ) (Equiv.sumComm ℕ ℕ)).trans
      ((Equiv.sumAssoc ℕ ℕ ℕ).symm.trans
        (Equiv.sumCongr Equiv.natSumNatEquivNat (Equiv.refl ℕ))))

@[simp] theorem lambdaAbsorptionSiteEquiv_old_lambda (n : ℕ) :
    lambdaAbsorptionSiteEquiv (Sum.inl (Sum.inl n)) = Sum.inl (2 * n) := rfl

@[simp] theorem lambdaAbsorptionSiteEquiv_new_lambda (n : ℕ) :
    lambdaAbsorptionSiteEquiv (Sum.inr n) = Sum.inl (2 * n + 1) := rfl

@[simp] theorem lambdaAbsorptionSiteEquiv_mu (n : ℕ) :
    lambdaAbsorptionSiteEquiv (Sum.inl (Sum.inr n)) = Sum.inr n := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PointedFiniteBlock
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

def matrixSiteBlockWeight (ν : I → ℝ) :
    (l : List I) → MatrixSiteBlockIndex l → MatrixSiteBlockIndex l → ℂ
  | [], _, _ => 1
  | i :: l, r, c =>
    (if r.1 = c.1 then (twoSiteWeight (ν i) r.1 : ℂ) else 0) *
      matrixSiteBlockWeight ν l r.2 c.2

theorem matrixSiteBlockWeight_ofFunction (ν : I → ℝ) (l : List I) (r c : I → Fin 2) :
    matrixSiteBlockWeight ν l (matrixSiteBlockIndexOfFunction l r)
      (matrixSiteBlockIndexOfFunction l c) =
      (l.map fun i => if r i = c i then (twoSiteWeight (ν i) (r i) : ℂ) else 0).prod := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [matrixSiteBlockWeight, matrixSiteBlockIndexOfFunction,
      List.map_cons, List.prod_cons, ih]
    rfl

theorem matrixSiteBlockWeight_map {J : Type*} (ν : I → ℝ) (η : J → ℝ) (f : I → J)
    (hf : ∀ i, η (f i) = ν i) (l : List I) (r c : MatrixSiteBlockIndex l) :
    matrixSiteBlockWeight η (l.map f) (matrixSiteBlockMapEquiv f l r)
      (matrixSiteBlockMapEquiv f l c) = matrixSiteBlockWeight ν l r c := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change (if r.1 = c.1 then (twoSiteWeight (η (f i)) r.1 : ℂ) else 0) * _ = _
    change (if r.1 = c.1 then (twoSiteWeight (η (f i)) r.1 : ℂ) else 0) *
      matrixSiteBlockWeight η (l.map f) (matrixSiteBlockMapEquiv f l r.2)
        (matrixSiteBlockMapEquiv f l c.2) = _
    rw [hf i, ih]
    rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TwoRatioFiniteSites
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Finite stages and unused sites in the two-ratio product -/

namespace KadisonKastler

def twoRatioFiniteSites (n : ℕ) : List TwoRatioSite :=
  (List.range n).map Sum.inl ++ (List.range n).map Sum.inr

@[simp] theorem inl_mem_twoRatioFiniteSites (i n : ℕ) :
    Sum.inl i ∈ twoRatioFiniteSites n ↔ i < n := by
  simp [twoRatioFiniteSites]

@[simp] theorem inr_mem_twoRatioFiniteSites (i n : ℕ) :
    Sum.inr i ∈ twoRatioFiniteSites n ↔ i < n := by
  simp [twoRatioFiniteSites]

theorem twoRatioFiniteSites_nodup (n : ℕ) : (twoRatioFiniteSites n).Nodup := by
  apply List.Nodup.append
  · exact (show (List.range n).Nodup from List.nodup_range).map Sum.inl_injective
  · exact (show (List.range n).Nodup from List.nodup_range).map Sum.inr_injective
  · apply List.disjoint_left.mpr
    intro i hi hj
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hi
    simp at hj

theorem twoRatioFiniteSites_mono {n m : ℕ} (h : n ≤ m) :
    ∀ i ∈ twoRatioFiniteSites n, i ∈ twoRatioFiniteSites m := by
  intro i hi
  cases i <;> simp only [inl_mem_twoRatioFiniteSites, inr_mem_twoRatioFiniteSites] at hi ⊢
  all_goals exact hi.trans_le h

theorem twoRatioFiniteSites_exhausts (i : TwoRatioSite) :
    ∃ n, i ∈ twoRatioFiniteSites n := by
  cases i with
  | inl i => exact ⟨i + 1, by simp⟩
  | inr i => exact ⟨i + 1, by simp⟩

def twoRatioSiteShift (q : ℕ) : TwoRatioSite → TwoRatioSite :=
  Sum.map (q + ·) (q + ·)

theorem twoRatioSiteShift_injective (q : ℕ) : Function.Injective (twoRatioSiteShift q) := by
  intro i j h
  cases i <;> cases j <;> simp_all [twoRatioSiteShift]

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PointedSiteBalance
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The weighted trace identity at a matrix site

Product moments identify the two weights in the KMS balance equation.
The identity is first proved in a finite block containing the site, then
extended to the actual von Neumann closure by strong density.
-/

namespace KadisonKastler

open Generator Filter
open scoped Topology

noncomputable section

variable {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {Ω : H} {ν : I → ℝ}

theorem weighted_productState_generated
    (A : StarSubalgebra ℂ (H →L[ℂ] H)) (Ω : H) (u : H →L[ℂ] H)
    (c d : ℂ)
    (hA : ∀ x ∈ A, c * productVectorState Ω (u * x) =
      d * productVectorState Ω (x * u)) :
    ∀ x ∈ generatedVonNeumannAlgebra A,
      c * productVectorState Ω (u * x) = d * productVectorState Ω (x * u) := by
  classical
  intro x hx
  have hx' : x ∈ Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H))) := by
    rwa [← generatedVonNeumannAlgebra_coe]
  obtain ⟨a, ha⟩ := Generator.bicommutant_exists_strong_net A x hx'
  have hl : Tendsto (fun k => c * productVectorState Ω (u * (a k : H →L[ℂ] H)))
      atTop (𝓝 (c * productVectorState Ω (u * x))) := by
    apply tendsto_const_nhds.mul
    change Tendsto (fun k => inner ℂ Ω (u ((a k : H →L[ℂ] H) Ω))) atTop
      (𝓝 (inner ℂ Ω (u (x Ω))))
    exact (continuous_const.inner continuous_id).continuousAt.tendsto.comp
      (u.continuous.continuousAt.tendsto.comp (ha Ω))
  have hr : Tendsto (fun k => d * productVectorState Ω ((a k : H →L[ℂ] H) * u))
      atTop (𝓝 (d * productVectorState Ω (x * u))) := by
    apply tendsto_const_nhds.mul
    change Tendsto (fun k => inner ℂ Ω ((a k : H →L[ℂ] H) (u Ω))) atTop
      (𝓝 (inner ℂ Ω (x (u Ω))))
    exact (continuous_const.inner continuous_id).continuousAt.tendsto.comp (ha (u Ω))
  exact tendsto_nhds_unique (hl.congr fun k => hA _ (a k).property) hr

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularStateAction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A semantic certificate for the modular action of a vector state

The bounded KMS strip condition is Blackadar, *Operator Algebras*,
III.4.7.1--2 (printed pp.325--326). For a faithful normal vector state
it characterizes its modular automorphism group. Retaining the condition
prevents the core classification from being applied to an arbitrary
strongly continuous action.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The scalar strip condition at inverse temperature minus one, with
the sign convention `σ_t(x) = U_t x U_t*`. -/
def VectorStateKMS (M : VonNeumannAlgebra H) (Ω : H)
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H)) : Prop :=
  ∀ x ∈ M, ∀ y ∈ M, ∃ f : ℂ → ℂ,
    ContinuousOn f {z | 0 ≤ z.im ∧ z.im ≤ 1} ∧
    DifferentiableOn ℂ f {z | 0 < z.im ∧ z.im < 1} ∧
    (∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.im → z.im ≤ 1 → ‖f z‖ ≤ C) ∧
    (∀ t : ℝ, f t = productVectorState Ω
      (unitaryConj (U (Multiplicative.ofAdd t)) x * y)) ∧
    (∀ t : ℝ, f ((t : ℂ) + Complex.I) = productVectorState Ω
      (y * unitaryConj (U (Multiplicative.ofAdd t)) x))

/-- The canonical implementation fixes the vector; together with the
strip condition this identifies the represented modular state action. -/
structure IsModularStateGroup (M : VonNeumannAlgebra H) (Ω : H)
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H)) : Prop where
  fixes_vector : ∀ t, (U t : H →L[ℂ] H) Ω = Ω
  kms : VectorStateKMS M Ω U

theorem productVectorState_unitaryConj_of_fixes
    (Ω : H) (u : unitary (H →L[ℂ] H))
    (hfix : (u : H →L[ℂ] H) Ω = Ω) (x : H →L[ℂ] H) :
    productVectorState Ω (unitaryConj u x) = productVectorState Ω x := by
  have hstar : (star (u : H →L[ℂ] H)) Ω = Ω := by
    have hinv := Unitary.star_mul_self_of_mem u.property
    calc
      _ = (star (u : H →L[ℂ] H)) ((u : H →L[ℂ] H) Ω) := by rw [hfix]
      _ = (star (u : H →L[ℂ] H) * (u : H →L[ℂ] H)) Ω := rfl
      _ = Ω := by rw [hinv]; rfl
  change inner ℂ Ω ((u : H →L[ℂ] H) (x ((star (u : H →L[ℂ] H)) Ω))) = _
  rw [hstar]
  calc
    _ = inner ℂ ((u : H →L[ℂ] H) Ω) ((u : H →L[ℂ] H) (x Ω)) := by rw [hfix]
    _ = _ := _root_.Unitary.inner_map_map u Ω (x Ω)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularSiteEigen
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Modular eigenoperators from the site-state balance identity -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {Ω : H}

theorem state_balance_unitary
    (v : unitary (H →L[ℂ] H)) (hv : Conjugates v M M)
    (hfix : (v : H →L[ℂ] H) Ω = Ω) (x : H →L[ℂ] H) (r : ℂ)
    (hbal : ∀ y ∈ M, productVectorState Ω (y * x) =
      r * productVectorState Ω (x * y)) :
    ∀ y ∈ M, productVectorState Ω (y * unitaryConj v x) =
      r * productVectorState Ω (unitaryConj v x * y) := by
  intro y hy
  let y₀ := unitaryConj (star v) y
  have hy₀ : y₀ ∈ M := by
    have h : y₀ ∈ unitaryConj (star v) '' (M : Set (H →L[ℂ] H)) :=
      Set.mem_image_of_mem _ hy
    rwa [hv.symm] at h
  have hcancel : unitaryConj v y₀ = y := by
    simpa only [star_star] using unitaryConj_star_unitaryConj (star v) y
  have hmul (a b : H →L[ℂ] H) :
      unitaryConj v (a * b) = unitaryConj v a * unitaryConj v b := by
    unfold unitaryConj
    symm
    calc
      _ = (v : H →L[ℂ] H) * a * (star (v : H →L[ℂ] H) * v) * b *
          star (v : H →L[ℂ] H) := by noncomm_ring
      _ = _ := by rw [Unitary.star_mul_self_of_mem v.property]; simp only [mul_one, mul_assoc]
  have hl := productVectorState_unitaryConj_of_fixes Ω v hfix (y₀ * x)
  have hr := productVectorState_unitaryConj_of_fixes Ω v hfix (x * y₀)
  rw [hmul, hcancel] at hl hr
  rw [hl, hr, hbal y₀ hy₀]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ShiftInvariantSigma
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The invariant sigma algebra of the nonsingular boundary shift

Using this measurable space directly avoids a redundant point-set coding of
the boundary. Its measurable sets are exactly the ambient measurable sets
fixed by the shift modulo null sets.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory Set

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) (S : X → X)

theorem measurable_shiftInvariantSigma_of_fixed
    {Y : Type*} [MeasurableSpace Y] {f : X → Y} (hf : Measurable f)
    (hfixed : ∀ᵐ x ∂μ, f (S x) = f x) :
    Measurable[shiftInvariantSigma μ S] f := by
  intro A hA
  refine ⟨hf hA, hfixed.mono ?_⟩
  intro x hx
  change f (S x) ∈ A ↔ f x ∈ A
  rw [hx]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProductInvariantIntegrals
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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
theorem invariant_section_measurable (hfm : StronglyMeasurable f)
    (hf : ∀ᵐ z ∂μ.prod ν, f (S z.1, z.2) = f z) (B : Set Y) :
    Measurable[shiftInvariantSigma μ S] (fun x => ∫ y in B, f (x, y) ∂ν) := by
  apply measurable_shiftInvariantSigma_of_fixed μ S
    ((hfm.integral_prod_right' (ν := ν.restrict B)).measurable)
  exact invariant_section_setIntegral hf B

theorem invariant_integrable_zero_of_rectangle_tests (hfm : StronglyMeasurable f)
    (hfi : Integrable f (μ.prod ν))
    (hfix : ∀ᵐ z ∂μ.prod ν, f (S z.1, z.2) = f z)
    (htest : ∀ A B, MeasurableSet[shiftInvariantSigma μ S] A → MeasurableSet B →
      ∫ z in A ×ˢ B, f z ∂μ.prod ν = 0) : f =ᵐ[μ.prod ν] 0 := by
  have hB (B : Set Y) (hBm : MeasurableSet B) :
      (fun x => ∫ y in B, f (x, y) ∂ν) =ᵐ[μ] 0 := by
    have hi := integrable_section_setIntegral hfi B
    apply ae_eq_of_forall_setIntegral_eq_of_sigmaFinite' (shiftInvariantSigma_le μ S)
      (fun _ _ _ => hi.integrableOn) (fun _ _ _ => (integrable_zero _ _ _).integrableOn)
    · intro A hA _
      rw [← setIntegral_prod f hfi.integrableOn, htest A B hA hBm]
      simp
    · exact (invariant_section_measurable hfm hfix B).stronglyMeasurable.aestronglyMeasurable
    · exact aestronglyMeasurable_zero
  apply integrable_eq_zero_of_rectangle_integrals hfi
  intro A B _ hBmeas
  rw [setIntegral_prod f hfi.integrableOn]
  calc
    (∫ x in A, ∫ y in B, f (x, y) ∂ν ∂μ) = ∫ x in A, (0 : ℂ) ∂μ :=
      integral_congr_ae (ae_restrict_of_ae (hB B hBmeas))
    _ = 0 := by simp

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ScalarWeakLimit
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Bounded scalar weak limits

Uniformly bounded scalar functions have simultaneous weak L2 cluster points
on a probability space. Closed convex disk constraints retain the essential
bound, so the limits are actual L-infinity classes.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

def scalarInfinityToL2 (f : ScalarLInfinity μ) : Lp ℂ 2 μ :=
  ((Lp.memLp f).mono_exponent le_top).toLp f

theorem scalarInfinityToL2_ae (f : ScalarLInfinity μ) :
    scalarInfinityToL2 f =ᵐ[μ] f := MemLp.coeFn_toLp _

theorem scalarInfinityToL2_injective :
    Function.Injective (scalarInfinityToL2 (μ := μ)) := by
  intro f g hfg
  apply Lp.ext
  have hf := scalarInfinityToL2_ae f
  rw [hfg] at hf
  exact hf.symm.trans (scalarInfinityToL2_ae g)

theorem scalarInfinityToL2_add (f g : ScalarLInfinity μ) :
    scalarInfinityToL2 (f + g) = scalarInfinityToL2 f + scalarInfinityToL2 g := by
  apply Lp.ext
  filter_upwards [scalarInfinityToL2_ae (f + g), scalarInfinityToL2_ae f,
    scalarInfinityToL2_ae g, Lp.coeFn_add f g,
    Lp.coeFn_add (scalarInfinityToL2 f) (scalarInfinityToL2 g)] with x ha hb hc hd he
  simp only [Pi.add_apply] at hd he
  rw [ha, hd, he, hb, hc]

theorem scalarInfinityToL2_smul (c : ℂ) (f : ScalarLInfinity μ) :
    scalarInfinityToL2 (c • f) = c • scalarInfinityToL2 f := by
  apply Lp.ext
  filter_upwards [scalarInfinityToL2_ae (c • f), scalarInfinityToL2_ae f,
    Lp.coeFn_smul c f, Lp.coeFn_smul c (scalarInfinityToL2 f)] with x ha hb hc hd
  simp only [Pi.smul_apply] at hc hd
  rw [ha, hc, hd, hb]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProductInvariantL2
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.Generator.vectorOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The product range of a one-coordinate invariant projection

An L2 function fixed by the shift in its first coordinate is measurable,
modulo null sets, for the product of the invariant and second sigma algebras.
The proof tests its orthogonal-projection remainder against rectangles.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory Set

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
  {S : X → X}

omit [IsFiniteMeasure μ] [IsFiniteMeasure ν] in
theorem firstInvariantSigma_le : firstInvariantSigma (Y := Y) μ S ≤
    (inferInstance : MeasurableSpace (X × Y)) := by
  apply sup_le_sup
  · exact MeasurableSpace.comap_mono (shiftInvariantSigma_le μ S)
  · exact le_rfl

theorem L2_mem_firstInvariantSigma_of_fixed
    (hS : Measure.QuasiMeasurePreserving S μ μ) (f : Lp ℂ 2 (μ.prod ν))
    (hf : ∀ᵐ z ∂μ.prod ν, f (S z.1, z.2) = f z) :
    f ∈ lpMeas ℂ ℂ (firstInvariantSigma μ S) 2 (μ.prod ν) := by
  have hm : firstInvariantSigma (Y := Y) μ S ≤ mX.prod mY := firstInvariantSigma_le
  let : Fact (firstInvariantSigma (Y := Y) μ S ≤ mX.prod mY) := ⟨hm⟩
  let K := lpMeas ℂ ℂ (firstInvariantSigma μ S) 2 (μ.prod ν)
  let p := K.starProjection f
  let h := f - p
  have hp : p ∈ K := K.starProjection_apply_mem f
  have hpf := firstInvariantSigma_fixed hS
    (mem_lpMeas_iff_aestronglyMeasurable.mp hp)
  have hfix : ∀ᵐ z ∂μ.prod ν, h (S z.1, z.2) = h z := by
    filter_upwards [hf, hpf, Lp.coeFn_sub f p,
      (firstCoordinateShift_quasi (ν := ν) hS).ae (Lp.coeFn_sub f p)] with z hf hp hz hs
    change h (firstCoordinateShift S z) = h z
    change h (firstCoordinateShift S z) = _ at hs
    rw [hs, hz]
    exact congrArg₂ (· - ·) hf hp
  have hz : h = 0 := by
    apply Lp.eq_zero_iff_ae_eq_zero.mpr
    apply invariant_integrable_zero_of_rectangle_tests (Lp.stronglyMeasurable h)
      ((Lp.memLp h).integrable (by norm_num)) hfix
    intro A B hA hB
    have hAB : MeasurableSet[firstInvariantSigma μ S] (A ×ˢ B) := hA.prod hB
    have hAB' : MeasurableSet (A ×ˢ B) := hm _ hAB
    have hfin : (μ.prod ν) (A ×ˢ B) ≠ ⊤ := measure_ne_top _ _
    have hi : indicatorConstLp 2 hAB' hfin (1 : ℂ) ∈ K :=
      mem_lpMeas_indicatorConstLp hm hAB hfin
    have ho := (K.sub_starProjection_mem_orthogonal f) _ hi
    exact (L2.inner_indicatorConstLp_one hAB' hfin h).symm.trans ho
  have he : f = p := sub_eq_zero.mp hz
  rw [he]
  exact hp

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RandomWalkPathAction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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

def randomWalkPathAction : NonsingularAction G (RandomWalkPath G) (randomWalkPathLaw G) where
  toPerm := {
    toFun := fun g => Equiv.prodCongr (Equiv.mulLeft g) (Equiv.refl _)
    map_one' := by ext x <;> simp
    map_mul' := by intro g h; ext x <;> simp [mul_assoc] }
  quasi g := MeasureTheory.QuasiMeasurePreserving.prodMap
    (symmetricRandomWalkLaw_quasi (fun x => g * x))
    (Measure.QuasiMeasurePreserving.id _)

@[simp]
theorem randomWalkPathAction_apply (g : G) (x : RandomWalkPath G) :
    (randomWalkPathAction G).toPerm g x = (g * x.1, x.2) := rfl

def randomWalkAdvance (x : RandomWalkPath G) : RandomWalkPath G :=
  (x.1 * x.2 0, fun n => x.2 (n + 1))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ShiftBoundarySpace
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The boundary as the invariant measurable space

Only its measurable structure enters the application. Keeping the original
points and restricting their sigma algebra gives the probability boundary
directly, with a nonsingular action induced by the rooted path action.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) (S : X → X)

variable {G : Type*} [Group G]

def shiftBoundaryAction (α : NonsingularAction G X μ)
    (hc : ∀ g x, S (α.toPerm g x) = α.toPerm g (S x)) :
    NonsingularAction G (ShiftBoundarySpace μ S) (shiftBoundaryMeasure μ S) where
  toPerm := α.toPerm
  quasi g := quasi_shiftInvariantSigma_of_commuting μ S (α.toPerm g) (α.quasi g) (hc g)

@[simp]
theorem shiftBoundaryAction_apply (α : NonsingularAction G X μ)
    (hc : ∀ g x, S (α.toPerm g x) = α.toPerm g (S x)) (g : G) (x : X) :
    (shiftBoundaryAction μ S α hc).toPerm g (shiftBoundaryMap μ S x) =
      shiftBoundaryMap μ S (α.toPerm g x) := rfl

variable (G : Type*) [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]

abbrev RandomWalkBoundary :=
  ShiftBoundarySpace (randomWalkPathLaw G) (randomWalkAdvance G)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProductBoundaryLifts
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

def firstBoundaryMap (z : X × Y) : ShiftBoundarySpace μ S × Y :=
  (shiftBoundaryMap μ S z.1, z.2)

theorem firstBoundaryMap_measurePreserving :
    MeasurePreserving (firstBoundaryMap (Y := Y) μ S) (μ.prod ν)
      ((shiftBoundaryMeasure μ S).prod ν) :=
  (shiftBoundaryMap_measurePreserving μ S).prod (MeasurePreserving.id ν)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ParameterizedBoundaryMean
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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

namespace NonsingularAction

variable {G D Y : Type*} [Group G] [MeasurableSpace D] [MeasurableSpace Y]
  {μ : Measure D} {ν : Measure Y} [SFinite μ] [SFinite ν]

def leftOnProduct (α : NonsingularAction G D μ) : NonsingularAction G (D × Y) (μ.prod ν) where
  toPerm :=
    { toFun := fun g => Equiv.prodCongr (α.toPerm g) (Equiv.refl Y)
      map_one' := by ext z <;> simp
      map_mul' g h := by ext z <;> simp }
  quasi g := MeasureTheory.QuasiMeasurePreserving.prodMap
    (α.quasi g) (Measure.QuasiMeasurePreserving.id ν)

@[simp]
theorem leftOnProduct_apply (α : NonsingularAction G D μ) (g : G) (z : D × Y) :
    (α.leftOnProduct (ν := ν)).toPerm g z = (α.toPerm g z.1, z.2) := rfl

end NonsingularAction

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PointedLocalMatrix
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

structure PointedLocalMatrixData (ν : ℝ) where
  left : Generator.MatrixUnitSystem (Fin 2) (PointedLocalHilbert →L[ℂ] PointedLocalHilbert)
  right : Generator.MatrixUnitSystem (Fin 2) (PointedLocalHilbert →L[ℂ] PointedLocalHilbert)
  commutes : ∀ i j k l, Commute (left.entry i j) (right.entry k l)
  left_spans : Submodule.span ℂ (Set.range (fun ij : Fin 2 × Fin 2 =>
    left.entry ij.1 ij.2 pointedLocalVacuum)) = ⊤
  right_spans : Submodule.span ℂ (Set.range (fun ij : Fin 2 × Fin 2 =>
    right.entry ij.1 ij.2 pointedLocalVacuum)) = ⊤
  moment : ∀ i j, inner ℂ pointedLocalVacuum (left.entry i j pointedLocalVacuum) =
    if i = j then (twoSiteWeight ν i : ℂ) else 0

def pointedRawVacuum (ν : ℝ) : PointedRawHilbert :=
  WithLp.toLp 2 (fun p => if p.1 = p.2 then (Real.sqrt (twoSiteWeight ν p.1) : ℂ) else 0)

@[simp] theorem pointedRawVacuum_apply (ν : ℝ) (p : Fin 2 × Fin 2) :
    pointedRawVacuum ν p =
      if p.1 = p.2 then (Real.sqrt (twoSiteWeight ν p.1) : ℂ) else 0 := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PreparedGraphRows
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Prepared graph comparison from individual row approximants

Only a separate nearby row is required for each finite row in either
algebra. No global linear map selecting those approximants is assumed.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance preparedGraphRowsOrder_rdab73d_1 (M : VonNeumannAlgebra H) : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance preparedGraphRowsStarOrder_rdab73d_1 (M : VonNeumannAlgebra H) : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _
attribute [local instance] OAI.KadisonKastler.preparedGraphRowsOperatorOrder
local instance preparedGraphRowsOperatorStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _

/-- The individual finite-row approximation property used in the graph
construction. This notation imposes no compatibility among the choices. -/
abbrev GraphRowApproximation (M N : VonNeumannAlgebra H) (γ : ℝ) : Prop :=
  ∀ (k : ℕ) (X : Fin k → H →L[ℂ] H), (∀ i, X i ∈ M) →
    ∃ Z : Fin k → H →L[ℂ] H, (∀ i, Z i ∈ N) ∧
      ‖operatorRow X - operatorRow Z‖ ≤ γ * ‖operatorRow X‖

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_VectorCoreField
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Measurable operator fields from a countable vector core

Pointwise bounded rational-linear maps commuting with multiplication by
`i` extend to complex-linear operators. Countability gives simultaneous
identities off one null set; dense coefficient tests give measurability.
-/

namespace KadisonKastler

open MeasureTheory Filter TopologicalSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] OAI.KadisonKastler.vectorCoreNormedSpace
structure CoherentVectorCore (C : RationalComplexCore H) (B : ℝ) (g : C.space → H) : Prop where
  add : ∀ x y, g (x + y) = g x + g y
  rat : ∀ (r : ℚ) x, g (r • x) = r • g x
  mulI : ∀ x, g (C.mulI x) = Complex.I • g x
  bound : ∀ x, ‖g x‖ ≤ B * ‖(x : H)‖

namespace CoherentVectorCore

variable {C : RationalComplexCore H} {B : ℝ} {g : C.space → H}

attribute [local instance] OAI.KadisonKastler.vectorCoreNormedSpace
def linearMap (h : CoherentVectorCore C B g) : C.space →ₗ[ℚ] H where
  toFun := g
  map_add' := h.add
  map_smul' := h.rat

def operator (h : CoherentVectorCore C B g) : H →L[ℂ] H :=
  C.extendComplex h.linearMap h.bound h.mulI

end CoherentVectorCore

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCoreCommutant
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The regular crossed-product commutant and fixed algebra

The sole input is the commutant-generator theorem for a covariant
representation of a von Neumann algebra.  See Takesaki, *Theory of
Operator Algebras II* (2003), Theorem X.1.21, and Van Daele, *Continuous
Crossed Products and Type III von Neumann Algebras* (1978), Part I,
Theorem 3.11.  The exact covariant-implementation formula is also stated
in Takesaki's author notes *Structure of von Neumann Algebras of Type
III*, Lecture 1, Theorem 1.3(ii), pp. 10--11:
https://www.imsc.res.in/~sunder/mtnotes.pdf

Its generators here are constant operators from `P'` and the actual
operators `f(t) ↦ U(s) f(t+s)`.  The fixed-algebra equality is proved
below from this input and double commutants; it is not an input.
-/

namespace KadisonKastler

open MeasureTheory
open scoped Topology

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The concrete generators on the commutant side of the regular
crossed-product commutation theorem. -/
def regularCommutantGenerators
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H)) (P : VonNeumannAlgebra H) :
    Set (RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) :=
  regularConstantHom (volume : Measure ℝ) '' (P.commutant : Set (H →L[ℂ] H)) ∪
    Set.range (fun s => (regularCoreAction U s :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H))

/-- The actual von Neumann algebra generated by the commutant generators. -/
def regularCommutantAlgebra
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H)) (P : VonNeumannAlgebra H) :
    VonNeumannAlgebra (RegularCoreHilbert H) :=
  generatedVonNeumannAlgebra (StarAlgebra.adjoin ℂ (regularCommutantGenerators U P))

/-- The real-group specialization of the published commutant-generator
theorem. Strong continuity refers to the ordinary topology on `ℝ`.
No fixed-point equality or perturbation assertion is assumed. -/
def PublishedRegularCommutant : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H],
    ∀ (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
      (hU : ∀ ξ, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) ξ))
      (P : VonNeumannAlgebra H),
      (∀ s T, T ∈ P → unitaryConj (U s) T ∈ P) →
      (regularCoreAlgebra U hU P).commutant = regularCommutantAlgebra U P

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCommutantPackets
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Gauged wave-packet coefficients

Compression between two scalar wave packets turns commutation with the
regular copy of `P` into membership in `P'`. Translation commutation
then gives the exact covariance of these coefficients. These are the
operator-valued coefficients used in the regular commutant argument.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ ξ, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) ξ))

/-- A scalar wave packet in the regular representation, with its gauge removed. -/
def regularGaugedPacket (φ : Lp ℂ 2 (volume : Measure ℝ)) :
    H →L[ℂ] RegularCoreHilbert H :=
  (star (regularGauge U hU) : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H).comp
    (regularTensorVector φ)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RowVectorEstimate
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrixAlgebraEquiv_apply _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.spatialTransportEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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

local instance rowVectorAlgebraOrder_rdab73d_1 (M : VonNeumannAlgebra H) : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance rowVectorAlgebraStarOrder_rdab73d_1 (M : VonNeumannAlgebra H) : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _
local instance rowVectorOperatorOrder_rdab73d_1 : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
local instance rowVectorOperatorStarOrder_rdab73d_1 : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _
def algebraRow {M : VonNeumannAlgebra H} {ι : Type*} (r : ι → Algebra M) :
    CStarMatrix (Fin 1) ι (Algebra M) := CStarMatrix.ofMatrix fun _ j => r j

@[simp] theorem algebraRow_apply {M : VonNeumannAlgebra H} {ι : Type*}
    (r : ι → Algebra M) (i : Fin 1) (j : ι) : algebraRow r i j = r j := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SignedMatrixRefinement
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFiniteBoundedWord _root_.OAI.HochschildPatching.instFiniteLinearLabel _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.MatrixSiteWord.eval_append _root_.OAI.KadisonKastler.MatrixSiteWord.eval_cons _root_.OAI.KadisonKastler.MatrixSiteWord.eval_nil _root_.OAI.KadisonKastler.MatrixSiteWord.eval_reindex _root_.OAI.KadisonKastler.MatrixSiteWord.eval_star _root_.OAI.KadisonKastler.conjugatedMatrixUnits_entry _root_.OAI.KadisonKastler.matrixPermutationValue_one _root_.OAI.KadisonKastler.spatialMatrixUnits_entry _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Compatible finite signed groups under matrix refinement

Keeping the first matrix coordinates as sums over the new coordinates keeps
the old signed-permutation group inside the new finite group.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {A ι κ : Type*}
  [Ring A]
  [StarRing A]
  [_root_.Algebra ℂ A]
  [StarModule ℂ A]
  [Fintype ι]
  [DecidableEq ι]
  [Fintype κ]
  [DecidableEq κ]

instance matrixSignedGroup_finite (E : Generator.MatrixUnitSystem ι A) :
    Finite (matrixSignedGroup E) := (Set.finite_range _).to_subtype

theorem signedRepresentation_permutation (E : Generator.MatrixUnitSystem ι A)
    (σ : Equiv.Perm ι) :
    (matrixUnitSignedRepresentation E (SemidirectProduct.inr σ) : A) =
      ∑ i, E.entry (σ i) i := by
  rw [matrixUnitSignedRepresentation_inr]
  simp only [Generator.MatrixUnitSystem.hom_apply, permutationMatrix_apply,
    ite_smul, one_smul, zero_smul]
  rw [Finset.sum_comm]
  simp

variable (E : Generator.MatrixUnitSystem ι A) (F : Generator.MatrixUnitSystem (ι × κ) A)
  (hretain : ∀ i j, ∑ k, F.entry (i, k) (j, k) = E.entry i j)

include hretain in
theorem signedDiagonal_refinement (d : ι → ℤˣ) :
    (matrixUnitSignedRepresentation F (SemidirectProduct.inl (fun p : ι × κ => d p.1)) : A) =
      matrixUnitSignedRepresentation E (SemidirectProduct.inl d) := by
  rw [signedRepresentation_diagonal, signedRepresentation_diagonal, Fintype.sum_prod_type]
  simp_rw [← Finset.smul_sum, hretain]

include hretain in
theorem signedPermutation_refinement (σ : Equiv.Perm ι) :
    (matrixUnitSignedRepresentation F
      (SemidirectProduct.inr (σ.prodCongr (Equiv.refl κ))) : A) =
      matrixUnitSignedRepresentation E (SemidirectProduct.inr σ) := by
  rw [signedRepresentation_permutation, signedRepresentation_permutation,
    Fintype.sum_prod_type]
  simp only [Equiv.prodCongr_apply, Prod.map_apply, Equiv.refl_apply, hretain]

include hretain in
/-- Every old signed unitary is a new signed unitary after compatible refinement. -/
theorem matrixSignedGroup_refinement : matrixSignedGroup E ≤ matrixSignedGroup F := by
  rintro u ⟨g, rfl⟩
  let g' : SignedPermutation (ι × κ) :=
    SemidirectProduct.inl (fun p => g.left p.1) *
      SemidirectProduct.inr (g.right.prodCongr (Equiv.refl κ))
  refine ⟨g', ?_⟩
  apply Subtype.ext
  rw [show g' = SemidirectProduct.inl (fun p => g.left p.1) *
      SemidirectProduct.inr (g.right.prodCongr (Equiv.refl κ)) from rfl, map_mul]
  change (matrixUnitSignedRepresentation F (SemidirectProduct.inl (fun p => g.left p.1)) : A) *
      (matrixUnitSignedRepresentation F
        (SemidirectProduct.inr (g.right.prodCongr (Equiv.refl κ))) : A) = _
  rw [signedDiagonal_refinement E F hretain, signedPermutation_refinement E F hretain,
    ← Submonoid.coe_mul, ← map_mul]
  congr 2
  exact SemidirectProduct.inl_left_mul_inr_right g

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_WeakMapCompact
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

local instance weakMapCompactOrder (M : VonNeumannAlgebra H) : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance weakMapCompactStarOrder (M : VonNeumannAlgebra H) : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _

structure BoundedWeakAlgebraMap (M : VonNeumannAlgebra H) (c : ℝ) where
  map : Algebra M →ₗ[ℂ] Algebra M
  bound : CompletelyBoundedBy map c

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_WeakRowAction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! Finite row averages act continuously on the compact completely bounded ball. -/

namespace KadisonKastler

noncomputable section

open scoped Topology InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance weakRowActionOrder_rdab73d_1 (M : VonNeumannAlgebra H) : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance weakRowActionStarOrder_rdab73d_1 (M : VonNeumannAlgebra H) : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _
def boundedWeakRowAverage {M : VonNeumannAlgebra H} {c : ℝ} (hc : 0 ≤ c)
    {n : ℕ} (r : Fin n → Algebra M) (hr : ∑ i, r i * star (r i) = 1)
    (F : BoundedWeakAlgebraMap M c) : BoundedWeakAlgebraMap M c :=
  ⟨finiteRightAverage r F.map, F.bound.finiteRightAverage hc r hr⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SimultaneousRowFamily
attribute [-instance] _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! A compact product keeps the same normalized rows for an entire family
of completely bounded maps. Minimality descends to each coordinate. -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {J : Type*} {c : J → ℝ}

abbrev WeakMapFamily (M : VonNeumannAlgebra H) {J : Type*} (c : J → ℝ) :=
  ∀ j, BoundedWeakAlgebraMap M (c j)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SpatialAssociatorAlgebra
attribute [-instance] _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Associativity of represented spatial von Neumann products

The canonical Hilbert tensor associator transports the actual spatial
product algebras. The passage from algebraic generators to their von
Neumann algebras uses the existing bounded Kaplansky approximation input.
-/

namespace KadisonKastler

open UnitalTomsWinter Generator Filter
open scoped TensorProduct Topology

noncomputable section

universe u

section Generated

variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem generated_of_vonNeumann (A : VonNeumannAlgebra H) :
    generatedVonNeumannAlgebra A.toStarSubalgebra = A := by
  apply le_antisymm
  · exact generatedVonNeumannAlgebra_le_of_le _ A le_rfl
  · exact subset_generatedVonNeumannAlgebra _

end Generated

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SwappedBoundaryMean
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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

namespace NonsingularAction

variable (α : NonsingularAction G D μ)

def rightOnProduct : NonsingularAction G (D × D) (μ.prod μ) where
  toPerm :=
    { toFun := fun g => Equiv.prodCongr (Equiv.refl D) (α.toPerm g)
      map_one' := by ext z <;> simp
      map_mul' g h := by ext z <;> simp }
  quasi g := MeasureTheory.QuasiMeasurePreserving.prodMap
    (Measure.QuasiMeasurePreserving.id μ) (α.quasi g)

end NonsingularAction

end

end KadisonKastler

end OAI
end


