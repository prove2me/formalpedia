-- Prove2me | Definitions.Def_Q260K017
-- name    : Q260K017
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T05:01:40.169241+00:00
-- url     : https://prove2.me/theorems/e7e8586e-2297-45f5-803c-d1d6e7a37bd3
-- title:
--   Definitions bundle Q260K017 of the split of OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 172 declarations of OpenAI's Lean: 50 definitions, 4 inductive types or structures, 3 instances and 115 theorems. The definitions and types are `OAI.KadisonKastler.FaithfulTracialState.toContinuousLinearMap`, `OAI.KadisonKastler.FirstBoundaryProjection`, `OAI.KadisonKastler.FullMatrixCorner.cuntzFamily`, `OAI.KadisonKastler.FullMatrixCorner.finiteCuntz`, `OAI.KadisonKastler.FullMatrixCorner.periodicMatrixUnits`, `OAI.KadisonKastler.FullMatrixCorner.scalarMatrixAlgebra`, `OAI.KadisonKastler.FullMatrixCorner.scalarMatrixInitialProjection`, `OAI.KadisonKastler.FullMatrixCorner.signedGroupUnion`, `OAI.KadisonKastler.FullMatrixCorner.spatialTransport`, `OAI.KadisonKastler.FullMatrixFrame`, `OAI.KadisonKastler.FullMatrixFrame.ambientUnits`, `OAI.KadisonKastler.FullMatrixFrame.group`, `OAI.KadisonKastler.FullMatrixFrame.ofUnits`, `OAI.KadisonKastler.IsTypeIFactor`, `OAI.KadisonKastler.NormNullSequence`, `OAI.KadisonKastler.NormUltraproduct`, `OAI.KadisonKastler.PublishedBoundary`, `OAI.KadisonKastler.PublishedTypeIInjectivity`, `OAI.KadisonKastler.RowInvariant`, `OAI.KadisonKastler.ScalarInvariantProjection`, `OAI.KadisonKastler.ScalarNonnegative`, `OAI.KadisonKastler.WeakOperatorField.coefficient`, `OAI.KadisonKastler.WeakOperatorField.coefficientFamily`, `OAI.KadisonKastler.WeakOperatorField.uniformFamily`, `OAI.KadisonKastler.baireChosenBranch`, `OAI.KadisonKastler.baireChosenWord`, `OAI.KadisonKastler.baireImageHull`, `OAI.KadisonKastler.baireNextDigit`, `OAI.KadisonKastler.baireNextPredicate`, `OAI.KadisonKastler.canonicalMatrixCorner`, `OAI.KadisonKastler.countableOperatorEntry`, `OAI.KadisonKastler.countableTensorAlgebraic`, `OAI.KadisonKastler.countableTensorBilinear`, `OAI.KadisonKastler.countableTensorEquiv`, `OAI.KadisonKastler.countableTensorIsometry`, `OAI.KadisonKastler.countableTensorVector`, `OAI.KadisonKastler.denseSeparatingUnitVector`, `OAI.KadisonKastler.firstBoundaryLiftL`, `OAI.KadisonKastler.normNullClosedIdeal`, `OAI.KadisonKastler.normProductMap` and 14 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `FactorGeneration_NormalTrace`, `KadisonKastler_AdaptedMatrixRefinement`, `KadisonKastler_AmplifiedAlgebra`, `KadisonKastler_BaireMeasurableBranch`, `KadisonKastler_BaireSelectionHulls`, `KadisonKastler_Basic`, `KadisonKastler_BoundaryBoundedTransport`, `KadisonKastler_CanonicalAmplificationGap`, `KadisonKastler_CanonicalMatrixCorner`, `KadisonKastler_CompatibleMatrixFrames`, `KadisonKastler_ConcreteTraceUniqueness`, `KadisonKastler_CornerCuntzFamily`, `KadisonKastler_CountableAmplificationNormal`, `KadisonKastler_CountableOperatorEntries`, `KadisonKastler_CountableSpatialTensor`, `KadisonKastler_FiniteCornerGroups`, `KadisonKastler_FiniteCornerRefinement`, `KadisonKastler_FullCornerEmbedding`, `KadisonKastler_FullMatrixInjectivity`, `KadisonKastler_FullMatrixRefinement`, `KadisonKastler_InflatedConjugacy`, `KadisonKastler_MinimalRowFamily`, `KadisonKastler_NormUltraproduct`, `KadisonKastler_NormUltraproductMaps`, `KadisonKastler_OperatorCoefficientMean`, `KadisonKastler_PeriodicMatrixUnits`, `KadisonKastler_ProductBoundaryAlgebra`, `KadisonKastler_ProductBoundaryLifts`, `KadisonKastler_PublishedBoundary`, `KadisonKastler_PublishedTypeIInjectivity`, `KadisonKastler_RemoteSiteDoubling`, `KadisonKastler_ScalarBoundaryMean`, `KadisonKastler_ScalarCesaroCommutation`, `KadisonKastler_ScalarInvariantProjection`, `KadisonKastler_ScalarL2Multiplication`, `KadisonKastler_ScalarPositiveLimit`, `KadisonKastler_ScalarPullbackAlgebra`, `KadisonKastler_ScalarPullbackWeakGraph`, `KadisonKastler_ScalarShiftCesaro`, `KadisonKastler_ScalarWeakLimit`, `KadisonKastler_TwoRatioFiniteMatrix`, `KadisonKastler_TwoRatioFiniteSites`, `KadisonKastler_TwoRatioRemoteBlock`, `KadisonKastler_TwoRatioRemoteComplement`, `KadisonKastler_TypeIIIMatrixCorner`, `KadisonKastler_WeakFieldCoefficients`, `KadisonKastler_WeakFieldPullback`, `KadisonKastler_WeakOperatorCoefficients`.
--
--   **Imports.** It imports the published bundle `Def_StrongKadisonKastler`; the bundles `Q260K009`, `Q260K010`, `Q260K011`, `Q260K012` and `Q260K013` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q260K022`, `Q260K023`, `Q260K024`, `Q260K025` and `Q260K057`; the statements `OAI.KadisonKastler.FullMatrixCorner.scalarMatrixAlgebra_isInjective`, `OAI.KadisonKastler.minimal_row_family_right_module_of_factorization` and `OAI.KadisonKastler.publishedBoundary`; the proofs of `OAI.KadisonKastler.FullMatrixCorner.exists_injective_algebra_containing_entries`, `OAI.KadisonKastler.ScalarInvariantMean.algebraMean_translate`, `OAI.KadisonKastler.exists_group_representation_of_mean`, `OAI.KadisonKastler.exists_unitary_boundary_intertwiner` and `OAI.KadisonKastler.kkDistance_regularTensor_conjugate_le`.
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
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
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
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Group.Tannery
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
import Mathlib.Analysis.Normed.Operator.Mul
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
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Topology.MetricSpace.Cauchy
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
import Definitions.Def_StrongKadisonKastler
import Definitions.Def_Q260K009
import Definitions.Def_Q260K010
import Definitions.Def_Q260K011
import Definitions.Def_Q260K012
import Definitions.Def_Q260K013

section
-- module Solutions.OAIQ075_KS.FactorGeneration_NormalTrace
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.algebraCStarAlgebra _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.varyingSequenceCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.Generator.Tracial.cyclicCoefficient_apply _root_.OAI.Generator.Tracial.cyclicPredualEvaluation_apply _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.dyadicCornerHom_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply _root_.OAI.KadisonSimilarity.predualRestriction_apply _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! A genuine linear state with exact equality of real quadratic values,
constructed from the original finite factor predicates by scalar compactness. -/

/-! Construction of a tracial state on the original concrete finite diffuse factor without a supplied trace. -/

/-! Every positive normalized tracial functional agrees with the dimension on
all projections. Lower and upper dyadic bounds use actual partial isometries. -/
section
open scoped BigOperators CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

attribute [local instance] OAI.Generator.Tracial.stateDimensionStarOrder
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

theorem tracialFunctional_dyadic_subset_re (φ : M.toStarSubalgebra →L[ℂ] ℂ)
    (h1 : φ 1=1) (htrace : ∀ x y : M.toStarSubalgebra, φ (x*y)=φ (y*x))
    (n : ℕ) (s : Finset (DyadicIndex n)) :
    (φ ((traceFreeDyadicPartition hfactor hdiff ⟨1,IsStarProjection.one _⟩ n).subset s).val).re=
      dyadicWeight n s := by
  let E := traceFreeDyadicPartition hfactor hdiff ⟨1,IsStarProjection.one _⟩ n
  have he (i : DyadicIndex n) : (φ (E.leg i).target.val).re=(φ E.base.val).re := by
    exact congrArg Complex.re (tracialFunctional_equivalent φ htrace
      (show (E.leg i).target.Equivalent E.base from
        AlgebraProjection.equivalent_symm ⟨E.leg i,E.initial i,rfl⟩))
  have ht := congrArg (fun x : M.toStarSubalgebra => (φ x).re) E.total
  simp only [map_sum,Complex.re_sum,he,Finset.sum_const,Finset.card_univ,
    nsmul_eq_mul,card_dyadicIndex,Nat.cast_pow,Nat.cast_ofNat,h1,Complex.one_re] at ht
  have hb : (φ E.base.val).re=1/(2 : ℝ)^n := by
    apply (eq_div_iff (ne_of_gt (pow_pos (by norm_num : (0 : ℝ)<2) n))).mpr
    nlinarith [ht]
  change (φ (E.subset s).val).re=_
  rw [E.subset_val,map_sum,Complex.re_sum]
  simp only [he,hb,Finset.sum_const,nsmul_eq_mul]
  change (s.card : ℝ)*(1/2^n)=(s.card : ℝ)/2^n
  ring

local instance stateDimensionCStar_rb6d0c3_1 : CStarAlgebra M.toStarSubalgebra := {}
attribute [local instance] OAI.Generator.Tracial.stateDimensionOrder
local instance stateDimensionPreorder_rb6d0c3_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
attribute [local instance] OAI.Generator.Tracial.stateDimensionLE
include hfinite in
theorem tracialFunctional_projection_dimension_re (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (φ : M.toStarSubalgebra →L[ℂ] ℂ) (h1 : φ 1=1)
    (hpos : ∀ x : M.toStarSubalgebra, 0 ≤ x → 0 ≤ (φ x).re)
    (htrace : ∀ x y : M.toStarSubalgebra, φ (x*y)=φ (y*x))
    (p : AlgebraProjection M) : (φ p.val).re=traceFreeDimension hfactor hdiff p := by
  apply eq_of_all_dyadic_errors
  intro n
  obtain ⟨s,t,_,_,hs,ht,hl,hu,hgap⟩ := traceFreeDyadicSup_rounding hfactor hdiff hfinite
    ⟨1,IsStarProjection.one _⟩ p hunit (one_mul _) n
  have hφl := tracialFunctional_subequivalent φ hpos htrace hs
  have hφu := tracialFunctional_subequivalent φ hpos htrace ht
  rw [tracialFunctional_dyadic_subset_re hfactor hdiff φ h1 htrace] at hφl hφu
  change dyadicWeight n s ≤ traceFreeDimension hfactor hdiff p at hl
  change traceFreeDimension hfactor hdiff p ≤ dyadicWeight n t at hu
  have hn : 0 ≤ 1/(2 : ℝ)^n := by positivity
  rw [show (2 : ℝ)/2^n=2*(1/2^n) by ring]
  apply abs_le.mpr
  constructor <;> linarith

include hfinite in
theorem tracialFunctional_projection_dimension (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (φ : M.toStarSubalgebra →L[ℂ] ℂ) (h1 : φ 1=1)
    (hpos : ∀ x : M.toStarSubalgebra, 0 ≤ x → 0 ≤ (φ x).re)
    (hstar : ∀ x : M.toStarSubalgebra, φ (star x)=star (φ x))
    (htrace : ∀ x y : M.toStarSubalgebra, φ (x*y)=φ (y*x))
    (p : AlgebraProjection M) : φ p.val=(traceFreeDimension hfactor hdiff p : ℂ) := by
  apply Complex.ext
  · exact tracialFunctional_projection_dimension_re hfactor hdiff hfinite hunit φ h1 hpos htrace p
  · have h := congrArg Complex.im (hstar p.val)
    rw [p.property.isSelfAdjoint.star_eq] at h
    change (φ p.val).im= -(φ p.val).im at h
    change (φ p.val).im=0
    linarith

end

/-! Identification of the actual tracial state with the spectral dimension
value, and unrestricted additivity for noncommuting self-adjoint operators. -/
section
open scoped BigOperators CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
attribute [local instance] OAI.Generator.Tracial.spectralAdditivityCStar
local instance spectralAdditivityOrder_rb6d0c3_1 : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance spectralAdditivityPreorder_rb6d0c3_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance spectralAdditivityLE_rb6d0c3_1 : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance spectralAdditivityStarOrder_rb6d0c3_1 : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

theorem functional_isDimensionSpectralValue (φ : M.toStarSubalgebra →L[ℂ] ℂ)
    (hnorm : ‖φ‖ ≤ 1)
    (hproj : ∀ p : AlgebraProjection M, φ p.val=(traceFreeDimension hfactor hdiff p : ℂ))
    (x : M.toStarSubalgebra) : IsDimensionSpectralValue hfactor hdiff x (φ x) := by
  intro Q c _
  have he : φ (∑ i, c i • (Q.piece i).val)=
      ∑ i, c i*(traceFreeDimension hfactor hdiff (Q.piece i) : ℂ) := by
    simp only [map_sum,map_smul,smul_eq_mul,hproj]
  rw [← he,← map_sub]
  simpa only [one_mul] using φ.le_of_opNorm_le hnorm (x-∑ i, c i • (Q.piece i).val)

end

/-! The constructed faithful normalized trace on the original algebra.
Projection-net continuity is proved explicitly; no general normality or
representation theorem is hidden in the definition. -/

/-! The constructed trace is dominated by a finite sum of concrete vector
functionals. The matrix partition is constructed inside the localized corner. -/

/-! Finite vector-functional representation and actual ultraweak continuity of
the constructed trace. No normality criterion is taken as an axiom. -/
open scoped BigOperators CStarAlgebra

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_Basic
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

theorem unitBall_hausdorffEDist_ne_top (M N : VonNeumannAlgebra H) :
    Metric.hausdorffEDist (unitBall M) (unitBall N) ≠ ⊤ :=
  Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded
    (unitBall_nonempty M) (unitBall_nonempty N) (unitBall_bounded M) (unitBall_bounded N)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_AdaptedMatrixRefinement
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.concrete_finiteDimensional _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.MatrixSiteWord.eval_append _root_.OAI.KadisonKastler.MatrixSiteWord.eval_cons _root_.OAI.KadisonKastler.MatrixSiteWord.eval_nil _root_.OAI.KadisonKastler.MatrixSiteWord.eval_reindex _root_.OAI.KadisonKastler.MatrixSiteWord.eval_star _root_.OAI.KadisonKastler.conjugatedMatrixUnits_entry _root_.OAI.KadisonKastler.matrixPermutationValue_one _root_.OAI.KadisonKastler.spatialMatrixUnits_entry _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Refining matrix units while retaining their finite signed group -/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {H ι κ : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

variable (E : Generator.MatrixUnitSystem ι (H →L[ℂ] H)) (o : ι)
  (b : OrthonormalBasis κ ℂ (E.initialHilbertSpace o))

/-- Rank-one units for the adapted basis retain each old matrix entry as
a sum over the new index. -/
theorem adaptedMatrixUnits_retains (i j : ι) :
    ∑ r, (Generator.orthonormalMatrixUnits (E.adaptedBasis o b)).entry (i, r) (j, r) =
      E.entry i j := by
  let B := E.adaptedBasis o b
  change (∑ r, (Generator.orthonormalMatrixUnits B).entry (i, r) (j, r)) = E.entry i j
  have hb (p : ι × κ) :
      (∑ r, (Generator.orthonormalMatrixUnits B).entry (i, r) (j, r)) (B p) =
        E.entry i j (B p) := by
    obtain ⟨k, s⟩ := p
    rw [sum_apply, E.entry_adaptedBasis]
    simp only [Generator.orthonormalMatrixUnits_entry_apply, B.inner_eq_ite, Prod.mk.injEq]
    by_cases h : j = k
    · subst k
      simp [B]
    · simp [h]
  apply ContinuousLinearMap.ext
  intro x
  rw [← B.sum_repr' x]
  simp only [map_sum, map_smul, hb]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_InflatedConjugacy
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.finiteSignedGroup_finite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Recovering the full algebra from its common matrix corners -/

namespace KadisonKastler

open Filter
open scoped BigOperators Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {E : Submodule ℂ H} [CompleteSpace E]

namespace FullMatrixCorner

variable (F : FullMatrixCorner E)

theorem partialDiagonal_star (s : Finset ℕ) :
    star (F.partialDiagonal s) = F.partialDiagonal s := by
  simp only [partialDiagonal, star_sum, F.star_entry]

theorem partialDiagonal_tendsto (x : H) :
    Tendsto (fun s : Finset ℕ => F.partialDiagonal s x) atTop (𝓝 x) := by
  simpa only [HasSum, SummationFilter.unconditional, partialDiagonal, sum_apply] using
    F.total x

end FullMatrixCorner

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CornerCuntzFamily
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.finiteSignedGroup_finite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

theorem ext_on_columns {T U : H →L[ℂ] H}
    (h : ∀ k x, T (F.column k x) = U (F.column k x)) : T = U := by
  apply ContinuousLinearMap.ext
  intro x
  have he (s : Finset ℕ) : T (F.partialDiagonal s x) = U (F.partialDiagonal s x) := by
    simp only [partialDiagonal, sum_apply, map_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [F.diagonal_apply, h]
  exact tendsto_nhds_unique
    ((T.continuous.continuousAt.tendsto.comp (F.partialDiagonal_tendsto x)).congr he)
    (U.continuous.continuousAt.tendsto.comp (F.partialDiagonal_tendsto x))

variable {n : Type*} (e : n × ℕ ≃ ℕ)

variable [DecidableEq n]

theorem regrouping_orthogonal (i j : n) :
    star (F.regroupingOperator e i) * F.regroupingOperator e j =
      if i = j then 1 else 0 := by
  apply F.ext_on_columns
  intro k x
  simp only [mul_apply_eq_comp, F.regroupingOperator_column, F.adjoint_regrouping_column]
  split_ifs <;> rfl

variable [Fintype n]

theorem regrouping_total :
    ∑ i, F.regroupingOperator e i * star (F.regroupingOperator e i) = 1 := by
  apply F.ext_on_columns
  intro k x
  obtain ⟨⟨j, l⟩, rfl⟩ := e.surjective k
  simp only [sum_apply, mul_apply_eq_comp, F.adjoint_regrouping_column]
  simp only [apply_ite, map_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
  exact F.regroupingOperator_column e j l x

/-- This construction is independent of the algebra that contains the
matrix units, so the same family can be used on both sides of a gap. -/
def cuntzFamily : CuntzFamily n H where
  entry := F.regroupingOperator e
  orthogonal := F.regrouping_orthogonal e
  total := F.regrouping_total e

/-- Every positive matrix size is obtained from the same countable matrix
units by the quotient-and-remainder bijection. -/
def finiteCuntz (n : ℕ) [NeZero n] : CuntzFamily (Fin n) H :=
  F.cuntzFamily ((Equiv.prodComm (Fin n) ℕ).trans (Nat.divModEquiv n).symm)

end FullMatrixCorner

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_AmplifiedAlgebra
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.finiteSignedGroup_finite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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

theorem inflateHom_commute_entry (T : E →L[ℂ] E) (i j : ℕ) :
    Commute (F.inflateHom T) (F.entry i j) := by
  apply F.ext_on_columns
  intro k x
  simp only [mul_apply_eq_comp, F.entry_column, F.inflateHom_column]
  split_ifs
  · exact F.inflateHom_column T i x
  · simp

end FullMatrixCorner

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BaireSelectionHulls
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

variable {X : Type*} [MeasurableSpace X]

variable [TopologicalSpace X] [BorelSpace X]

def baireImageHull (μ : Measure X) (F : (ℕ → ℕ) → X) (s : List ℕ) : Set X :=
  toMeasurable μ (F '' bairePrefixCylinder s) ∩ closure (F '' bairePrefixCylinder s)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BaireMeasurableBranch
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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

def baireNextPredicate (μ : Measure X) (F : (ℕ → ℕ) → X)
    (s : List ℕ) (x : X) (n : ℕ) : Prop :=
  x ∈ baireImageHull μ F (n :: s) ∨
    (n = 0 ∧ ¬∃ m, x ∈ baireImageHull μ F (m :: s))

omit [BorelSpace X] in
theorem baireNextPredicate_exists (μ : Measure X) (F : (ℕ → ℕ) → X) (s : List ℕ) (x : X) :
    ∃ n, baireNextPredicate μ F s x n := by
  classical
  by_cases h : ∃ n, x ∈ baireImageHull μ F (n :: s)
  · obtain ⟨n, hn⟩ := h
    exact ⟨n, Or.inl hn⟩
  · exact ⟨0, Or.inr ⟨rfl, h⟩⟩

@[irreducible] def baireNextDigit (μ : Measure X) (F : (ℕ → ℕ) → X) (s : List ℕ) (x : X) : ℕ := by
  classical
  exact Nat.find (baireNextPredicate_exists μ F s x)

def baireChosenWord (μ : Measure X) (F : (ℕ → ℕ) → X) : ℕ → X → List ℕ
  | 0, _ => []
  | n + 1, x => baireNextDigit μ F (baireChosenWord μ F n x) x :: baireChosenWord μ F n x

omit [BorelSpace X] in
@[simp] theorem baireChosenWord_length (μ : Measure X) (F : (ℕ → ℕ) → X) (n : ℕ) (x : X) :
    (baireChosenWord μ F n x).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [baireChosenWord, ih]

def baireChosenBranch (μ : Measure X) (F : (ℕ → ℕ) → X) (x : X) (n : ℕ) : ℕ :=
  baireNextDigit μ F (baireChosenWord μ F n x) x

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BoundaryBoundedTransport
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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

local instance boundaryBoundedComplete_rb6d0c3_1 : CompleteSpace (unitary (G →ᵇ B)) :=
  isClosed_unitary.completeSpace_coe
attribute [local instance] OAI.KadisonKastler.boundaryBoundedStarOrder
@[simp]
theorem boundaryTranslate_apply (α : G →* (B ≃⋆ₐ[ℂ] B)) (g : G)
    (f : G →ᵇ B) (t : G) : boundaryTranslate α g f t = α g (f (g⁻¹ * t)) := rfl

omit [Group G] in
@[simp]
theorem boundedUnitaryFamily_apply (V : G → unitary B) (g : G) :
    (boundedUnitaryFamily V).val g = (V g : B) := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CanonicalMatrixCorner
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.finiteSignedGroup_finite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.FullMatrixCorner.regroupingIsometry_column _root_.OAI.KadisonKastler.FullMatrixCorner.regroupingOperator_column _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The canonical countable matrix corner

The coordinate injections and evaluations on the Hilbert direct sum give
actual matrix units.  Their initial corner is canonically isometric to
the original Hilbert space, and their diagonal projections sum strongly
to the identity.
-/

namespace KadisonKastler

noncomputable section

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable [CompleteSpace H]

theorem canonicalSingle_adjoint (i : ℕ) :
    (canonicalSingle H i).adjoint = canonicalCoordinate H i := by
  apply Eq.symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  exact (lp.inner_single_right (𝕜 := ℂ) i y x).symm

theorem canonicalMatrixUnit_star (i j : ℕ) :
    star (canonicalMatrixUnit H i j) = canonicalMatrixUnit H j i := by
  have hc : (canonicalCoordinate H j).adjoint = canonicalSingle H j := by
    rw [← canonicalSingle_adjoint, ContinuousLinearMap.adjoint_adjoint]
  simp only [canonicalMatrixUnit, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_comp, canonicalSingle_adjoint, hc]

theorem canonicalMatrixUnit_zero_zero :
    canonicalMatrixUnit H 0 0 = (canonicalInitialSpace H).starProjection := by
  apply ContinuousLinearMap.ext
  intro x
  apply Eq.symm
  apply (canonicalInitialSpace H).eq_starProjection_of_mem_of_inner_eq_zero
  · exact ⟨x 0, rfl⟩
  · intro w hw
    obtain ⟨y, rfl⟩ := hw
    change inner ℂ (x - lp.single 2 0 (x 0)) (lp.single 2 0 y) = 0
    rw [lp.inner_single_right]
    simp [lp.single_apply]

/-- The standard countable matrix units on the Hilbert direct sum. -/
def canonicalMatrixCorner : FullMatrixCorner (canonicalInitialSpace H) where
  entry := canonicalMatrixUnit H
  star_entry := canonicalMatrixUnit_star H
  mul_entry := canonicalMatrixUnit_mul H
  zero_zero := canonicalMatrixUnit_zero_zero H
  total x := lp.hasSum_single (by norm_num) x

@[simp] theorem canonicalMatrixCorner_entry (i j : ℕ) :
    (canonicalMatrixCorner H).entry i j = canonicalMatrixUnit H i j := rfl

@[simp] theorem canonicalMatrixCorner_column (i : ℕ) (x : H) :
    (canonicalMatrixCorner H).column i (canonicalInitialEquiv H x) =
      lp.single 2 i x := by
  change canonicalMatrixUnit H i 0 (lp.single 2 0 x) = _
  rw [canonicalMatrixUnit_apply]
  simp [lp.single_apply]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CanonicalAmplificationGap
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.KadisonKastler.FullMatrixCorner.finiteSignedGroup_finite _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The canonical amplification gap from common matrix units

Actual countable matrix units transport under a Hilbert-space isometry.
Thus the common-matrix-unit gap estimate applies to the canonical Hilbert
sum of the original representation, retaining its original tolerance.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {D : Submodule ℂ H} [CompleteSpace D]

namespace FullMatrixCorner

variable (F : FullMatrixCorner D)

/-- Transport of all the matrix units, including the strong sum condition. -/
def spatialTransport (e : H ≃ₗᵢ[ℂ] K) :
    FullMatrixCorner (D.map e.toLinearEquiv.toLinearMap) where
  entry i j := e.conjStarAlgEquiv (F.entry i j)
  star_entry i j := by
    calc
      star (e.conjStarAlgEquiv (F.entry i j)) =
          e.conjStarAlgEquiv (star (F.entry i j)) :=
        (StarHomClass.map_star e.conjStarAlgEquiv (F.entry i j)).symm
      _ = e.conjStarAlgEquiv (F.entry j i) :=
        congrArg e.conjStarAlgEquiv (F.star_entry i j)
  mul_entry i j k l := by
    rw [← map_mul, F.mul_entry]
    split_ifs <;> simp only [map_zero]
  zero_zero := by
    rw [F.zero_zero]
    apply ContinuousLinearMap.ext
    intro x
    exact (Submodule.starProjection_map_apply e D x).symm
  total x := by
    have h := e.toContinuousLinearEquiv.toContinuousLinearMap.hasSum (F.total (e.symm x))
    change HasSum (fun i => e (F.entry i i (e.symm x))) (e (e.symm x)) at h
    rw [e.apply_symm_apply] at h
    exact h

@[simp] theorem spatialTransport_entry (e : H ≃ₗᵢ[ℂ] K) (i j : ℕ) :
    (F.spatialTransport e).entry i j = e.conjStarAlgEquiv (F.entry i j) := rfl

end FullMatrixCorner

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FullMatrixRefinement
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.concrete_finiteDimensional _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFiniteBoundedWord _root_.OAI.HochschildPatching.instFiniteLinearLabel _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Compatible refinement inside a full matrix algebra

Pass to a finite Hilbert-space representation, use the adapted basis, and
transport its rank-one matrix units back. The old signed group is retained.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {A ι : Type*}
  [Ring A]
  [StarRing A]
  [_root_.Algebra ℂ A]
  [StarModule ℂ A]
  [Fintype ι]
  [DecidableEq ι]

theorem matrixUnits_map_hom (E : Generator.MatrixUnitSystem ι A)
    {B : Type*} [Ring B] [StarRing B] [_root_.Algebra ℂ B] [StarModule ℂ B]
    (φ : A →⋆ₐ[ℂ] B) (a : Matrix ι ι ℂ) : (E.map φ).hom a = φ (E.hom a) := by
  simp only [Generator.MatrixUnitSystem.hom_apply, Generator.MatrixUnitSystem.map_entry,
    map_sum, map_smul]

variable [Nontrivial A]

/-- A matrix system in a finite full operator algebra extends to a full
system whose signed group contains the original one. -/
theorem exists_matrix_refinement_of_finite_representation
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [FiniteDimensional ℂ H] (θ : A ≃⋆ₐ[ℂ] (H →L[ℂ] H))
    (E : Generator.MatrixUnitSystem ι A) (o : ι) :
    ∃ (r : ℕ) (F : Generator.MatrixUnitSystem (ι × Fin r) A),
      0 < r ∧ Function.Surjective F.hom ∧
      (∀ i j, ∑ k, F.entry (i, k) (j, k) = E.entry i j) ∧
      matrixSignedGroup E ≤ matrixSignedGroup F := by
  let E' := E.map θ.toStarAlgHom
  let r := Module.finrank ℂ (E'.initialHilbertSpace o)
  let b := stdOrthonormalBasis ℂ (E'.initialHilbertSpace o)
  let Q := Generator.orthonormalMatrixUnits (E'.adaptedBasis o b)
  let F := Q.map θ.symm.toStarAlgHom
  have hfull : Function.Surjective F.hom := by
    intro a
    obtain ⟨x, hx⟩ := Generator.orthonormalMatrixUnits_surjective (E'.adaptedBasis o b) (θ a)
    refine ⟨x, ?_⟩
    rw [matrixUnits_map_hom, hx]
    exact θ.symm_apply_apply a
  have hretain (i j : ι) : ∑ k, F.entry (i, k) (j, k) = E.entry i j := by
    change ∑ k, θ.symm (Q.entry (i, k) (j, k)) = E.entry i j
    rw [← map_sum, adaptedMatrixUnits_retains]
    exact θ.symm_apply_apply _
  have hr : 0 < r := by
    by_contra h
    have hz : r = 0 := Nat.eq_zero_of_not_pos h
    let : IsEmpty (ι × Fin r) := by rw [hz]; infer_instance
    have ht := F.total
    have he : (0 : A) = 1 := by simpa only [Finset.univ_eq_empty, Finset.sum_empty] using ht
    exact zero_ne_one he
  exact ⟨r, F, hr, hfull, hretain, matrixSignedGroup_refinement E F hretain⟩

/-- The only representation data needed above are supplied by any full
matrix system for the containing algebra. -/
theorem exists_matrix_refinement_in_full_matrix_algebra
    {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (P : Generator.MatrixUnitSystem κ A) (hP : Function.Surjective P.hom)
    (E : Generator.MatrixUnitSystem ι A) (o : ι) :
    ∃ (r : ℕ) (F : Generator.MatrixUnitSystem (ι × Fin r) A),
      0 < r ∧ Function.Surjective F.hom ∧
      (∀ i j, ∑ k, F.entry (i, k) (j, k) = E.entry i j) ∧
      matrixSignedGroup E ≤ matrixSignedGroup F := by
  let θ₀ : Matrix κ κ ℂ ≃⋆ₐ[ℂ] A :=
    StarAlgEquiv.ofBijective P.hom ⟨P.injective, hP⟩
  let θ := θ₀.symm.trans (Matrix.toEuclideanCLM (𝕜 := ℂ))
  exact exists_matrix_refinement_of_finite_representation θ E o

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CompatibleMatrixFrames
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.concrete_finiteDimensional _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildMatrixSystems.MatrixSystem.signedPermutationGroup_finite _root_.OAI.HochschildPatching.instFiniteBoundedWord _root_.OAI.HochschildPatching.instFiniteLinearLabel _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.finiteSignedGroup_finite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.MatrixSiteWord.eval_append _root_.OAI.KadisonKastler.MatrixSiteWord.eval_cons _root_.OAI.KadisonKastler.MatrixSiteWord.eval_nil _root_.OAI.KadisonKastler.MatrixSiteWord.eval_reindex _root_.OAI.KadisonKastler.MatrixSiteWord.eval_star _root_.OAI.KadisonKastler.conjugatedMatrixUnits_entry _root_.OAI.KadisonKastler.matrixPermutationValue_one _root_.OAI.KadisonKastler.spatialMatrixUnits_entry _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Compatible finite groups for an increasing matrix chain

The finite index set is retained as data, so tensor refinements do not
require changing the represented operators or reindexing to a fixed type.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A full matrix system for a concrete algebra, with a finite nonempty index. -/
structure FullMatrixFrame (A : StarSubalgebra ℂ (H →L[ℂ] H)) where
  Index : Type
  fintype : Fintype Index
  decidableEq : DecidableEq Index
  point : Index
  units : Generator.MatrixUnitSystem Index A
  full : Function.Surjective units.hom

attribute [instance] FullMatrixFrame.fintype FullMatrixFrame.decidableEq

namespace FullMatrixFrame

variable {A B : StarSubalgebra ℂ (H →L[ℂ] H)}

instance index_nonempty (F : FullMatrixFrame A) : Nonempty F.Index := ⟨F.point⟩

def ambientUnits (F : FullMatrixFrame A) : Generator.MatrixUnitSystem F.Index (H →L[ℂ] H) :=
  F.units.map A.subtype

def group (F : FullMatrixFrame A) : Subgroup (unitary (H →L[ℂ] H)) :=
  matrixSignedGroup F.ambientUnits

instance group_finite (F : FullMatrixFrame A) : Finite F.group :=
  matrixSignedGroup_finite _

theorem ambientUnits_algebra (F : FullMatrixFrame A) : F.ambientUnits.algebra = A := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    change (F.units.map A.subtype).hom a ∈ A
    rw [matrixUnits_map_hom]
    exact (F.units.hom a).property
  · intro hx
    obtain ⟨a, ha⟩ := F.full ⟨x, hx⟩
    refine ⟨a, ?_⟩
    change (F.units.map A.subtype).hom a = x
    rw [matrixUnits_map_hom, ha]
    rfl

theorem group_mem (F : FullMatrixFrame A) (u : F.group) : (u : H →L[ℂ] H) ∈ A := by
  obtain ⟨g, hg⟩ := u.property
  have h := F.ambientUnits_algebra.le (matrixUnitSignedRepresentation_mem F.ambientUnits g)
  rw [hg] at h
  exact h

/-- A full matrix frame is obtained from a specified matrix-unit range. -/
def ofUnits {ι : Type} [Fintype ι] [DecidableEq ι]
    (E : Generator.MatrixUnitSystem ι (H →L[ℂ] H)) (o : ι) : FullMatrixFrame E.algebra := by
  let P : Generator.MatrixUnitSystem ι E.algebra :=
    { entry i j := ⟨E.entry i j, E.entry_mem i j⟩
      star_entry i j := Subtype.ext (E.star_entry i j)
      mul_entry i j k l := Subtype.ext (by
        change E.entry i j * E.entry k l = _
        rw [E.mul_entry]
        split_ifs <;> rfl)
      total := Subtype.ext (by simpa using E.total) }
  refine ⟨ι, inferInstance, inferInstance, o, P, ?_⟩
  rintro ⟨x, a, ha⟩
  refine ⟨a, Subtype.ext ?_⟩
  change ((P.hom a : E.algebra) : H →L[ℂ] H) = x
  calc
    _ = E.hom a := by
      change E.algebra.subtype (P.hom a) = _
      rw [← matrixUnits_map_hom]
      rfl
    _ = x := ha

variable [Nontrivial H]

/-- Refine a frame inside a larger full matrix algebra while retaining the
actual ambient finite group. -/
theorem exists_refinement (E : FullMatrixFrame A) (P : FullMatrixFrame B) (hAB : A ≤ B) :
    ∃ F : FullMatrixFrame B, E.group ≤ F.group := by
  let j := StarSubalgebra.inclusion hAB
  obtain ⟨r, Q, hr, hfull, hretain, _⟩ := exists_matrix_refinement_in_full_matrix_algebra
    P.units P.full (E.units.map j) E.point
  let F : FullMatrixFrame B :=
    ⟨E.Index × Fin r, inferInstance, inferInstance, (E.point, ⟨0, hr⟩), Q, hfull⟩
  refine ⟨F, ?_⟩
  apply matrixSignedGroup_refinement E.ambientUnits F.ambientUnits
  intro i k
  change (∑ a, ((Q.entry (i, a) (k, a) : B) : H →L[ℂ] H)) =
    ((E.units.entry i k : A) : H →L[ℂ] H)
  have hh := congrArg (fun b : B => (b : H →L[ℂ] H)) (hretain i k)
  simpa [Generator.MatrixUnitSystem.map_entry, j] using hh

end FullMatrixFrame

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ConcreteTraceUniqueness
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

def FaithfulTracialState.toContinuousLinearMap (τ : FaithfulTracialState B) : B →L[ℂ] ℂ :=
  τ.toLinearMap.mkContinuous 1 (fun x => by simpa only [one_mul] using τ.norm_apply_le_norm x)

theorem FaithfulTracialState.norm_toContinuousLinearMap_le (τ : FaithfulTracialState B) :
    ‖τ.toContinuousLinearMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound τ.toContinuousLinearMap zero_le_one
  intro x
  change ‖τ.toLinearMap x‖ ≤ 1 * ‖x‖
  simpa only [one_mul] using τ.norm_apply_le_norm x

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CountableAmplificationNormal
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Normality and separating vectors for countable amplification

Bounded weak operator limits pass through the countable diagonal action.
A weighted dense sequence is a separating vector for that action. These
are the concrete ingredients for a faithful cyclic representation.
-/

namespace KadisonKastler

open Filter TopologicalSpace
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem l2Diagonal_tendsto_weak {ι : Type*} {l : Filter ι}
    (T : ι → H →L[ℂ] H) (S : H →L[ℂ] H) (C : ℝ)
    (hC : ∀ᶠ i in l, ‖T i‖ ≤ C)
    (hT : ∀ x y : H, Tendsto (fun i => inner ℂ y (T i x)) l
      (𝓝 (inner ℂ y (S x))))
    (x y : CountableHilbertSum H) :
    Tendsto (fun i => inner ℂ y (l2Diagonal (T i) x)) l
      (𝓝 (inner ℂ y (l2Diagonal S x))) := by
  simp only [lp.inner_eq_tsum, l2Diagonal_apply]
  apply tendsto_tsum_of_dominated_convergence
    ((lp.summable_mul (by rw [Real.holderConjugate_iff]; norm_num) y x).mul_left C)
    (fun n => hT (x n) (y n))
  filter_upwards [hC] with i hi n
  calc
    ‖inner ℂ (y n) (T i (x n))‖ ≤ ‖y n‖ * ‖T i (x n)‖ := norm_inner_le_norm _ _
    _ ≤ ‖y n‖ * (C * ‖x n‖) := mul_le_mul_of_nonneg_left
      ((T i).le_opNorm (x n) |>.trans (mul_le_mul_of_nonneg_right hi (norm_nonneg _)))
      (norm_nonneg _)
    _ = C * (‖y n‖ * ‖x n‖) := by ring

variable [SeparableSpace H]

def weightedDenseVector : CountableHilbertSum H :=
  ⟨fun n => (denseSequenceWeight (H := H) n : ℂ) • denseSeq H n, by
    have hg : Memℓp (fun n : ℕ => (1 / 2 : ℝ) ^ n) 2 := by
      apply memℓp_gen
      have h := summable_geometric_of_lt_one (r := (1 / 2 : ℝ) ^ 2)
        (by positivity) (by norm_num)
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs,
        abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), ← pow_mul,
        Nat.mul_comm] using h
    exact hg.mono (norm_weighted_denseSeq_le (H := H))⟩

theorem weightedDenseVector_separating (T : H →L[ℂ] H)
    (hT : l2Diagonal T (weightedDenseVector (H := H)) = 0) : T = 0 := by
  apply DFunLike.ext'
  apply (denseRange_denseSeq H).equalizer T.continuous continuous_const
  funext n
  have h := congrArg (fun x : CountableHilbertSum H => x n) hT
  change T ((denseSequenceWeight (H := H) n : ℂ) • denseSeq H n) = 0 at h
  rw [map_smul] at h
  exact (smul_eq_zero.mp h).resolve_left
    (by exact_mod_cast (denseSequenceWeight_pos (H := H) n).ne')

variable [Nontrivial H]

theorem weightedDenseVector_ne_zero : weightedDenseVector (H := H) ≠ 0 := by
  intro h
  have he : (1 : H →L[ℂ] H) = 0 := weightedDenseVector_separating _ (by
    rw [h, map_zero])
  exact one_ne_zero he

def denseSeparatingUnitVector : CountableHilbertSum H :=
  ((‖weightedDenseVector (H := H)‖⁻¹ : ℝ) : ℂ) • weightedDenseVector

theorem denseSeparatingUnitVector_separating (T : H →L[ℂ] H)
    (hT : l2Diagonal T (denseSeparatingUnitVector (H := H)) = 0) : T = 0 := by
  apply weightedDenseVector_separating
  rw [denseSeparatingUnitVector, map_smul] at hT
  exact (smul_eq_zero.mp hT).resolve_left (by
    exact_mod_cast inv_ne_zero (norm_ne_zero_iff.mpr
      (weightedDenseVector_ne_zero (H := H))))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CountableSpatialTensor
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.leftTensorVector_apply _root_.OAI.KadisonKastler.rightTensorSlice_apply _root_.OAI.KadisonKastler.spatialIsometry_tmul _root_.OAI.KadisonKastler.spatialMap_id _root_.OAI.KadisonKastler.spatialMap_tmul _root_.OAI.KadisonKastler.spatialMatrixUnits_entry _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Countable sums commute with the spatial Hilbert tensor product

The coordinate tensor map preserves inner products on algebraic tensors.
Its completion is onto because it contains every finitely supported tensor
vector. This is the concrete amplification bridge for the constructed
faithful cyclic representation.
-/

namespace KadisonKastler

open UnitalTomsWinter
open scoped TensorProduct Topology

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

def countableTensorVector (x : CountableHilbertSum H) (y : K) :
    CountableHilbertSum (SpatialHilbert H K) :=
  ⟨fun n => ((x n ⊗ₜ[ℂ] y : H ⊗[ℂ] K) : SpatialHilbert H K), by
    apply ((lp.memℓp x).norm.const_mul ‖y‖).mono
    intro n
    simp only [UniformSpace.Completion.norm_coe, TensorProduct.norm_tmul, mul_comm, le_refl]⟩

@[simp] theorem countableTensorVector_apply (x : CountableHilbertSum H) (y : K) (n : ℕ) :
    countableTensorVector x y n =
      ((x n ⊗ₜ[ℂ] y : H ⊗[ℂ] K) : SpatialHilbert H K) := rfl

def countableTensorBilinear :
    CountableHilbertSum H →ₗ[ℂ] K →ₗ[ℂ] CountableHilbertSum (SpatialHilbert H K) where
  toFun x :=
    { toFun := countableTensorVector x
      map_add' := by intros; ext n; simp [TensorProduct.tmul_add, UniformSpace.Completion.coe_add]
      map_smul' := by intros; ext n; simp [UniformSpace.Completion.coe_smul] }
  map_add' := by intros; ext y n; simp [TensorProduct.add_tmul, UniformSpace.Completion.coe_add]
  map_smul' := by
    intro c x
    ext y n
    change (((c • x n) ⊗ₜ[ℂ] y : H ⊗[ℂ] K) : SpatialHilbert H K) =
      c • ((x n ⊗ₜ[ℂ] y : H ⊗[ℂ] K) : SpatialHilbert H K)
    rw [← TensorProduct.smul_tmul', UniformSpace.Completion.coe_smul]

theorem inner_countableTensorVector (x x' : CountableHilbertSum H) (y y' : K) :
    inner ℂ (countableTensorVector x y) (countableTensorVector x' y') =
      inner ℂ x x' * inner ℂ y y' := by
  simp only [lp.inner_eq_tsum, countableTensorVector_apply,
    UniformSpace.Completion.inner_coe, TensorProduct.inner_tmul]
  exact tsum_mul_right

def countableTensorAlgebraic :
    CountableHilbertSum H ⊗[ℂ] K →ₗ[ℂ] CountableHilbertSum (SpatialHilbert H K) :=
  TensorProduct.lift countableTensorBilinear

@[simp] theorem countableTensorAlgebraic_tmul (x : CountableHilbertSum H) (y : K) :
    countableTensorAlgebraic (x ⊗ₜ[ℂ] y) = countableTensorVector x y := rfl

theorem inner_countableTensorAlgebraic (z w : CountableHilbertSum H ⊗[ℂ] K) :
    inner ℂ (countableTensorAlgebraic z) (countableTensorAlgebraic w) = inner ℂ z w := by
  induction z using OAI.tensorInductionOn with
  | add a b ha hb => simp only [map_add, inner_add_left, ha, hb]
  | tmul x y =>
    induction w using OAI.tensorInductionOn with
    | add a b ha hb => simp only [map_add, inner_add_right, ha, hb]
    | tmul x' y' =>
      simp only [countableTensorAlgebraic_tmul, inner_countableTensorVector,
        TensorProduct.inner_tmul]

def countableTensorIsometry :
    SpatialHilbert (CountableHilbertSum H) K →ₗᵢ[ℂ]
      CountableHilbertSum (SpatialHilbert H K) :=
  let f := countableTensorAlgebraic.isometryOfInner inner_countableTensorAlgebraic
  fromCompletionCompat f

@[simp] theorem countableTensorIsometry_tmul (x : CountableHilbertSum H) (y : K) :
    countableTensorIsometry
      ((x ⊗ₜ[ℂ] y : CountableHilbertSum H ⊗[ℂ] K) :
        SpatialHilbert (CountableHilbertSum H) K) = countableTensorVector x y := by
  exact fromCompletionCompat_apply_coe _ _

theorem countableTensorIsometry_surjective :
    Function.Surjective (countableTensorIsometry (H := H) (K := K)) := by
  classical
  let J := countableTensorIsometry (H := H) (K := K)
  let V := J.toLinearMap.range
  have hV : IsClosed (V : Set (CountableHilbertSum (SpatialHilbert H K))) :=
    J.isometry.isClosedEmbedding.isClosed_range
  have hs (n : ℕ) (z : SpatialHilbert H K) : lp.single 2 n z ∈ V := by
    induction z using UniformSpace.Completion.induction_on with
    | hp => exact hV.preimage (lp.isometry_single n).continuous
    | ih z =>
      induction z using OAI.tensorInductionOn with
      | add a b ha hb =>
        simpa only [UniformSpace.Completion.coe_add, lp.single_add] using V.add_mem ha hb
      | tmul x y =>
        refine ⟨((lp.single 2 n x ⊗ₜ[ℂ] y : CountableHilbertSum H ⊗[ℂ] K) :
          SpatialHilbert (CountableHilbertSum H) K), ?_⟩
        change countableTensorIsometry _ = _
        rw [countableTensorIsometry_tmul]
        ext m
        by_cases h : m = n
        · subst m; simp
        · simp [lp.single_apply, h]
  intro z
  have hz : z ∈ V := hV.mem_of_tendsto (lp.hasSum_single (by norm_num) z)
    (Filter.Eventually.of_forall fun s => V.sum_mem (fun n _ => hs n (z n)))
  exact hz

def countableTensorEquiv :
    SpatialHilbert (CountableHilbertSum H) K ≃ₗᵢ[ℂ]
      CountableHilbertSum (SpatialHilbert H K) :=
  LinearIsometryEquiv.ofSurjective countableTensorIsometry countableTensorIsometry_surjective

@[simp] theorem countableTensorEquiv_tmul (x : CountableHilbertSum H) (y : K) :
    countableTensorEquiv
      ((x ⊗ₜ[ℂ] y : CountableHilbertSum H ⊗[ℂ] K) :
        SpatialHilbert (CountableHilbertSum H) K) = countableTensorVector x y :=
  countableTensorIsometry_tmul x y

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CountableOperatorEntries
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.leftTensorVector_apply _root_.OAI.KadisonKastler.rightTensorSlice_apply _root_.OAI.KadisonKastler.spatialIsometry_tmul _root_.OAI.KadisonKastler.spatialMap_id _root_.OAI.KadisonKastler.spatialMap_tmul _root_.OAI.KadisonKastler.spatialMatrixUnits_entry _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Entries of operators on a countable Hilbert sum

Entrywise identities detect equality and diagonal commutation. Under the
countable tensor unitary, tensoring an operator on the sum tensors each
of its entries. No summability of the operator's matrix is assumed.
-/

namespace KadisonKastler

open UnitalTomsWinter Filter
open scoped TensorProduct Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def countableOperatorEntry (S : CountableHilbertSum H →L[ℂ] CountableHilbertSum H)
    (i j : ℕ) : H →L[ℂ] H :=
  (canonicalCoordinate H i).comp (S.comp (canonicalSingle H j))

@[simp] theorem countableOperatorEntry_apply
    (S : CountableHilbertSum H →L[ℂ] CountableHilbertSum H) (i j : ℕ) (x : H) :
    countableOperatorEntry S i j x = S (lp.single 2 j x) i := rfl

@[simp] theorem countableOperatorEntry_diagonal_mul
    (a : H →L[ℂ] H) (S : CountableHilbertSum H →L[ℂ] CountableHilbertSum H) (i j : ℕ) :
    countableOperatorEntry (l2Diagonal a * S) i j = a * countableOperatorEntry S i j := by
  ext x
  rfl

@[simp] theorem countableOperatorEntry_mul_diagonal
    (a : H →L[ℂ] H) (S : CountableHilbertSum H →L[ℂ] CountableHilbertSum H) (i j : ℕ) :
    countableOperatorEntry (S * l2Diagonal a) i j = countableOperatorEntry S i j * a := by
  ext x
  simp only [countableOperatorEntry_apply, mul_apply_eq_comp, l2Diagonal_single]

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

@[simp] theorem countableTensorVector_single (i : ℕ) (x : H) (y : K) :
    countableTensorVector (lp.single 2 i x) y =
      lp.single 2 i ((x ⊗ₜ[ℂ] y : H ⊗[ℂ] K) : SpatialHilbert H K) := by
  classical
  ext j
  by_cases h : j = i
  · subst j; simp
  · simp [lp.single_apply, h]

@[simp] theorem countableTensorEquiv_symm_single (i : ℕ) (x : H) (y : K) :
    (countableTensorEquiv (H := H) (K := K)).symm
      (lp.single 2 i ((x ⊗ₜ[ℂ] y : H ⊗[ℂ] K) : SpatialHilbert H K)) =
      ((lp.single 2 i x ⊗ₜ[ℂ] y : CountableHilbertSum H ⊗[ℂ] K) :
        SpatialHilbert (CountableHilbertSum H) K) := by
  apply countableTensorEquiv.injective
  simp

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteCornerGroups
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransport_entry _root_.OAI.KadisonKastler.canonicalMatrixCorner_entry _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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

theorem scalarBlockHom_one (n : ℕ) :
    F.scalarBlockHom n 1 = F.partialDiagonal (Finset.range n) := by
  rw [F.scalarBlockHom_apply]
  simp only [CStarMatrix.one_apply, ite_smul, one_smul, zero_smul]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true]
  exact Fin.sum_univ_eq_sum_range (fun i => F.entry i i) n

theorem finiteSignedRepresentation_apply (n : ℕ) (g : SignedPermutation (Fin n)) :
    (F.finiteSignedRepresentation n g : H →L[ℂ] H) =
      (∑ i : Fin n, ∑ j : Fin n, (signedPermutationHom g : Matrix (Fin n) (Fin n) ℂ) i j •
        F.entry i j) + (1 - F.partialDiagonal (Finset.range n)) := by
  change F.scalarBlockHom n _ + (1 - F.scalarBlockHom n 1) = _
  rw [F.scalarBlockHom_apply, F.scalarBlockHom_one]
  rfl

/-- Diagonal signed elements, with identity on the complementary summands. -/
theorem finiteSignedRepresentation_diagonal (n : ℕ) (d : Fin n → ℤˣ) :
    (F.finiteSignedRepresentation n (SemidirectProduct.inl d) : H →L[ℂ] H) =
      (∑ i : Fin n, ((d i : ℤ) : ℂ) • F.entry i i) +
        (1 - F.partialDiagonal (Finset.range n)) := by
  rw [F.finiteSignedRepresentation_apply]
  have h : (signedPermutationHom (SemidirectProduct.inl d) : Matrix (Fin n) (Fin n) ℂ) =
      signDiagonal d := by
    simp [signedPermutationHom, signDiagonalHom, signDiagonalUnitary]
  rw [h]
  simp [signDiagonal, Matrix.diagonal, ite_smul]

/-- Permutations of the finite block, with identity on its complement. -/
theorem finiteSignedRepresentation_permutation (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (F.finiteSignedRepresentation n (SemidirectProduct.inr σ) : H →L[ℂ] H) =
      (∑ i : Fin n, F.entry (σ i) i) + (1 - F.partialDiagonal (Finset.range n)) := by
  rw [F.finiteSignedRepresentation_apply]
  have h : (signedPermutationHom (SemidirectProduct.inr σ) : Matrix (Fin n) (Fin n) ℂ) =
      Matrix.permMatrixHom (R := ℂ) σ := by
    simp [signedPermutationHom, permutationHom, permutationUnitary]
  rw [h]
  simp only [permutationMatrix_apply, ite_smul, one_smul, zero_smul]
  congr 1
  rw [Finset.sum_comm]
  simp

/-- The finite signed groups stay in every algebra containing the original entries. -/
theorem finiteSignedGroup_mem (M : VonNeumannAlgebra H)
    (hF : ∀ i j, F.entry i j ∈ M) (n : ℕ) (u : F.finiteSignedGroup n) :
    (u : H →L[ℂ] H) ∈ M := by
  obtain ⟨g, hg⟩ := u.property
  have hm : (F.finiteSignedRepresentation n g : H →L[ℂ] H) ∈ M := by
    rw [F.finiteSignedRepresentation_apply]
    apply M.add_mem
    · apply M.sum_mem
      intro i _
      apply M.sum_mem
      intro j _
      exact M.toStarSubalgebra.smul_mem (hF i j) _
    · apply M.sub_mem M.one_mem
      exact M.sum_mem (fun i _ => hF i i)
  rwa [hg] at hm

end FullMatrixCorner

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteCornerRefinement
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Compatibility of finite signed corner groups -/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {n : ℕ}

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {E : Submodule ℂ H} [CompleteSpace E]

namespace FullMatrixCorner

variable (F : FullMatrixCorner E)

theorem finiteSignedDiagonal_succ (d : Fin n → ℤˣ) :
    F.finiteSignedRepresentation (n + 1) (SemidirectProduct.inl (Fin.lastCases 1 d)) =
      F.finiteSignedRepresentation n (SemidirectProduct.inl d) := by
  apply Subtype.ext
  rw [F.finiteSignedRepresentation_diagonal, F.finiteSignedRepresentation_diagonal,
    Fin.sum_univ_castSucc]
  simp only [Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, Fin.val_last,
    Units.val_one, Int.cast_one, one_smul]
  simp only [partialDiagonal, Finset.sum_range_succ]
  abel

theorem finiteSignedPermutation_succ (σ : Equiv.Perm (Fin n)) :
    F.finiteSignedRepresentation (n + 1) (SemidirectProduct.inr (cornerSuccessorPermutation σ)) =
      F.finiteSignedRepresentation n (SemidirectProduct.inr σ) := by
  apply Subtype.ext
  rw [F.finiteSignedRepresentation_permutation, F.finiteSignedRepresentation_permutation,
    Fin.sum_univ_castSucc]
  simp only [cornerSuccessorPermutation_castSucc, cornerSuccessorPermutation_last,
    Fin.val_castSucc, Fin.val_last]
  simp only [partialDiagonal, Finset.sum_range_succ]
  abel

/-- These concrete finite subgroups increase with the finite corner. -/
theorem finiteSignedGroup_monotone : Monotone F.finiteSignedGroup := by
  apply monotone_nat_of_le_succ
  intro n u hu
  obtain ⟨g, rfl⟩ := hu
  refine ⟨SemidirectProduct.inl (Fin.lastCases 1 g.left) *
    SemidirectProduct.inr (cornerSuccessorPermutation g.right), ?_⟩
  rw [map_mul, F.finiteSignedDiagonal_succ, F.finiteSignedPermutation_succ,
    ← map_mul, SemidirectProduct.inl_left_mul_inr_right]

end FullMatrixCorner

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PublishedTypeIInjectivity
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The published injectivity input for type I factors

Blackadar, *Operator Algebras* (Springer, 2006), Corollary IV.2.2.10,
states that every type I von Neumann algebra is injective. Proposition
IV.2.1.4(iii) expresses this by a contractive projection in every faithful
representation. We retain only the factor case in its given representation.

The projection-theoretic hypothesis below is the usual characterization:
a factor is type I precisely when it has a nonzero minimal projection.
See III.1.3.10 and III.1.5.2--3. The latter also give the familiar spatial
form `B(H₁) ⊗ 1`. No perturbation or stability assertion is assumed.

Primary author PDF: https://bruceblackadar.com/Mathematics/Cycr.pdf
(printed pp. 244, 247, 373, 377).
-/

namespace KadisonKastler

open Generator.Tracial

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- A type I factor, expressed only in terms of its scalar center and
the existence of a minimal projection. -/
structure IsTypeIFactor (M : VonNeumannAlgebra H) : Prop where
  factor : ScalarCenter M
  minimal : ∃ p : AlgebraProjection M, IsMinimalProjectionIn M p

/-- The factor specialization of Blackadar IV.2.2.10. -/
def PublishedTypeIInjectivity : Prop :=
  ∀ M : VonNeumannAlgebra H, IsTypeIFactor M → IsInjective M

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FullMatrixInjectivity
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.finiteSignedGroup_finite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The type I algebra generated by full countable matrix units

Taking the commutant of the diagonal corner operators realizes the scalar
matrix factor directly. Its matrix coefficients are scalar, so it lies in
any von Neumann algebra containing the original matrix units.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {E : Submodule ℂ H} [CompleteSpace E]

namespace FullMatrixCorner

variable (F : FullMatrixCorner E)

/-- The scalar matrix algebra, as the commutant of diagonal corner operators. -/
def scalarMatrixAlgebra : VonNeumannAlgebra H where
  toStarSubalgebra := StarSubalgebra.centralizer ℂ (Set.range F.inflateHom)
  centralizer_centralizer' := by
    let S := Set.range F.inflateHom
    change (S ∪ star S).centralizer.centralizer.centralizer = (S ∪ star S).centralizer
    exact Set.centralizer_centralizer_centralizer _

theorem mem_scalarMatrixAlgebra_iff (T : H →L[ℂ] H) :
    T ∈ F.scalarMatrixAlgebra ↔ ∀ S : E →L[ℂ] E, Commute (F.inflateHom S) T := by
  change T ∈ StarSubalgebra.centralizer ℂ _ ↔ _
  rw [StarSubalgebra.mem_centralizer_iff]
  constructor
  · intro h S
    exact (h _ ⟨S,rfl⟩).1
  · intro h _ hS
    obtain ⟨S,rfl⟩ := hS
    exact ⟨(h S).eq, by rw [← map_star]; exact (h (star S)).eq⟩

theorem entry_mem_scalarMatrixAlgebra (i j : ℕ) :
    F.entry i j ∈ F.scalarMatrixAlgebra := by
  rw [F.mem_scalarMatrixAlgebra_iff]
  intro S
  exact F.inflateHom_commute_entry S i j

/-- The initial diagonal projection in the scalar matrix algebra. -/
def scalarMatrixInitialProjection : AlgebraProjection F.scalarMatrixAlgebra :=
  ⟨⟨F.entry 0 0, F.entry_mem_scalarMatrixAlgebra 0 0⟩,
    ⟨by apply Subtype.ext; simpa only [MulMemClass.coe_mul, ite_true, if_true] using F.mul_entry 0 0 0 0,
      by apply Subtype.ext; exact F.star_entry 0 0⟩⟩

end FullMatrixCorner

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FullCornerEmbedding
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Constructed embeddings of countable scalar matrix algebras -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {E : Submodule ℂ H} [CompleteSpace E]

namespace FullMatrixCorner

variable (F : FullMatrixCorner E)

/-- The locally finite group carried by the countable matrix units. -/
def signedGroupUnion : Subgroup (unitary (H →L[ℂ] H)) :=
  increasingSubgroupUnion F.finiteSignedGroup F.finiteSignedGroup_monotone

theorem signedGroupUnion_mem (u : F.signedGroupUnion) :
    (u : H →L[ℂ] H) ∈ F.scalarMatrixAlgebra := by
  obtain ⟨n, hn⟩ := u.property
  exact F.finiteSignedGroup_mem F.scalarMatrixAlgebra F.entry_mem_scalarMatrixAlgebra
    n ⟨u.val, hn⟩

end FullMatrixCorner

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MinimalRowFamily
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! Minimal compact invariant families for normalized row averaging. -/

namespace KadisonKastler

noncomputable section

open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance minimalRowFamilyOrder_rb6d0c3_1 (M : VonNeumannAlgebra H) : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance minimalRowFamilyStarOrder_rb6d0c3_1 (M : VonNeumannAlgebra H) : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _
def RowInvariant {M : VonNeumannAlgebra H} {c : ℝ} (hc : 0 ≤ c)
    (K : Set (BoundedWeakAlgebraMap M c)) : Prop :=
  ∀ (n : ℕ) (r : Fin n → Algebra M) (hr : ∑ i, r i * star (r i) = 1),
    Set.MapsTo (boundedWeakRowAverage hc r hr) K K

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_NormUltraproduct
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.algebraCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

def NormNullSequence (ω : Ultrafilter ℕ) (x : VaryingBoundedSequence B) : Prop :=
  Tendsto (fun j => ‖x j‖) (ω : Filter ℕ) (𝓝 0)

omit [∀ j, Nontrivial (B j)] in
theorem normNullSequence_add (ω : Ultrafilter ℕ) {x y : VaryingBoundedSequence B}
    (hx : NormNullSequence B ω x) (hy : NormNullSequence B ω y) :
    NormNullSequence B ω (x + y) := by
  apply squeeze_zero (fun j => norm_nonneg ((x + y) j)) (fun j => norm_add_le (x j) (y j))
  simpa only [add_zero] using hx.add hy

omit [∀ j, Nontrivial (B j)] in
theorem normNullSequence_mul_left (ω : Ultrafilter ℕ) (x : VaryingBoundedSequence B)
    {y : VaryingBoundedSequence B} (hy : NormNullSequence B ω y) :
    NormNullSequence B ω (x * y) := by
  apply squeeze_zero (fun j => norm_nonneg ((x * y) j))
    (fun j => (norm_mul_le (x j) (y j)).trans
      (mul_le_mul_of_nonneg_right (varyingSequence_norm_apply_le x j) (norm_nonneg _)))
  simpa only [mul_zero] using tendsto_const_nhds.mul hy

omit [∀ j, Nontrivial (B j)] in
theorem normNullSequence_mul_right (ω : Ultrafilter ℕ) {x : VaryingBoundedSequence B}
    (hx : NormNullSequence B ω x) (y : VaryingBoundedSequence B) :
    NormNullSequence B ω (x * y) := by
  apply squeeze_zero (fun j => norm_nonneg ((x * y) j))
    (fun j => (norm_mul_le (x j) (y j)).trans
      (mul_le_mul_of_nonneg_left (varyingSequence_norm_apply_le y j) (norm_nonneg _)))
  simpa only [zero_mul] using hx.mul tendsto_const_nhds

theorem isClosed_normNullSequence (ω : Ultrafilter ℕ) :
    IsClosed {x : VaryingBoundedSequence B | NormNullSequence B ω x} := by
  apply isClosed_of_closure_subset
  intro x hx
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨y, hy, hyx⟩ := Metric.mem_closure_iff.mp hx (ε / 2) (half_pos hε)
  have hxy : ‖x - y‖ < ε / 2 := by
    simpa only [dist_eq_norm, norm_sub_rev] using hyx
  filter_upwards [(Metric.tendsto_nhds.mp hy) (ε / 2) (half_pos hε)] with j hj
  have hyj : ‖y j‖ < ε / 2 := by simpa only [dist_zero_right, norm_norm] using hj
  have hc : ‖x j - y j‖ ≤ ‖x - y‖ := varyingSequence_norm_apply_le (x - y) j
  have ht : ‖x j‖ ≤ ‖x j - y j‖ + ‖y j‖ := by
    simpa only [sub_add_cancel] using norm_add_le (x j - y j) (y j)
  simpa only [dist_zero_right, norm_norm] using
    (lt_of_le_of_lt ht (by linarith only [hc, hxy, hyj]))

def normNullClosedIdeal (ω : Ultrafilter ℕ) :
    CuntzPureness.ClosedStarIdeal (VaryingBoundedSequence B) where
  ideal := TwoSidedIdeal.mk' {x | NormNullSequence B ω x}
    (by
      change NormNullSequence B ω 0
      simpa only [NormNullSequence, lp.coeFn_zero, Pi.zero_apply, norm_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) (ω : Filter ℕ) (𝓝 0)))
    (normNullSequence_add B ω)
    (by
      intro x hx
      change NormNullSequence B ω (-x)
      change NormNullSequence B ω x at hx
      simpa only [NormNullSequence, lp.coeFn_neg, Pi.neg_apply, norm_neg] using hx)
    (by intro x y hy; exact normNullSequence_mul_left B ω x hy)
    (by intro x y hx; exact normNullSequence_mul_right B ω hx y)
  star_mem := by
    intro x hx
    change NormNullSequence B ω (star x - 0)
    change NormNullSequence B ω (x - 0) at hx
    simpa only [sub_zero, NormNullSequence, lp.coeFn_star, Pi.star_apply, norm_star] using hx
  isClosed := by
    simpa only [TwoSidedIdeal.coe_mk'] using isClosed_normNullSequence B ω

abbrev NormUltraproduct (ω : Ultrafilter ℕ) := (normNullClosedIdeal B ω).Quotient

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_NormUltraproductMaps
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.tracialQuotientLinear_map _root_.OAI.KadisonKastler.tracialSequenceContinuous_apply _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.tracialSequenceValue_one _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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

def normProductMap (φ : ∀ j, B j →⋆ₐ[ℂ] C j) :
    VaryingBoundedSequence B →⋆ₐ[ℂ] VaryingBoundedSequence C where
  toFun x := ⟨fun j => φ j (x j),
    (lp.memℓp x).mono' (fun j => NonUnitalStarAlgHom.norm_apply_le (φ j) (x j))⟩
  map_zero' := lp.ext (by funext j; exact map_zero (φ j))
  map_one' := lp.ext (by funext j; exact map_one (φ j))
  map_add' x y := lp.ext (by funext j; exact map_add (φ j) (x j) (y j))
  map_mul' x y := lp.ext (by funext j; exact map_mul (φ j) (x j) (y j))
  commutes' z := lp.ext (by funext j; exact (φ j).commutes z)
  map_star' x := lp.ext (by funext j; exact map_star (φ j) (x j))

@[simp] theorem normProductMap_apply (φ : ∀ j, B j →⋆ₐ[ℂ] C j)
    (x : VaryingBoundedSequence B) (j : ℕ) : normProductMap φ x j = φ j (x j) := rfl

theorem NormNullSequence.map {ω : Ultrafilter ℕ} {x : VaryingBoundedSequence B}
    (hx : NormNullSequence B ω x) (φ : ∀ j, B j →⋆ₐ[ℂ] C j) :
    NormNullSequence C ω (normProductMap φ x) :=
  squeeze_zero (fun _ => norm_nonneg _) (fun j => NonUnitalStarAlgHom.norm_apply_le (φ j) _) hx

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ScalarBoundaryMean
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.ScalarOperatorKernel.toContinuous_apply _root_.OAI.KadisonKastler.UniformMeasurableOperators.coefficientFamily_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The scalar boundary mean on actual L-infinity classes

The source is the bounded family of L-infinity sections indexed by the
countable discrete group. Multiplication and nonsingular pullback are
defined on the actual almost-everywhere classes. The scalar
conditional-expectation property includes the module and action identities.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped BoundedContinuousFunction

noncomputable section

variable {D : Type*} [MeasurableSpace D] {μ : Measure D}

theorem scalarInfinityMul_add_left (f g h : ScalarLInfinity μ) :
    scalarInfinityMul (f + g) h = scalarInfinityMul f h + scalarInfinityMul g h := by
  apply Lp.ext
  filter_upwards [scalarInfinityMul_ae (f + g) h, scalarInfinityMul_ae f h,
    scalarInfinityMul_ae g h, Lp.coeFn_add f g,
    Lp.coeFn_add (scalarInfinityMul f h) (scalarInfinityMul g h)] with x ha hb hc hd he
  simp only [Pi.add_apply] at hd he
  rw [ha, hd, he, hb, hc, add_mul]

theorem scalarInfinityMul_smul_left (c : ℂ) (f g : ScalarLInfinity μ) :
    scalarInfinityMul (c • f) g = c • scalarInfinityMul f g := by
  apply Lp.ext
  filter_upwards [scalarInfinityMul_ae (c • f) g, scalarInfinityMul_ae f g,
    Lp.coeFn_smul c f, Lp.coeFn_smul c (scalarInfinityMul f g)] with x ha hb hc hd
  simp only [Pi.smul_apply] at hc hd
  rw [ha, hc, hd, hb, smul_mul_assoc]

theorem scalarInfinityMul_comm (f g : ScalarLInfinity μ) :
    scalarInfinityMul f g = scalarInfinityMul g f := by
  apply Lp.ext
  filter_upwards [scalarInfinityMul_ae f g, scalarInfinityMul_ae g f] with x hf hg
  rw [hf, hg, mul_comm]

section Pullback

variable [IsFiniteMeasure μ] {E : Type*} [MeasurableSpace E]
  {ν : Measure E} [IsFiniteMeasure ν]

def scalarInfinityPullbackL (T : D → E) (hT : Measure.QuasiMeasurePreserving T μ ν) :
    ScalarLInfinity ν →L[ℂ] ScalarLInfinity μ :=
  LinearMap.mkContinuous
    { toFun := scalarInfinityPullback T hT
      map_add' f g := by
        apply Lp.ext
        filter_upwards [scalarInfinityPullback_ae T hT (f + g),
          scalarInfinityPullback_ae T hT f, scalarInfinityPullback_ae T hT g,
          hT.ae (Lp.coeFn_add f g),
          Lp.coeFn_add (scalarInfinityPullback T hT f) (scalarInfinityPullback T hT g)]
          with x ha hb hc hd he
        simp only [Pi.add_apply] at hd he
        rw [ha, he, hb, hc, hd]
      map_smul' c f := by
        simp only [RingHom.id_apply]
        apply Lp.ext
        filter_upwards [scalarInfinityPullback_ae T hT (c • f),
          scalarInfinityPullback_ae T hT f, hT.ae (Lp.coeFn_smul c f),
          Lp.coeFn_smul c (scalarInfinityPullback T hT f)] with x ha hb hc hd
        simp only [Pi.smul_apply] at hc hd
        rw [ha, hd, hb, hc] }
    1 (fun f => by simpa using norm_scalarInfinityPullback_le T hT f)

end Pullback

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_WeakOperatorCoefficients
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Scalar coefficients determine weak operator fields -/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

variable {D H : Type*} [MeasurableSpace D] {μ : Measure D} [IsFiniteMeasure μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace WeakOperatorRepresentative

omit [IsFiniteMeasure μ] in
/-- Almost-everywhere equal representatives have identical scalar coefficients. -/
theorem coefficient_eq_of_ae (F G : WeakOperatorRepresentative (H := H) μ)
    (h : eval F =ᵐ[μ] eval G) (ξ η : H) : coefficient F ξ η = coefficient G ξ η := by
  apply Lp.ext
  filter_upwards [coefficient_ae F ξ η, coefficient_ae G ξ η, h] with x hF hG hFG
  rw [hF, hG, hFG]

omit [IsFiniteMeasure μ] in
/-- Conversely, a countable dense set of coefficients detects AE equality. -/
theorem ae_eq_of_coefficient_eq [TopologicalSpace.SeparableSpace H]
    (F G : WeakOperatorRepresentative (H := H) μ)
    (h : ∀ ξ η : H, coefficient F ξ η = coefficient G ξ η) : eval F =ᵐ[μ] eval G := by
  obtain ⟨v, hv⟩ := TopologicalSpace.exists_dense_seq (α := H)
  have hp (i j : ℕ) : ∀ᵐ x ∂μ,
      inner ℂ (v i) (eval F x (v j)) = inner ℂ (v i) (eval G x (v j)) := by
    have hi := h (v j) (v i)
    filter_upwards [coefficient_ae F (v j) (v i), coefficient_ae G (v j) (v i)] with x hF hG
    rw [hi] at hF
    exact hF.symm.trans hG
  have hall : ∀ᵐ x ∂μ, ∀ i j : ℕ,
      inner ℂ (v i) (eval F x (v j)) = inner ℂ (v i) (eval G x (v j)) :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => hp i j
  filter_upwards [hall] with x hx
  apply ContinuousLinearMap.ext
  have he : (fun ξ => eval F x ξ) = (fun ξ => eval G x ξ) := by
    apply hv.equalizer (eval F x).continuous (eval G x).continuous
    funext j
    exact hv.eq_of_inner_right ℂ (fun i => hx i j)
  exact congrFun he

omit [IsFiniteMeasure μ] in
/-- Scalar coefficients exactly detect equality in the actual C-star quotient. -/
theorem quotient_eq_iff_coefficient_eq [TopologicalSpace.SeparableSpace H]
    (F G : WeakOperatorRepresentative (H := H) μ) :
    operatorFieldQuotient μ F = operatorFieldQuotient μ G ↔
      ∀ ξ η : H, coefficient F ξ η = coefficient G ξ η := by
  rw [operatorFieldQuotient_eq_iff]
  exact ⟨fun h ξ η => coefficient_eq_of_ae F G h ξ η,
    ae_eq_of_coefficient_eq F G⟩

end WeakOperatorRepresentative

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_WeakFieldCoefficients
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Intrinsic scalar coefficients of weak operator fields -/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

variable {D H : Type*} [MeasurableSpace D] {μ : Measure D}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace WeakOperatorField

/-- Matrix coefficients depend only on the almost-everywhere operator class. -/
def coefficient (T : WeakOperatorField (H := H) μ) (ξ η : H) : ScalarLInfinity μ :=
  WeakOperatorRepresentative.coefficient (representative T) ξ η

theorem coefficient_quotient (F : WeakOperatorRepresentative (H := H) μ) (ξ η : H) :
    coefficient (operatorFieldQuotient μ F) ξ η = WeakOperatorRepresentative.coefficient F ξ η := by
  apply WeakOperatorRepresentative.coefficient_eq_of_ae
  exact (operatorFieldQuotient_eq_iff μ _ _).mp (quotient_representative _)

variable [IsFiniteMeasure μ]

variable [TopologicalSpace.SeparableSpace H]

omit [IsFiniteMeasure μ] in
/-- Intrinsic scalar coefficients separate the quotient. -/
theorem ext_coeff {T S : WeakOperatorField (H := H) μ}
    (h : ∀ ξ η, coefficient T ξ η = coefficient S ξ η) : T = S := by
  rw [← quotient_representative T, ← quotient_representative S]
  apply (WeakOperatorRepresentative.quotient_eq_iff_coefficient_eq _ _).mpr
  exact h

omit [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace H] in
theorem coefficient_add (T S : WeakOperatorField (H := H) μ) (ξ η : H) :
    coefficient (T + S) ξ η = coefficient T ξ η + coefficient S ξ η := by
  rw [← quotient_representative T, ← quotient_representative S, ← map_add,
    coefficient_quotient, coefficient_quotient, coefficient_quotient]
  apply Lp.ext
  filter_upwards [WeakOperatorRepresentative.coefficient_ae (representative T + representative S) ξ η,
    WeakOperatorRepresentative.coefficient_ae (representative T) ξ η,
    WeakOperatorRepresentative.coefficient_ae (representative S) ξ η,
    Lp.coeFn_add (WeakOperatorRepresentative.coefficient (representative T) ξ η)
      (WeakOperatorRepresentative.coefficient (representative S) ξ η)] with x ha hb hc hd
  simp only [Pi.add_apply] at hd
  rw [ha, hd, hb, hc, WeakOperatorRepresentative.eval_add,
    add_apply, inner_add_right]

omit [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace H] in
theorem coefficient_smul (c : ℂ) (T : WeakOperatorField (H := H) μ) (ξ η : H) :
    coefficient (c • T) ξ η = c • coefficient T ξ η := by
  rw [← quotient_representative T, ← map_smul, coefficient_quotient, coefficient_quotient]
  apply Lp.ext
  filter_upwards [WeakOperatorRepresentative.coefficient_ae (c • representative T) ξ η,
    WeakOperatorRepresentative.coefficient_ae (representative T) ξ η,
    Lp.coeFn_smul c (WeakOperatorRepresentative.coefficient (representative T) ξ η)] with x ha hb hc
  simp only [Pi.smul_apply] at hc
  rw [ha, hc, hb, WeakOperatorRepresentative.eval_smul,
    smul_apply, inner_smul_right]
  rfl

end WeakOperatorField

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_OperatorCoefficientMean
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Contractive operator-field averaging from the scalar boundary mean

All objects here are the actual measurable fields modulo almost-everywhere
equality. The construction uses norm-minimizing representatives only to
produce an operator; its scalar coefficients characterize it intrinsically.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped BoundedContinuousFunction

noncomputable section

variable {G D H : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace D] {μ : Measure D} [IsFiniteMeasure μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

namespace WeakOperatorField

/-- Choose norm-controlled representatives of a bounded operator-field family. -/
def uniformFamily (F : G →ᵇ WeakOperatorField (H := H) μ) :
    UniformMeasurableOperators G D H μ where
  eval g := WeakOperatorRepresentative.eval (representative (F g))
  bound := ‖F‖
  bound_nonneg := norm_nonneg F
  norm_le g x := (WeakOperatorRepresentative.eval_norm_le (representative (F g)) x).trans
    ((norm_representative_le (F g)).trans (F.norm_coe_le_norm g))
  measurable g := WeakOperatorRepresentative.eval_aestronglyMeasurable (representative (F g))

/-- The intrinsic scalar coefficient family. -/
def coefficientFamily (F : G →ᵇ WeakOperatorField (H := H) μ) (ξ η : H) :
    G →ᵇ ScalarLInfinity μ := (uniformFamily F).coefficientFamily ξ η

omit [Group G] [TopologicalSpace.SeparableSpace H] in
theorem coefficientFamily_apply (F : G →ᵇ WeakOperatorField (H := H) μ) (ξ η : H) (g : G) :
    coefficientFamily F ξ η g = coefficient (F g) ξ η := by
  apply Lp.ext
  filter_upwards [(uniformFamily F).coefficient_ae g ξ η,
    WeakOperatorRepresentative.coefficient_ae (representative (F g)) ξ η] with x hF hR
  exact hF.trans hR.symm

omit [Group G] [TopologicalSpace.SeparableSpace H] in
theorem coefficientFamily_add (F E : G →ᵇ WeakOperatorField (H := H) μ) (ξ η : H) :
    coefficientFamily (F + E) ξ η = coefficientFamily F ξ η + coefficientFamily E ξ η := by
  apply BoundedContinuousFunction.ext
  intro g
  simp only [coefficientFamily_apply, BoundedContinuousFunction.add_apply, coefficient_add]

omit [Group G] [TopologicalSpace.SeparableSpace H] in
theorem coefficientFamily_smul (c : ℂ) (F : G →ᵇ WeakOperatorField (H := H) μ) (ξ η : H) :
    coefficientFamily (c • F) ξ η = c • coefficientFamily F ξ η := by
  apply BoundedContinuousFunction.ext
  intro g
  simp only [coefficientFamily_apply, BoundedContinuousFunction.smul_apply, coefficient_smul]

omit [Group G] [TopologicalSpace.SeparableSpace H] in
theorem coefficientFamily_const (T : WeakOperatorField (H := H) μ) (ξ η : H) :
    coefficientFamily (BoundedContinuousFunction.const G T) ξ η =
      BoundedContinuousFunction.const G (coefficient T ξ η) := by
  apply BoundedContinuousFunction.ext
  intro g
  exact coefficientFamily_apply _ ξ η g

end WeakOperatorField

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PeriodicMatrixUnits
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.finiteSignedGroup_finite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.matrixSignedGroup_finite _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Finite full matrix algebras from countable matrix units

The finite algebras need not be increasing. Their matrix units agree with
the countable matrix units on any fixed finite collection of columns once
the matrix size is large enough.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace FullMatrixCorner

variable {E : Submodule ℂ H} [CompleteSpace E] (F : FullMatrixCorner E)

def periodicMatrixUnits (n : ℕ) [NeZero n] :
    Generator.MatrixUnitSystem (Fin n) (H →L[ℂ] H) :=
  (F.finiteCuntz n).matrixUnits

end FullMatrixCorner

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ScalarWeakLimit
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.ScalarOperatorKernel.toContinuous_apply _root_.OAI.KadisonKastler.UniformMeasurableOperators.coefficientFamily_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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

theorem norm_scalarInfinityToL2_le (f : ScalarLInfinity μ) :
    ‖scalarInfinityToL2 f‖ ≤ ‖f‖ := by
  have ha : ∀ᵐ x ∂μ, ‖scalarInfinityToL2 f x‖ ≤ ‖f‖ := by
    filter_upwards [scalarInfinityToL2_ae f, scalarInfinity_ae_norm_le f] with x hx hf
    rwa [hx]
  simpa [measureUnivNNReal] using Lp.norm_le_of_ae_bound (norm_nonneg f) ha

def scalarInfinityToL2L : ScalarLInfinity μ →L[ℂ] Lp ℂ 2 μ :=
  LinearMap.mkContinuous
    { toFun := scalarInfinityToL2
      map_add' := scalarInfinityToL2_add
      map_smul' := scalarInfinityToL2_smul }
    1 (fun f => by simpa using norm_scalarInfinityToL2_le f)

@[simp]
theorem scalarInfinityToL2L_apply (f : ScalarLInfinity μ) :
    scalarInfinityToL2L f = scalarInfinityToL2 f := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ScalarPullbackAlgebra
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Algebraic identities for nonsingular scalar pullback -/

namespace KadisonKastler

noncomputable section

open MeasureTheory

variable {D : Type*} [MeasurableSpace D] {μ : Measure D}

theorem scalarInfinityPullback_mul (T : D → D)
    (hT : Measure.QuasiMeasurePreserving T μ μ) (f g : ScalarLInfinity μ) :
    scalarInfinityPullback T hT (scalarInfinityMul f g) =
      scalarInfinityMul (scalarInfinityPullback T hT f) (scalarInfinityPullback T hT g) := by
  apply Lp.ext
  filter_upwards [scalarInfinityPullback_ae T hT (scalarInfinityMul f g),
    hT.ae (scalarInfinityMul_ae f g),
    scalarInfinityMul_ae (scalarInfinityPullback T hT f) (scalarInfinityPullback T hT g),
    scalarInfinityPullback_ae T hT f, scalarInfinityPullback_ae T hT g]
    with x hfg hmul hout hf hg
  rw [hfg, hmul, hout, hf, hg]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ScalarL2Multiplication
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.ScalarOperatorKernel.toContinuous_apply _root_.OAI.KadisonKastler.UniformMeasurableOperators.coefficientFamily_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Bounded scalar multiplication on L2

This supplies weak continuity of multiplication by a fixed boundary
function when passing the averaging module identity to the limit.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

def scalarL2Mul (b : ScalarLInfinity μ) (f : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  (MeasureTheory.MemLp.mul (hφ := (Lp.memLp b)) (hf := (Lp.memLp f))).toLp (fun x => b x * f x)

theorem scalarL2Mul_ae (b : ScalarLInfinity μ) (f : Lp ℂ 2 μ) :
    scalarL2Mul b f =ᵐ[μ] fun x => b x * f x := MemLp.coeFn_toLp _

theorem norm_scalarL2Mul_le (b : ScalarLInfinity μ) (f : Lp ℂ 2 μ) :
    ‖scalarL2Mul b f‖ ≤ ‖b‖ * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [scalarL2Mul_ae b f, scalarInfinity_ae_norm_le b] with x hx hb
  rw [hx, norm_mul]
  exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)

theorem scalarL2Mul_add (b : ScalarLInfinity μ) (f g : Lp ℂ 2 μ) :
    scalarL2Mul b (f + g) = scalarL2Mul b f + scalarL2Mul b g := by
  apply Lp.ext
  filter_upwards [scalarL2Mul_ae b (f + g), scalarL2Mul_ae b f, scalarL2Mul_ae b g,
    Lp.coeFn_add f g, Lp.coeFn_add (scalarL2Mul b f) (scalarL2Mul b g)]
    with x ha hb hc hd he
  simp only [Pi.add_apply] at hd he
  rw [ha, hd, he, hb, hc, mul_add]

theorem scalarL2Mul_smul (b : ScalarLInfinity μ) (c : ℂ) (f : Lp ℂ 2 μ) :
    scalarL2Mul b (c • f) = c • scalarL2Mul b f := by
  apply Lp.ext
  filter_upwards [scalarL2Mul_ae b (c • f), scalarL2Mul_ae b f,
    Lp.coeFn_smul c f, Lp.coeFn_smul c (scalarL2Mul b f)] with x ha hb hc hd
  simp only [Pi.smul_apply, smul_eq_mul] at hc hd
  rw [ha, hc, hd, hb, mul_left_comm]

def scalarL2MulL (b : ScalarLInfinity μ) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  LinearMap.mkContinuous
    { toFun := scalarL2Mul b
      map_add' := scalarL2Mul_add b
      map_smul' := scalarL2Mul_smul b }
    ‖b‖ (norm_scalarL2Mul_le b)

@[simp]
theorem scalarL2MulL_apply (b : ScalarLInfinity μ) (f : Lp ℂ 2 μ) :
    scalarL2MulL b f = scalarL2Mul b f := rfl

variable [IsProbabilityMeasure μ]

theorem scalarInfinityToL2_mul (b f : ScalarLInfinity μ) :
    scalarInfinityToL2 (scalarInfinityMul b f) = scalarL2MulL b (scalarInfinityToL2 f) := by
  apply Lp.ext
  filter_upwards [scalarInfinityToL2_ae (scalarInfinityMul b f), scalarInfinityMul_ae b f,
    scalarL2Mul_ae b (scalarInfinityToL2 f), scalarInfinityToL2_ae f] with x ha hb hc hd
  exact ha.trans (hb.trans (by rw [scalarL2MulL_apply, hc, hd]))

theorem scalarInfinityMul_of_weak_limits
    {ι : Type*} {l : Filter ι} [l.NeBot] (b : ScalarLInfinity μ)
    (f g : ι → ScalarLInfinity μ) (a c : ScalarLInfinity μ)
    (hfg : ∀ i, scalarInfinityMul b (f i) = g i)
    (hf : ∀ y, Tendsto (fun i => inner ℂ y (scalarInfinityToL2 (f i))) l
      (𝓝 (inner ℂ y (scalarInfinityToL2 a))))
    (hg : ∀ y, Tendsto (fun i => inner ℂ y (scalarInfinityToL2 (g i))) l
      (𝓝 (inner ℂ y (scalarInfinityToL2 c)))) : scalarInfinityMul b a = c := by
  apply scalarInfinityToL2_injective
  apply ext_inner_left ℂ
  intro y
  apply (tendsto_nhds_unique (hg y) ?_).symm
  let F : Lp ℂ 2 μ →L[ℂ] ℂ := (innerSL ℂ y).comp (scalarL2MulL b)
  have h := dual_tendsto_of_inner_tendsto (fun i => scalarInfinityToL2 (f i))
    (scalarInfinityToL2 a) hf F
  change Tendsto (fun i => inner ℂ y (scalarL2MulL b (scalarInfinityToL2 (f i)))) l
    (𝓝 (inner ℂ y (scalarL2MulL b (scalarInfinityToL2 a)))) at h
  simpa only [← scalarInfinityToL2_mul, hfg] using h

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ScalarPullbackWeakGraph
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Weak closure of the nonsingular pullback graph

Pullback need not be a bounded operator on L2. Its graph is nonetheless
closed: norm-convergent pairs have subsequences converging pointwise, and
nonsingularity transports the first almost-everywhere limit. Linearity then
makes this graph weakly closed. This suffices for the boundary averages.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
  (T : X → X) (hT : Measure.QuasiMeasurePreserving T μ μ)

variable [IsProbabilityMeasure μ]

theorem scalarInfinityPullback_of_weak_limits
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (f g : ι → ScalarLInfinity μ) (a b : ScalarLInfinity μ)
    (hfg : ∀ i, scalarInfinityPullback T hT (f i) = g i)
    (hf : ∀ y, Tendsto (fun i => inner ℂ y (scalarInfinityToL2 (f i))) l
      (𝓝 (inner ℂ y (scalarInfinityToL2 a))))
    (hg : ∀ y, Tendsto (fun i => inner ℂ y (scalarInfinityToL2 (g i))) l
      (𝓝 (inner ℂ y (scalarInfinityToL2 b)))) :
    scalarInfinityPullback T hT a = b := by
  have hgraph (i : ι) : ∀ᵐ x ∂μ,
      scalarInfinityToL2 (g i) x = scalarInfinityToL2 (f i) (T x) := by
    have he := scalarInfinityPullback_ae T hT (f i)
    rw [hfg i] at he
    filter_upwards [scalarInfinityToL2_ae (g i), hT.ae (scalarInfinityToL2_ae (f i)), he]
      with x hgx hfx hex
    exact hgx.trans (hex.trans hfx.symm)
  have he := scalarL2PullbackGraph_of_inner_tendsto T hT
    (fun i => scalarInfinityToL2 (f i)) (fun i => scalarInfinityToL2 (g i))
    (scalarInfinityToL2 a) (scalarInfinityToL2 b) hgraph hf hg
  apply Lp.ext
  filter_upwards [scalarInfinityPullback_ae T hT a, scalarInfinityToL2_ae b,
    hT.ae (scalarInfinityToL2_ae a), he] with x hax hbx htax hex
  exact hax.trans (htax.symm.trans (hex.symm.trans hbx))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ScalarShiftCesaro
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Contractive Cesaro averages for the nonsingular boundary shift -/

namespace KadisonKastler

noncomputable section

open MeasureTheory
open scoped BigOperators

variable {D : Type*} [MeasurableSpace D] {μ : Measure D} [IsFiniteMeasure μ]
  (S : D → D) (hS : Measure.QuasiMeasurePreserving S μ μ)

def scalarShiftCesaro (n : ℕ) : ScalarLInfinity μ →L[ℂ] ScalarLInfinity μ :=
  (((n + 1 : ℕ) : ℝ)⁻¹ : ℂ) •
    ∑ i ∈ Finset.range (n + 1), (scalarInfinityPullbackL S hS) ^ i

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ScalarCesaroCommutation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.ScalarOperatorKernel.toContinuous_apply _root_.OAI.KadisonKastler.UniformMeasurableOperators.coefficientFamily_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Naturality and locality of scalar shift averages -/

namespace KadisonKastler

noncomputable section

open MeasureTheory
open scoped BigOperators

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
  (S : X → X) (hS : Measure.QuasiMeasurePreserving S μ μ)

theorem scalarShiftCesaro_commutes (A : ScalarLInfinity μ →L[ℂ] ScalarLInfinity μ)
    (hA : ∀ f, A (scalarInfinityPullback S hS f) = scalarInfinityPullback S hS (A f))
    (n : ℕ) (f : ScalarLInfinity μ) :
    A (scalarShiftCesaro S hS n f) = scalarShiftCesaro S hS n (A f) := by
  have hp (i : ℕ) : A (((scalarInfinityPullbackL S hS) ^ i) f) =
      ((scalarInfinityPullbackL S hS) ^ i) (A f) := by
    induction i with
    | zero => simp
    | succ i hi =>
      rw [pow_succ', mul_apply_eq_comp, mul_apply_eq_comp]
      exact (hA _).trans (congrArg (scalarInfinityPullback S hS) hi)
  simp only [scalarShiftCesaro, smul_apply, sum_apply, map_smul, map_sum, hp]

omit [IsProbabilityMeasure μ] in
theorem scalarInfinityPullback_commutes (T : X → X)
    (hT : Measure.QuasiMeasurePreserving T μ μ)
    (hcomm : ∀ x, S (T x) = T (S x)) (f : ScalarLInfinity μ) :
    scalarInfinityPullback T hT (scalarInfinityPullback S hS f) =
      scalarInfinityPullback S hS (scalarInfinityPullback T hT f) := by
  apply Lp.ext
  filter_upwards [scalarInfinityPullback_ae T hT (scalarInfinityPullback S hS f),
    hT.ae (scalarInfinityPullback_ae S hS f),
    scalarInfinityPullback_ae S hS (scalarInfinityPullback T hT f),
    hS.ae (scalarInfinityPullback_ae T hT f)] with x ha hb hc hd
  rw [ha, hb, hc, hd, hcomm]

def scalarInfinityMulL (b : ScalarLInfinity μ) : ScalarLInfinity μ →L[ℂ] ScalarLInfinity μ :=
  LinearMap.mkContinuous
    { toFun := scalarInfinityMul b
      map_add' f g := by
        rw [scalarInfinityMul_comm b, scalarInfinityMul_add_left,
          scalarInfinityMul_comm f, scalarInfinityMul_comm g]
      map_smul' c f := by
        simp only [RingHom.id_apply]
        rw [scalarInfinityMul_comm b, scalarInfinityMul_smul_left, scalarInfinityMul_comm f] }
    ‖b‖ (norm_scalarInfinityMul_le b)

omit [IsProbabilityMeasure μ] in
@[simp]
theorem scalarInfinityMulL_apply (b f : ScalarLInfinity μ) :
    scalarInfinityMulL b f = scalarInfinityMul b f := rfl

theorem scalarShiftCesaro_module (b : ScalarLInfinity μ)
    (hb : scalarInfinityPullback S hS b = b) (n : ℕ) (f : ScalarLInfinity μ) :
    scalarShiftCesaro S hS n (scalarInfinityMul b f) =
      scalarInfinityMul b (scalarShiftCesaro S hS n f) := by
  apply Eq.symm
  apply scalarShiftCesaro_commutes S hS (scalarInfinityMulL b)
  intro g
  simp only [scalarInfinityMulL_apply, scalarInfinityPullback_mul, hb]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ScalarPositiveLimit
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

def ScalarNonnegative (f : ScalarLInfinity μ) : Prop :=
  ∀ᵐ x ∂μ, f x ∈ scalarPositiveCone

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ScalarInvariantProjection
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

structure ScalarInvariantProjection where
  toCLM : ScalarLInfinity μ →L[ℂ] ScalarLInfinity μ
  norm_le : ∀ f, ‖toCLM f‖ ≤ ‖f‖
  positive : ∀ f, ScalarNonnegative f → ScalarNonnegative (toCLM f)
  invariant : ∀ f, scalarInfinityPullback S hS (toCLM f) = toCLM f
  fixed : ∀ f, scalarInfinityPullback S hS f = f → toCLM f = f
  weak_limit : ∀ f y, Tendsto
    (fun n => inner ℂ y (scalarInfinityToL2 (scalarShiftCesaro S hS n f)))
    (Ultrafilter.of (atTop : Filter ℕ) : Filter ℕ)
    (𝓝 (inner ℂ y (scalarInfinityToL2 (toCLM f))))

namespace ScalarInvariantProjection

variable {S hS} (P : ScalarInvariantProjection S hS)

theorem natural (T : X → X) (hT : Measure.QuasiMeasurePreserving T μ μ)
    (hcomm : ∀ x, S (T x) = T (S x)) (f : ScalarLInfinity μ) :
    P.toCLM (scalarInfinityPullback T hT f) = scalarInfinityPullback T hT (P.toCLM f) := by
  apply Eq.symm
  apply scalarInfinityPullback_of_weak_limits
    (l := (Ultrafilter.of (atTop : Filter ℕ) : Filter ℕ)) T hT
    (fun n => scalarShiftCesaro S hS n f)
    (fun n => scalarShiftCesaro S hS n (scalarInfinityPullback T hT f))
    (P.toCLM f) (P.toCLM (scalarInfinityPullback T hT f))
  · intro n
    exact scalarShiftCesaro_commutes S hS (scalarInfinityPullbackL T hT)
      (scalarInfinityPullback_commutes S hS T hT hcomm) n f
  · exact P.weak_limit f
  · exact P.weak_limit _

theorem module_map (b f : ScalarLInfinity μ) (hb : scalarInfinityPullback S hS b = b) :
    P.toCLM (scalarInfinityMul b f) = scalarInfinityMul b (P.toCLM f) := by
  apply Eq.symm
  apply scalarInfinityMul_of_weak_limits
    (l := (Ultrafilter.of (atTop : Filter ℕ) : Filter ℕ)) b
    (fun n => scalarShiftCesaro S hS n f)
    (fun n => scalarShiftCesaro S hS n (scalarInfinityMul b f))
    (P.toCLM f) (P.toCLM (scalarInfinityMul b f))
  · intro n
    exact (scalarShiftCesaro_module S hS b hb n f).symm
  · exact P.weak_limit f
  · exact P.weak_limit _

end ScalarInvariantProjection

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProductBoundaryLifts
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instIsProbabilityMeasureBilateralWalkPathBilateralWalkLaw _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

def firstBoundaryLiftL :
    ScalarLInfinity ((shiftBoundaryMeasure μ S).prod ν) →L[ℂ] ScalarLInfinity (μ.prod ν) :=
  (Lp.compMeasurePreservingₗᵢ ℂ (firstBoundaryMap μ S)
    (firstBoundaryMap_measurePreserving μ S)).toContinuousLinearMap

theorem firstBoundaryLiftL_ae (g : ScalarLInfinity ((shiftBoundaryMeasure μ S).prod ν)) :
    firstBoundaryLiftL μ S g =ᵐ[μ.prod ν] fun z => g (firstBoundaryMap μ S z) :=
  Lp.coeFn_compMeasurePreserving g (firstBoundaryMap_measurePreserving μ S)

theorem firstBoundaryLiftL_norm (g : ScalarLInfinity ((shiftBoundaryMeasure μ S).prod ν)) :
    ‖firstBoundaryLiftL μ S g‖ = ‖g‖ :=
  Lp.norm_compMeasurePreserving g (firstBoundaryMap_measurePreserving μ S)

theorem firstBoundaryLiftL_injective : Function.Injective (firstBoundaryLiftL (ν := ν) μ S) :=
  by
    intro f g h
    exact (Lp.compMeasurePreservingₗᵢ ℂ (firstBoundaryMap μ S)
      (firstBoundaryMap_measurePreserving μ S)).injective h

variable {μ S}

structure FirstBoundaryProjection
    (hS : Measure.QuasiMeasurePreserving S μ μ)
    (P : ScalarInvariantProjection (firstCoordinateShift (Y := Y) S)
      (firstCoordinateShift_quasi (ν := ν) hS)) where
  toCLM : ScalarLInfinity (μ.prod ν) →L[ℂ] ScalarLInfinity ((shiftBoundaryMeasure μ S).prod ν)
  lift_eq : ∀ f, firstBoundaryLiftL μ S (toCLM f) = P.toCLM f

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProductBoundaryAlgebra
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instIsProbabilityMeasureBilateralWalkPathBilateralWalkLaw _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Algebraic identities for first-coordinate boundary descent -/

namespace KadisonKastler

noncomputable section

open MeasureTheory

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {S : X → X}

theorem firstBoundaryLiftL_mul (f g : ScalarLInfinity ((shiftBoundaryMeasure μ S).prod ν)) :
    firstBoundaryLiftL μ S (scalarInfinityMul f g) =
      scalarInfinityMul (firstBoundaryLiftL μ S f) (firstBoundaryLiftL μ S g) := by
  apply Lp.ext
  have hp := (firstBoundaryMap_measurePreserving μ S).quasiMeasurePreserving.ae
    (scalarInfinityMul_ae f g)
  filter_upwards [firstBoundaryLiftL_ae μ S (scalarInfinityMul f g), hp,
    firstBoundaryLiftL_ae μ S f, firstBoundaryLiftL_ae μ S g,
    scalarInfinityMul_ae (firstBoundaryLiftL μ S f) (firstBoundaryLiftL μ S g)]
    with x ha hb hc hd he
  rw [ha, hb, he, hc, hd]

theorem firstBoundaryLiftL_nonnegative_iff
    (f : ScalarLInfinity ((shiftBoundaryMeasure μ S).prod ν)) :
    ScalarNonnegative (firstBoundaryLiftL μ S f) ↔ ScalarNonnegative f := by
  constructor
  · intro hf
    have hm : MeasurableSet {x | f x ∈ scalarPositiveCone} :=
      scalarPositiveCone_isClosed.measurableSet.preimage (Lp.stronglyMeasurable f).measurable
    have hpre : ∀ᵐ x ∂μ.prod ν, f (firstBoundaryMap μ S x) ∈ scalarPositiveCone := by
      filter_upwards [firstBoundaryLiftL_ae μ S f, hf] with x hx hp
      rwa [← hx]
    have hmap := (ae_map_iff (firstBoundaryMap_measurePreserving (ν := ν) μ S).measurable.aemeasurable hm).mpr hpre
    change ∀ᵐ x ∂(shiftBoundaryMeasure μ S).prod ν, f x ∈ scalarPositiveCone
    simpa only [(firstBoundaryMap_measurePreserving μ S).map_eq] using hmap
  · intro hf
    have hp := (firstBoundaryMap_measurePreserving μ S).quasiMeasurePreserving.ae hf
    filter_upwards [firstBoundaryLiftL_ae μ S f, hp] with x hx hp
    rwa [hx]

theorem firstBoundaryLiftL_fixed (hS : Measure.QuasiMeasurePreserving S μ μ)
    (f : ScalarLInfinity ((shiftBoundaryMeasure μ S).prod ν)) :
    scalarInfinityPullback (firstCoordinateShift S) (firstCoordinateShift_quasi hS)
      (firstBoundaryLiftL μ S f) = firstBoundaryLiftL μ S f := by
  have hm : AEStronglyMeasurable[firstInvariantSigma μ S]
      (fun z : X × Y => f (firstBoundaryMap μ S z)) (μ.prod ν) :=
    (Lp.stronglyMeasurable f).aestronglyMeasurable
  have hf := firstInvariantSigma_fixed hS hm
  apply Lp.ext
  filter_upwards [scalarInfinityPullback_ae (firstCoordinateShift S)
      (firstCoordinateShift_quasi hS) (firstBoundaryLiftL μ S f),
    firstBoundaryLiftL_ae μ S f,
    (firstCoordinateShift_quasi (ν := ν) hS).ae (firstBoundaryLiftL_ae μ S f), hf]
    with x hp hx hs hf
  exact hp.trans (hs.trans (hf.trans hx.symm))

theorem firstBoundaryLiftL_intertwine
    (T : X × Y → X × Y) (U : ShiftBoundarySpace μ S × Y → ShiftBoundarySpace μ S × Y)
    (hT : Measure.QuasiMeasurePreserving T (μ.prod ν) (μ.prod ν))
    (hU : Measure.QuasiMeasurePreserving U ((shiftBoundaryMeasure μ S).prod ν)
      ((shiftBoundaryMeasure μ S).prod ν))
    (hcomm : ∀ z, U (firstBoundaryMap μ S z) = firstBoundaryMap μ S (T z))
    (f : ScalarLInfinity ((shiftBoundaryMeasure μ S).prod ν)) :
    firstBoundaryLiftL μ S (scalarInfinityPullback U hU f) =
      scalarInfinityPullback T hT (firstBoundaryLiftL μ S f) := by
  apply Lp.ext
  have hp := (firstBoundaryMap_measurePreserving μ S).quasiMeasurePreserving.ae
    (scalarInfinityPullback_ae U hU f)
  filter_upwards [firstBoundaryLiftL_ae μ S (scalarInfinityPullback U hU f), hp,
    scalarInfinityPullback_ae T hT (firstBoundaryLiftL μ S f),
    hT.ae (firstBoundaryLiftL_ae μ S f)] with x ha hb hc hd
  rw [ha, hb, hc, hd, hcomm]

namespace FirstBoundaryProjection

variable {hS : Measure.QuasiMeasurePreserving S μ μ}
  {P : ScalarInvariantProjection (firstCoordinateShift (Y := Y) S)
    (firstCoordinateShift_quasi (ν := ν) hS)} (E : FirstBoundaryProjection hS P)

theorem norm_le (f : ScalarLInfinity (μ.prod ν)) : ‖E.toCLM f‖ ≤ ‖f‖ := by
  rw [← firstBoundaryLiftL_norm μ S, E.lift_eq]
  exact P.norm_le f

theorem positive (f : ScalarLInfinity (μ.prod ν)) (hf : ScalarNonnegative f) :
    ScalarNonnegative (E.toCLM f) := by
  rw [← firstBoundaryLiftL_nonnegative_iff, E.lift_eq]
  exact P.positive f hf

theorem lift_retract (f : ScalarLInfinity ((shiftBoundaryMeasure μ S).prod ν)) :
    E.toCLM (firstBoundaryLiftL μ S f) = f := by
  apply firstBoundaryLiftL_injective μ S
  rw [E.lift_eq, P.fixed _ (firstBoundaryLiftL_fixed hS f)]

theorem module_map (b : ScalarLInfinity ((shiftBoundaryMeasure μ S).prod ν))
    (f : ScalarLInfinity (μ.prod ν)) :
    E.toCLM (scalarInfinityMul (firstBoundaryLiftL μ S b) f) =
      scalarInfinityMul b (E.toCLM f) := by
  apply firstBoundaryLiftL_injective μ S
  rw [E.lift_eq, P.module_map _ _ (firstBoundaryLiftL_fixed hS b),
    firstBoundaryLiftL_mul, E.lift_eq]

theorem natural
    (T : X × Y → X × Y) (U : ShiftBoundarySpace μ S × Y → ShiftBoundarySpace μ S × Y)
    (hT : Measure.QuasiMeasurePreserving T (μ.prod ν) (μ.prod ν))
    (hU : Measure.QuasiMeasurePreserving U ((shiftBoundaryMeasure μ S).prod ν)
      ((shiftBoundaryMeasure μ S).prod ν))
    (hcomm : ∀ z, U (firstBoundaryMap μ S z) = firstBoundaryMap μ S (T z))
    (hshift : ∀ z, firstCoordinateShift S (T z) = T (firstCoordinateShift S z))
    (f : ScalarLInfinity (μ.prod ν)) :
    E.toCLM (scalarInfinityPullback T hT f) = scalarInfinityPullback U hU (E.toCLM f) := by
  apply firstBoundaryLiftL_injective μ S
  rw [E.lift_eq, P.natural T hT hshift, firstBoundaryLiftL_intertwine T U hT hU hcomm,
    E.lift_eq]

end FirstBoundaryProjection

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PublishedBoundary
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The published scalar boundary input

Bader--Furman, *Boundaries, rigidity of representations, and Lyapunov
exponents*, Proceedings ICM 2014, III, 71--96: Definition 2.3 (p. 73),
Remarks 2.4(1),(4) (pp. 73--74), and Theorem 2.7 (p. 75).
Adams--Elliott--Giordano, *Amenable Actions of Groups*, Transactions AMS
344 (1994), 803--822, Theorem 3.4 (pp. 810--811), supplies the scalar
conditional expectations for both amenable actions.

The means below act on actual scalar L-infinity classes. No operator
correction or algebra isomorphism is part of this input.
-/

namespace KadisonKastler

open MeasureTheory

universe u

/-- The application-specific existence statement for a countable group:
a probability boundary with scalar means for the original and separate
product actions, and unitary double ergodicity for the diagonal action. -/
def PublishedBoundary : Prop :=
  ∀ (G : Type u) [Group G] [Countable G] [TopologicalSpace G] [DiscreteTopology G],
    ∃ (D : Type u) (_ : MeasurableSpace D) (μ : Measure D)
      (_ : IsProbabilityMeasure μ) (α : NonsingularAction G D μ),
      Nonempty (ScalarBoundaryMean α) ∧
      Nonempty (ScalarBoundaryMean α.prod) ∧
      UnitaryDoubleErgodic.{u, u, u} α

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TwoRatioFiniteSites
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

@[simp] theorem twoRatioSiteShift_parameter (q : ℕ) (i : TwoRatioSite) :
    twoRatioSiteParameter (twoRatioSiteShift q i) = twoRatioSiteParameter i := by
  cases i <;> rfl

theorem twoRatioSiteShift_disjoint {n q : ℕ} (hn : n ≤ q) (k : ℕ) :
    List.Disjoint (twoRatioFiniteSites n)
      ((twoRatioFiniteSites k).map (twoRatioSiteShift q)) := by
  apply List.disjoint_left.mpr
  intro i hi hj
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hj
  cases j with
  | inl j =>
    have : q + j < n := (inl_mem_twoRatioFiniteSites _ _).mp hi
    omega
  | inr j =>
    have : q + j < n := (inr_mem_twoRatioFiniteSites _ _).mp hi
    omega

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_WeakFieldPullback
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.WeakOperatorRepresentative.evalHom_apply _root_.OAI.KadisonKastler.WeakOperatorRepresentative.eval_kernelProjection _root_.OAI.KadisonKastler.WeakOperatorRepresentative.eval_positiveKernelProjection _root_.OAI.KadisonKastler.WeakOperatorRepresentative.topElement_val _root_.OAI.KadisonKastler.tracialQuotientLinear_map _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Nonsingular pullback of weak operator fields

Composition preserves the measurable representatives and their uniform
bound. Nonsingularity makes the construction independent of representatives.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped BoundedContinuousFunction

noncomputable section

variable {D H : Type*} [MeasurableSpace D] {μ : Measure D}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace WeakOperatorField

@[simp]
theorem pullback_constant (T : D → D) (hT : Measure.QuasiMeasurePreserving T μ μ)
    (A : H →L[ℂ] H) : pullback T hT (operatorFieldConst μ A) = operatorFieldConst μ A := by
  change pullback T hT (operatorFieldQuotient (H := H) μ (operatorRepresentativeConst μ A)) = _
  rw [pullback_quotient, WeakOperatorRepresentative.pullback_constant]
  rfl

@[simp]
theorem pullback_id (q : WeakOperatorField (H := H) μ) :
    pullback id (Measure.QuasiMeasurePreserving.id μ) q = q := by
  obtain ⟨F, rfl⟩ := operatorFieldQuotient_surjective (H := H) μ q
  rw [pullback_quotient, WeakOperatorRepresentative.pullback_id]

theorem pullback_comp (T S : D → D)
    (hT : Measure.QuasiMeasurePreserving T μ μ)
    (hS : Measure.QuasiMeasurePreserving S μ μ) (q : WeakOperatorField (H := H) μ) :
    pullback S hS (pullback T hT q) = pullback (T ∘ S) (hT.comp hS) q := by
  obtain ⟨F, rfl⟩ := operatorFieldQuotient_surjective (H := H) μ q
  rw [pullback_quotient, pullback_quotient, pullback_quotient,
    WeakOperatorRepresentative.pullback_comp]

end WeakOperatorField

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TypeIIIMatrixCorner
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Countable matrix corners in type III factors

The absence of nonzero finite projections gives a proper isometry. Its
wandering projections are nonzero and orthogonal. A projection supremum
completes them to a partition of one; the published comparison theorem
then joins the pieces by partial isometries.
-/

namespace KadisonKastler

open Generator.Tracial Filter
open scoped BigOperators Topology

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

/-- The closed initial Hilbert space associated to a concrete projection. -/
def typeIIIInitialSpace (p : AlgebraProjection M) : Submodule ℂ H :=
  (p.val : H →L[ℂ] H).range

instance typeIIIInitialSpaceComplete (p : AlgebraProjection M) :
    CompleteSpace (typeIIIInitialSpace p) := by
  have hp : IsIdempotentElem (p.val : H →L[ℂ] H) := by
    change (p.val : H →L[ℂ] H) * p.val = p.val
    exact congrArg Subtype.val p.property.isIdempotentElem.eq
  exact (ContinuousLinearMap.IsIdempotentElem.isClosed_range hp).completeSpace_coe

theorem typeIIIInitialSpace_projection (p : AlgebraProjection M) :
    (p.val : H →L[ℂ] H) = (typeIIIInitialSpace p).starProjection := by
  have hp : IsStarProjection (p.val : H →L[ℂ] H) := ⟨by
    change (p.val : H →L[ℂ] H) * p.val = p.val
    exact congrArg Subtype.val p.property.isIdempotentElem.eq,
    congrArg Subtype.val p.property.isSelfAdjoint.star_eq⟩
  obtain ⟨_, he⟩ := isStarProjection_iff_eq_starProjection_range.mp hp
  exact he

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RemoteSiteDoubling
attribute [-instance] _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Interleaving two site families beyond a finite prefix -/

namespace KadisonKastler

def remoteTwoRatioDoubling (n : ℕ) : (TwoRatioSite ⊕ TwoRatioSite) ≃ TwoRatioSite :=
  (Equiv.sumSumSumComm ℕ ℕ ℕ ℕ).trans
    (Equiv.sumCongr (remoteNatDoubling n) (remoteNatDoubling n))

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TwoRatioFiniteMatrix
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The increasing full matrix algebras of the two-ratio product -/

namespace KadisonKastler

open Generator

noncomputable section

def twoRatioMatrixSize (n : ℕ) : ℕ :=
  Fintype.card (MatrixSiteBlockIndex (twoRatioFiniteSites n))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TwoRatioRemoteBlock
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Remote copies of two-ratio matrix blocks

Both site families are shifted beyond the two specified finite stages.
The shift preserves the density parameters, so the new block has exactly
the old matrix moments and is independent of the prescribed local algebra.
-/

namespace KadisonKastler

open Generator

noncomputable section

def twoRatioRemoteSites (k n : ℕ) : List TwoRatioSite :=
  (twoRatioFiniteSites k).map (twoRatioSiteShift (max k n))

theorem twoRatioRemoteSites_nodup (k n : ℕ) : (twoRatioRemoteSites k n).Nodup :=
  (twoRatioFiniteSites_nodup k).map (twoRatioSiteShift_injective _)

def twoRatioRemoteIndex (k n : ℕ) :
    Fin (twoRatioMatrixSize k) ≃ MatrixSiteBlockIndex (twoRatioRemoteSites k n) :=
  (Fintype.equivFin (MatrixSiteBlockIndex (twoRatioFiniteSites k))).symm.trans
    (matrixSiteBlockMapEquiv (twoRatioSiteShift (max k n)) (twoRatioFiniteSites k))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TwoRatioRemoteComplement
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Finite complements for remote product blocks -/

namespace KadisonKastler

open Generator

noncomputable section

def twoRatioComplementSites (k n m : ℕ) : List TwoRatioSite := by
  classical
  exact (twoRatioFiniteSites m).filter fun i =>
    decide (i ∉ twoRatioFiniteSites k ∧ i ∉ twoRatioRemoteSites k n)

@[simp] theorem mem_twoRatioComplementSites (k n m : ℕ) (i : TwoRatioSite) :
    i ∈ twoRatioComplementSites k n m ↔ i ∈ twoRatioFiniteSites m ∧
      i ∉ twoRatioFiniteSites k ∧ i ∉ twoRatioRemoteSites k n := by
  simp [twoRatioComplementSites]

theorem twoRatioComplementSites_nodup (k n m : ℕ) :
    (twoRatioComplementSites k n m).Nodup :=
  (twoRatioFiniteSites_nodup m).filter _

theorem twoRatioComplementSites_disjoint (k n m : ℕ) :
    List.Disjoint (twoRatioFiniteSites k) (twoRatioComplementSites k n m) ∧
      List.Disjoint (twoRatioRemoteSites k n) (twoRatioComplementSites k n m) := by
  constructor
  · exact List.disjoint_left.mpr fun i hi hj =>
      ((mem_twoRatioComplementSites k n m i).mp hj).2.1 hi
  · exact List.disjoint_left.mpr fun i hi hj =>
      ((mem_twoRatioComplementSites k n m i).mp hj).2.2 hi

def twoRatioComplementSize (k n m : ℕ) : ℕ :=
  Fintype.card (MatrixSiteBlockIndex (twoRatioComplementSites k n m))

end

end KadisonKastler

end OAI
end


