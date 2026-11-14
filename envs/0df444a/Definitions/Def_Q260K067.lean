-- Prove2me | Definitions.Def_Q260K067
-- name    : Q260K067
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T07:24:12.614213+00:00
-- url     : https://prove2.me/theorems/87c27b2c-b5b7-47d4-b17c-7baa78f45587
-- title:
--   Definitions bundle Q260K067 of the split of OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 115 declarations of OpenAI's Lean: 35 definitions, 6 inductive types or structures and 74 theorems. The definitions and types are `OAI.KadisonKastler.AsymptoticallyCentral`, `OAI.KadisonKastler.CountableProjectionCopies.fullCopyIsometry`, `OAI.KadisonKastler.CountableProjectionCopies.fullCopyUnitary`, `OAI.KadisonKastler.CuntzFamily.conjugate`, `OAI.KadisonKastler.ExpectedMatrixSubfactorModel`, `OAI.KadisonKastler.FaithfulVectorStateHomogeneity`, `OAI.KadisonKastler.FiniteInnerAverage.comp`, `OAI.KadisonKastler.FiniteInnerAverage.identity`, `OAI.KadisonKastler.MatrixSiteWord.letterAt`, `OAI.KadisonKastler.MatrixSiteWord.weight`, `OAI.KadisonKastler.ModularConjugationData`, `OAI.KadisonKastler.ModularConjugationData.rightAction`, `OAI.KadisonKastler.PointedMatrixProduct`, `OAI.KadisonKastler.PointedMatrixProduct.universeLift`, `OAI.KadisonKastler.PointedMatrixSites`, `OAI.KadisonKastler.PointedMatrixSites.blockEntry`, `OAI.KadisonKastler.PointedMatrixSites.finiteBlock`, `OAI.KadisonKastler.PointedMatrixSites.reindexEquivalence`, `OAI.KadisonKastler.PointedMatrixSites.siteGenerator`, `OAI.KadisonKastler.PointedMatrixSites.sumSite`, `OAI.KadisonKastler.PointedMatrixSites.transport`, `OAI.KadisonKastler.PointedMatrixSites.twoRatioComplementMatrix`, `OAI.KadisonKastler.PointedMatrixSites.twoRatioMatrix`, `OAI.KadisonKastler.PointedMatrixSites.twoRatioRemoteMatrix`, `OAI.KadisonKastler.PointedMatrixSites.twoRatioStages`, `OAI.KadisonKastler.PointedMatrixSites.twoRatioStages_coordinates`, `OAI.KadisonKastler.PointedMatrixSites.wordOperator`, `OAI.KadisonKastler.PointedMatrixSites.wordVector`, `OAI.KadisonKastler.ProductMatrixStages`, `OAI.KadisonKastler.ProductMatrixStages.algebra`, `OAI.KadisonKastler.ProductMatrixStages.localSwaps`, `OAI.KadisonKastler.ProjectionCentralVector`, `OAI.KadisonKastler.ProjectionDiffuse`, `OAI.KadisonKastler.PublishedDixmierAveraging`, `OAI.KadisonKastler.PublishedFactorialModularCore`, `OAI.KadisonKastler.TypeIII1Factor`, `OAI.KadisonKastler.conjugateRightAlgebra`, `OAI.KadisonKastler.conjugationRealStarAlgEquiv`, `OAI.KadisonKastler.innerUnitaryOrbit`, `OAI.KadisonKastler.matrixSiteBlockWord` and 1 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `KadisonKastler_AsymptoticCentralizer`, `KadisonKastler_CentralDefectMultiplication`, `KadisonKastler_CentralDefectSelfAdjoint`, `KadisonKastler_ConjugateRightAlgebra`, `KadisonKastler_ConjugationFunctionalCalculus`, `KadisonKastler_CornerHomogeneityApplication`, `KadisonKastler_CuntzChangeOfBasis`, `KadisonKastler_CyclicGeneratorSpan`, `KadisonKastler_FiniteCentralAveraging`, `KadisonKastler_FiniteInnerComposition`, `KadisonKastler_FullCopyHilbertSum`, `KadisonKastler_ModularConjugationData`, `KadisonKastler_ModularRightAction`, `KadisonKastler_ModularSiteEigen`, `KadisonKastler_PointedBlockMoments`, `KadisonKastler_PointedCyclicEquivalence`, `KadisonKastler_PointedFiniteBlock`, `KadisonKastler_PointedMatrixProduct`, `KadisonKastler_PointedMatrixSum`, `KadisonKastler_PointedProductLift`, `KadisonKastler_PointedSiteBalance`, `KadisonKastler_PointedSitesTransport`, `KadisonKastler_PointedWordMoments`, `KadisonKastler_PointedWordReduction`, `KadisonKastler_ProductMatrixStages`, `KadisonKastler_ProjectionCentralSpace`, `KadisonKastler_PublishedDixmier`, `KadisonKastler_PublishedExpectedMatrixSubfactor`, `KadisonKastler_PublishedModularCoreType`, `KadisonKastler_TwoRatioFiniteMatrix`, `KadisonKastler_TwoRatioRemoteBlock`, `KadisonKastler_TwoRatioRemoteComplement`, `KadisonKastler_TwoRatioStages`, `KadisonKastler_TypeIFactorStability`.
--
--   **Imports.** It imports the published bundle `Def_StrongKadisonKastler`; the bundle `Q260K029` of this split.
--
--   **Imported by** (directly, in this split): the bundle `Q260K032`; the statements `OAI.KadisonKastler.FaithfulVectorStateHomogeneity.spatial_transport`, `OAI.KadisonKastler.ModularConjugationData.expected_right_data`, `OAI.KadisonKastler.ModularConjugationData.rightAction_commute`, `OAI.KadisonKastler.ModularConjugationData.rightAction_mem`, `OAI.KadisonKastler.ModularConjugationData.rightAction_star`, `OAI.KadisonKastler.PointedMatrixSites.constructed_represented_expected_matrix_subfactor`, `OAI.KadisonKastler.PointedMatrixSites.exists_scaling_coisometry_near`, `OAI.KadisonKastler.PointedMatrixSites.exists_spatial_scaling_conjugations`, `OAI.KadisonKastler.PointedMatrixSites.represented_expected_matrix_subfactor`, `OAI.KadisonKastler.PointedMatrixSites.spatial_state_homogeneity`, `OAI.KadisonKastler.TypeIIIFactor.corner_comparison_of_vector_state_homogeneity` and `OAI.KadisonKastler.expected_modular_corrected_cyclic_separating`; the proofs of `OAI.KadisonKastler.ModularConjugationData.expected_right_data`, `OAI.KadisonKastler.ModularConjugationData.rightAction_commute`, `OAI.KadisonKastler.ModularConjugationData.rightAction_mem`, `OAI.KadisonKastler.ModularConjugationData.rightAction_star`, `OAI.KadisonKastler.TypeIIIFactor.corner_comparison_of_vector_state_homogeneity`, `OAI.KadisonKastler.TypeIIIFactor.exists_relative_matrix_spatial_equiv`, `OAI.KadisonKastler.expected_modular_corrected_cyclic_separating` and `OAI.KadisonKastler.universalStrongStability_of_factors`.
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
import Mathlib.Analysis.Normed.Module.Normalize
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
import Mathlib.MeasureTheory.Function.ContinuousMapDense
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
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.Bounds.OrderIso
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.Probability.Distributions.Cauchy
import Mathlib.Probability.Moments.ComplexMGF
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
import Definitions.Def_Q260K029

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ConjugateRightAlgebra
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The actual conjugate right algebra

An involutive conjugate-linear Hilbert isometry transports a concrete von
Neumann algebra to its exact operator image. Conjugating an ambient
contractive projection twice transports injectivity as well. These constructions preserve the represented algebraic operations.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem centralizer_image_conjugationOperator
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J) (S : Set (H →L[ℂ] H)) :
    Set.centralizer (conjugationOperator J '' S) =
      conjugationOperator J '' Set.centralizer S := by
  ext x
  constructor
  · intro hx
    refine ⟨conjugationOperator J x, ?_, conjugationOperator_twice J hJ x⟩
    intro y hy
    have he := congrArg (conjugationOperator J) (hx _ ⟨y, hy, rfl⟩)
    rw [conjugationOperator_mul J hJ, conjugationOperator_mul J hJ,
      conjugationOperator_twice J hJ] at he
    exact he
  · rintro ⟨y, hy, rfl⟩ z ⟨w, hw, rfl⟩
    rw [← conjugationOperator_mul J hJ, ← conjugationOperator_mul J hJ, hy w hw]

/-- The actual image `J R J`, as a concrete von Neumann algebra. -/
def conjugateRightAlgebra (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (R : VonNeumannAlgebra H) : VonNeumannAlgebra H where
  toStarSubalgebra := conjugateRightStarAlgebra J hJ R
  centralizer_centralizer' := by
    change Set.centralizer (Set.centralizer (conjugationOperator J '' (R : Set (H →L[ℂ] H)))) =
      conjugationOperator J '' (R : Set (H →L[ℂ] H))
    rw [centralizer_image_conjugationOperator J hJ,
      centralizer_image_conjugationOperator J hJ, R.centralizer_centralizer]

theorem conjugateRightAlgebra_coe (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (R : VonNeumannAlgebra H) :
    (conjugateRightAlgebra J hJ R : Set (H →L[ℂ] H)) =
      conjugationOperator J '' (R : Set (H →L[ℂ] H)) := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ConjugationFunctionalCalculus
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.centralVectorDefect_apply _root_.OAI.KadisonKastler.conjugateMatrixUnits_entry _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.mem_projectionFamilyCommutationSpace _root_.OAI.KadisonKastler.rightVectorLinear_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Real functional calculus under an antiunitary conjugation -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- An involutive antiunitary acts by a real star-algebra automorphism. -/
def conjugationRealStarAlgEquiv (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J) :
    (H →L[ℂ] H) ≃⋆ₐ[ℝ] (H →L[ℂ] H) where
  toFun := conjugationOperator J
  invFun := conjugationOperator J
  left_inv := conjugationOperator_twice J hJ
  right_inv := conjugationOperator_twice J hJ
  map_add' := conjugationOperator_add J
  map_mul' := conjugationOperator_mul J hJ
  map_smul' r a := by
    change conjugationOperator J ((r : ℂ) • a) = (r : ℂ) • conjugationOperator J a
    rw [conjugationOperator_smul]
    simp
  map_star' := conjugationOperator_star J hJ

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CentralDefectSelfAdjoint
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Reducing a central-vector defect to a self-adjoint contraction -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem centralVectorDefect_star_norm (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (ξ : H) (hξ : J ξ = ξ) (a : H →L[ℂ] H) :
    ‖centralVectorDefect J ξ (star a)‖ = ‖centralVectorDefect J ξ a‖ := by
  have he : J (centralVectorDefect J ξ a) = -centralVectorDefect J ξ (star a) := by
    change J (a ξ - J (star a (J ξ))) = -(star a ξ - J (star (star a) (J ξ)))
    rw [map_sub,hξ,hJ,star_star]
    abel
  have hn := congrArg norm he
  simpa only [J.norm_map,norm_neg] using hn.symm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CentralDefectMultiplication
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Product estimates for the central-vector defect -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem centralVectorDefect_mul
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (ξ : H) (a b : Algebra M) :
    centralVectorDefect J ξ (a*b).val =
      a.val (centralVectorDefect J ξ b.val) +
        conjugationOperator J (star b).val (centralVectorDefect J ξ a.val) := by
  have hc := VonNeumannAlgebra.mem_commutant_iff.mp (hright (star b)) a.val a.property
  have he : a.val (conjugationOperator J (star b).val ξ) =
      conjugationOperator J (star b).val (a.val ξ) :=
    congrArg (fun T : H →L[ℂ] H => T ξ) hc
  simp only [StarMemClass.coe_star] at he
  simp only [centralVectorDefect_apply,MulMemClass.coe_mul,star_mul,
    conjugationOperator_mul J hJ,mul_apply_eq_comp,map_sub,StarMemClass.coe_star]
  rw [he]
  abel

theorem centralVectorDefect_mul_norm_le
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (ξ : H) (a b : Algebra M) :
    ‖centralVectorDefect J ξ (a*b).val‖ ≤
      ‖a‖ * ‖centralVectorDefect J ξ b.val‖ +
        ‖b‖ * ‖centralVectorDefect J ξ a.val‖ := by
  rw [centralVectorDefect_mul J hJ hright]
  apply (norm_add_le _ _).trans
  apply add_le_add (a.val.le_opNorm _)
  have hn := (conjugationOperator J (star b).val).le_opNorm (centralVectorDefect J ξ a.val)
  rwa [norm_conjugationOperator J hJ,StarMemClass.coe_star,norm_star] at hn

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_AsymptoticCentralizer
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The C-star algebra of asymptotically central bounded sequences

The centrality defect is measured on the standard reference vector.
Its product estimate and adjoint symmetry give the sequence algebra
used in the bicentralizer argument (Haagerup, Acta Math.158(1987), §1).
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

def AsymptoticallyCentral (J : H ≃ₗᵢ⋆[ℂ] H) (ξ : H)
    (x : BoundedSequence (Algebra M)) : Prop :=
  Tendsto (fun n => ‖centralVectorDefect J ξ (x n).val‖) atTop (𝓝 0)

theorem AsymptoticallyCentral.add {J : H ≃ₗᵢ⋆[ℂ] H} {ξ : H}
    {x y : BoundedSequence (Algebra M)} (hx : AsymptoticallyCentral J ξ x)
    (hy : AsymptoticallyCentral J ξ y) : AsymptoticallyCentral J ξ (x+y) := by
  change Tendsto (fun n => ‖centralVectorDefect J ξ ((x n).val + (y n).val)‖) atTop (𝓝 0)
  simp only [map_add]
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun n => norm_add_le (centralVectorDefect J ξ (x n).val) (centralVectorDefect J ξ (y n).val))
  simpa only [add_zero] using Filter.Tendsto.add hx hy

theorem AsymptoticallyCentral.star
    {J : H ≃ₗᵢ⋆[ℂ] H} (hJ : Function.Involutive J) {ξ : H} (hξ : J ξ = ξ)
    {x : BoundedSequence (Algebra M)} (hx : AsymptoticallyCentral J ξ x) :
    AsymptoticallyCentral J ξ (star x) := by
  change Tendsto (fun n => ‖centralVectorDefect J ξ (Star.star (x n).val)‖) atTop (𝓝 0)
  simpa only [AsymptoticallyCentral,centralVectorDefect_star_norm J hJ ξ hξ] using hx

theorem AsymptoticallyCentral.mul
    {J : H ≃ₗᵢ⋆[ℂ] H} (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant) {ξ : H}
    {x y : BoundedSequence (Algebra M)} (hx : AsymptoticallyCentral J ξ x)
    (hy : AsymptoticallyCentral J ξ y) : AsymptoticallyCentral J ξ (x*y) := by
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun n => (centralVectorDefect_mul_norm_le J hJ hright ξ (x n) (y n)).trans
      (add_le_add
        (mul_le_mul_of_nonneg_right (x.norm_coe_le_norm n) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (y.norm_coe_le_norm n) (norm_nonneg _))))
  simpa only [mul_zero,add_zero] using (hy.const_mul ‖x‖).add (hx.const_mul ‖y‖)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CornerHomogeneityApplication
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The exact corner specialization of state homogeneity

Connes--Størmer, J. Funct. Anal. 28 (1978), 187--196, states norm
transitivity of inner automorphisms on faithful normal states of a type
III₁ factor. Its vector-state special case gives the corner application formalized here.
-/

namespace KadisonKastler

open Generator.Tracial NormedSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

def FaithfulVectorStateHomogeneity (M : VonNeumannAlgebra H) : Prop :=
  ∀ ξ ζ : H, ‖ξ‖=1 → ‖ζ‖=1 →
    Function.Injective (algebraVectorMap M ξ) →
    Function.Injective (algebraVectorMap M ζ) →
    ∀ ε : ℝ, 0 < ε → ∃ u : unitary (Algebra M),
      ‖sandwichFunctional (vectorFunctional ξ) u.val-vectorFunctional ζ‖ < ε

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CuntzChangeOfBasis
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.centralVectorDefect_apply _root_.OAI.KadisonKastler.conjugateMatrixUnits_entry _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.mem_projectionFamilyCommutationSpace _root_.OAI.KadisonKastler.rightVectorLinear_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Unitary change between two finite Cuntz families -/

namespace KadisonKastler.CuntzFamily

open scoped BigOperators

noncomputable section

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype ι] [DecidableEq ι]

def conjugate (S : CuntzFamily ι H) (J : H ≃ₗᵢ⋆[ℂ] H)
    (hJ : Function.Involutive J) : CuntzFamily ι H where
  entry i := conjugationOperator J (S.entry i)
  orthogonal i j := by
    change star (conjugationRealStarAlgEquiv J hJ (S.entry i))*
      conjugationRealStarAlgEquiv J hJ (S.entry j) = _
    rw [← map_star,← map_mul,S.orthogonal]
    split_ifs <;> simp
  total := by
    change (∑ i, conjugationRealStarAlgEquiv J hJ (S.entry i)*
      star (conjugationRealStarAlgEquiv J hJ (S.entry i)))=1
    simp only [← map_star,← map_mul,← map_sum,S.total,map_one]

end

end KadisonKastler.CuntzFamily

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProductMatrixStages
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSignedGroup_finite _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.Generator.MatrixUnitSystem.adaptedBasis_apply _root_.OAI.Generator.MatrixUnitSystem.initialColumn_apply _root_.OAI.Generator.orthonormalMatrixUnits_entry_apply _root_.OAI.KadisonKastler.MatrixSiteWord.eval_append _root_.OAI.KadisonKastler.MatrixSiteWord.eval_cons _root_.OAI.KadisonKastler.MatrixSiteWord.eval_nil _root_.OAI.KadisonKastler.MatrixSiteWord.eval_reindex _root_.OAI.KadisonKastler.MatrixSiteWord.eval_star _root_.OAI.KadisonKastler.ScalarInvariantMean.conjugationFamily_apply _root_.OAI.KadisonKastler.ScalarInvariantMean.stateOrbitScalar_apply _root_.OAI.KadisonKastler.conjugateMatrixUnits_entry _root_.OAI.KadisonKastler.conjugatedMatrixUnits_entry _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.spatialMatrixUnits_entry _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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

/-- An increasing sequence of finite product matrix algebras, in its
cyclic separating product representation. This describes the construction
data rather than any of its centralizer or factor consequences. -/
structure ProductMatrixStages where
  size : ℕ → ℕ
  matrix : ∀ n, MatrixUnitSystem (Fin (size n)) (H →L[ℂ] H)
  increasing : Monotone (fun n => (matrix n).algebra)
  vector : H
  unit_vector : ‖vector‖ = 1
  local_cyclic : DenseRange
    (fun p : Σ n, (matrix n).algebra => (p.2 : H →L[ℂ] H) vector)
  separating : Function.Injective (algebraVectorMap
    (generatedVonNeumannAlgebra (⨆ n, (matrix n).algebra)) vector)
  remote : ∀ k n, Nonempty (RemoteProductBlock size matrix vector k n)

namespace ProductMatrixStages

variable (P : ProductMatrixStages (H := H))

def algebra : VonNeumannAlgebra H :=
  generatedVonNeumannAlgebra (⨆ n, (P.matrix n).algebra)

theorem local_le (n : ℕ) : (P.matrix n).algebra ≤ P.algebra.toStarSubalgebra := by
  intro x hx
  exact subset_generatedVonNeumannAlgebra _
    ((le_iSup (fun n => (P.matrix n).algebra) n) hx)

/-- The actual finite swap is assembled from the two matrix systems.
Triple product moments put it in the centralizer of the full algebra. -/
def localSwaps : LocalProductSwaps P.algebra P.vector where
  localAlgebra n := (P.matrix n).algebra
  local_le := P.local_le
  dense := P.local_cyclic
  independent_swap k a n := by
    classical
    let R := Classical.choice (P.remote k n)
    let E := (P.matrix k).product R.copy R.commutes
    let u := finiteMatrixBlockSwap E
    have hE : E.algebra ≤ P.algebra.toStarSubalgebra := by
      dsimp [E]
      rw [MatrixUnitSystem.product_algebra_eq_sup]
      exact sup_le (P.local_le k) R.copy_mem
    have hu : (u : H →L[ℂ] H) ∈ P.algebra := hE (finiteMatrixBlockSwap_mem E)
    refine ⟨u, hu, ?_, ?_⟩
    · apply productStateCentralizes_of_local (fun j => (P.matrix j).algebra) P.increasing
      intro m x hx
      obtain ⟨r, C, hc, hle, β, hβ⟩ := R.complement m
      exact finiteMatrixBlockSwap_product_centralizes E C hc (productVectorLinear P.vector)
        (fun i j => productVectorState P.vector ((P.matrix k).entry i j)) β hβ x (hle hx)
    · intro b
      exact finiteMatrixBlockSwap_independent (P.matrix k) R.copy R.commutes
        (productVectorLinear P.vector) b (fun i j => R.independent i j b) a a.property

end ProductMatrixStages

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PointedMatrixProduct
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSignedGroup_finite _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Finite-site coordinates for pointed matrix products

The finite moments below identify the actual matrix-state product. They
do not include any assertion about factor type, centralizers or absorption.
-/

namespace KadisonKastler

open UnitalTomsWinter

noncomputable section

universe u

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A coordinate description of the product of two-dimensional matrix
states. Only distinct-site moments are needed: repeated entries at a
site are reduced by the matrix-unit identities. -/
structure PointedMatrixSites {I : Type*} (M : VonNeumannAlgebra H) (Ω : H) (ν : I → ℝ) where
  valid : ∀ i, 0 < ν i ∧ ν i < 1
  site : I → Generator.MatrixUnitSystem (Fin 2) (H →L[ℂ] H)
  commuting : ∀ i j, i ≠ j → ∀ a b c d,
    Commute ((site i).entry a b) ((site j).entry c d)
  generates : M = generatedVonNeumannAlgebra (⨆ i, (site i).algebra)
  unit_vector : ‖Ω‖ = 1
  cyclic : DenseRange (algebraVectorMap M Ω)
  separating : Function.Injective (algebraVectorMap M Ω)
  moments : ∀ (l : List I), l.Nodup → ∀ (r c : I → Fin 2),
    inner ℂ Ω (((l.map fun i => (site i).entry (r i) (c i)).prod) Ω) =
      (l.map fun i => if r i = c i then (twoSiteWeight (ν i) (r i) : ℂ) else 0).prod

/-- A concrete pointed matrix product in its faithful product-state
representation. This is construction data, not a classification. -/
structure PointedMatrixProduct {I : Type} (ν : I → ℝ) where
  K : Type u
  [normedK : NormedAddCommGroup K]
  [innerK : InnerProductSpace ℂ K]
  [completeK : CompleteSpace K]
  [nontrivialK : Nontrivial K]
  [separableK : TopologicalSpace.SeparableSpace K]
  algebra : VonNeumannAlgebra K
  vector : K
  coordinates : PointedMatrixSites algebra vector ν

attribute [instance] PointedMatrixProduct.normedK PointedMatrixProduct.innerK
  PointedMatrixProduct.completeK PointedMatrixProduct.nontrivialK
  PointedMatrixProduct.separableK

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CyclicGeneratorSpan
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

/-- A cyclic representation generated by a star-stable family is already
cyclic on any invariant word span containing its cyclic vector. -/
theorem denseRange_linearCombination_of_cyclic_generators
    (M : VonNeumannAlgebra H) (Ω : H) (g : J → H →L[ℂ] H) (v : I → H)
    (hM : M = generatedVonNeumannAlgebra (StarAlgebra.adjoin ℂ (Set.range g)))
    (hcyclic : DenseRange (algebraVectorMap M Ω))
    (hstar : ∀ j, ∃ k, g k = star (g j))
    (hΩ : Ω ∈ LinearMap.range (Finsupp.linearCombination ℂ v))
    (hinv : ∀ j i, g j (v i) ∈ LinearMap.range (Finsupp.linearCombination ℂ v)) :
    DenseRange (Finsupp.linearCombination ℂ v) := by
  let V := (LinearMap.range (Finsupp.linearCombination ℂ v)).topologicalClosure
  have hc (j : J) : V.starProjection * g j = g j * V.starProjection := by
    apply Generator.starProjection_commutes_of_invariant
    · exact invariant_closed_linearCombination_range v (g j) (hinv j)
    · obtain ⟨k, hk⟩ := hstar j
      rw [← hk]
      exact invariant_closed_linearCombination_range v (g k) (hinv k)
  have hS : StarAlgebra.adjoin ℂ (Set.range g) ≤
      StarSubalgebra.centralizer ℂ {V.starProjection} := by
    apply StarAlgebra.adjoin_le
    rintro _ ⟨j, rfl⟩
    change g j ∈ StarSubalgebra.centralizer ℂ {V.starProjection}
    rw [StarSubalgebra.mem_centralizer_iff]
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact ⟨hc j, by simpa only [(isStarProjection_starProjection (U := V)).isSelfAdjoint.star_eq] using hc j⟩
  have hcomm (a : Algebra M) : V.starProjection * a.val = a.val * V.starProjection := by
    have ha0 : (a : H →L[ℂ] H) ∈ (M : Set (H →L[ℂ] H)) := a.property
    have ha : (a : H →L[ℂ] H) ∈
        (generatedVonNeumannAlgebra (StarAlgebra.adjoin ℂ (Set.range g)) :
          Set (H →L[ℂ] H)) :=
      (congrArg (fun Q : VonNeumannAlgebra H =>
        (a : H →L[ℂ] H) ∈ (Q : Set (H →L[ℂ] H))) hM).mp ha0
    rw [generatedVonNeumannAlgebra_coe] at ha
    have hp : V.starProjection ∈ Set.centralizer
        (StarAlgebra.adjoin ℂ (Set.range g) : Set (H →L[ℂ] H)) := by
      intro x hx
      exact ((StarSubalgebra.mem_centralizer_iff ℂ).mp (hS hx) _ (Set.mem_singleton _)).1.symm
    exact ha _ hp
  have hpΩ : V.starProjection Ω = Ω :=
    Submodule.starProjection_eq_self_iff.mpr (Submodule.le_topologicalClosure _ hΩ)
  have hcontains (a : Algebra M) : a.val Ω ∈ V := by
    apply Submodule.starProjection_eq_self_iff.mp
    calc
      V.starProjection (a.val Ω) = a.val (V.starProjection Ω) :=
        congrArg (fun T : H →L[ℂ] H => T Ω) (hcomm a)
      _ = a.val Ω := by rw [hpΩ]
  intro x
  change x ∈ V
  exact hcyclic.induction_on (p := fun y => y ∈ V) x (Submodule.isClosed_topologicalClosure _)
    (fun a => hcontains a)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PublishedDixmier
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The published Dixmier averaging input

Only the contraction case is retained. Blackadar, *Operator Algebras*,
Definition III.2.5.16 and Theorem III.2.5.18, p. 282 (PDF p. 290), state that
the norm-closed convex hull of the unitary conjugates of an element of a
von Neumann algebra meets its center. This input contains no comparison
between different algebras and no perturbation bound.

Primary text: https://bruceblackadar.com/Mathematics/Cycr.pdf
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def innerUnitaryOrbit (N : VonNeumannAlgebra H) (x : H →L[ℂ] H) :
    Set (H →L[ℂ] H) :=
  Set.range (fun u : unitary (Algebra N) => unitaryConj (ambientAlgebraUnitary u) x)

/-- The published averaging statement used to identify centers. -/
def PublishedDixmierAveraging (N : VonNeumannAlgebra H) : Prop :=
  ∀ x ∈ unitBall N, ∃ z ∈ concreteCenter N,
    z ∈ closure (convexHull ℝ (innerUnitaryOrbit N x))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteInnerComposition
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Composition and scalar invariance of finite inner averages -/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

namespace FiniteInnerAverage

/-- Applying one finite average after another is again a finite average. -/
def comp (B A : FiniteInnerAverage M) : FiniteInnerAverage M where
  Index := A.Index × B.Index
  fintype := inferInstance
  nonempty := inferInstance
  unitary p := B.unitary p.2 * A.unitary p.1

end FiniteInnerAverage

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteCentralAveraging
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.CommonTracialPositionData.rightEquiv_transportEquiv _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.ScalarInvariantMean.conjugationFamily_apply _root_.OAI.KadisonKastler.ScalarInvariantMean.stateOrbitScalar_apply _root_.OAI.KadisonKastler.StandardTracialPosition.conjugation_algebraVector _root_.OAI.KadisonKastler.StandardTracialPosition.diagonalRepresentation_vector _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.concreteDerivation_apply _root_.OAI.KadisonKastler.concreteDiagonalSequenceUnitary_coe _root_.OAI.KadisonKastler.concreteDiagonalSequence_apply _root_.OAI.KadisonKastler.concreteDiagonalUnitary_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.matrixLiftUnitaryAt_coe _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.minimalCyclicRetraction_compression _root_.OAI.KadisonKastler.productBoundaryRepresentation_coe _root_.OAI.KadisonKastler.rescaledGraphMap_apply _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.typeICyclicHom_apply _root_.OAI.KadisonKastler.typeICyclicOperator_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Arbitrarily accurate finite averages toward the center -/

namespace KadisonKastler

open Generator.Tracial
open scoped ComplexStarModule

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

namespace FiniteInnerAverage

/-- The one-term average. -/
def identity (M : VonNeumannAlgebra H) : FiniteInnerAverage M where
  Index := Unit
  fintype := inferInstance
  nonempty := inferInstance
  unitary _ := 1

@[simp] theorem identity_apply (x : H →L[ℂ] H) : (identity M).apply x = x := by
  change finiteAverage (fun _ : Unit =>
    unitaryConj (ambientAlgebraUnitary (1 : _root_.unitary (Algebra M))) x) = x
  have h : unitaryConj (ambientAlgebraUnitary (1 : _root_.unitary (Algebra M))) x = x := by
    change (1 : H →L[ℂ] H) * x * star (1 : H →L[ℂ] H) = x
    simp
  rw [h]
  exact finiteAverage_const x

end FiniteInnerAverage

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FullCopyHilbertSum
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.CommonTracialPositionData.rightEquiv_transportEquiv _root_.OAI.KadisonKastler.FiniteInnerAverage.algebraApply_sub _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.StandardTracialPosition.diagonalRepresentation_vector _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.concreteDerivation_apply _root_.OAI.KadisonKastler.concreteDiagonalSequenceUnitary_coe _root_.OAI.KadisonKastler.concreteDiagonalSequence_apply _root_.OAI.KadisonKastler.concreteDiagonalUnitary_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.matrixLiftUnitaryAt_coe _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.minimalCyclicRetraction_compression _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Full projection copies identify the countable Hilbert amplification -/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

namespace CountableProjectionCopies

variable (C : CountableProjectionCopies M (⟨1,IsStarProjection.one _⟩ : AlgebraProjection M))

def fullCopyIsometry (i : ℕ) : H →ₗᵢ[ℂ] H where
  toLinearMap := (C.witness i).val.toLinearMap
  norm_map' x := norm_apply_of_operator_isometry (C.witness i).val
    (congrArg Subtype.val (C.initial i)) x

theorem fullCopyIsometry_orthogonal :
    OrthogonalFamily ℂ (fun _ : ℕ => H) C.fullCopyIsometry := by
  intro i j hij x y
  have hvi : (C.projection i).val*C.witness i=C.witness i := by
    rw [← C.final,mul_assoc,C.initial,mul_one]
  have hvj : (C.projection j).val*C.witness j=C.witness j := by
    rw [← C.final,mul_assoc,C.initial,mul_one]
  have hvi' : star (C.witness i)*(C.projection i).val=star (C.witness i) := by
    simpa only [star_mul,(C.projection i).property.isSelfAdjoint.star_eq] using congrArg star hvi
  have hc : star (C.witness i)*C.witness j=0 := by
    calc
      _ = (star (C.witness i)*(C.projection i).val)*
          ((C.projection j).val*C.witness j) := by rw [hvi',hvj]
      _ = star (C.witness i)*((C.projection i).val*(C.projection j).val)*C.witness j := by
        simp only [mul_assoc]
      _ = 0 := by rw [C.orthogonal hij,mul_zero,zero_mul]
  change inner ℂ ((C.witness i).val x) ((C.witness j).val y)=0
  rw [← ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ x ((star (C.witness i)*C.witness j).val y)=0
  rw [hc]
  simp

theorem fullCopyIsometry_total :
    ⊤ ≤ (⨆ i, LinearMap.range (C.fullCopyIsometry i).toLinearMap).topologicalClosure := by
  intro x _
  apply (Submodule.isClosed_topologicalClosure _).mem_of_tendsto (C.total x)
  apply Filter.Eventually.of_forall
  intro F
  apply Submodule.sum_mem
  intro i _
  apply Submodule.le_topologicalClosure
  apply (le_iSup (fun j => LinearMap.range (C.fullCopyIsometry j).toLinearMap) i)
  refine ⟨(star (C.witness i)).val x,?_⟩
  change (C.witness i).val ((star (C.witness i)).val x)=(C.projection i).val.val x
  exact congrArg (fun a : Algebra M => a.val x) (C.final i)

theorem fullCopyHilbertSum : IsHilbertSum ℂ (fun _ : ℕ => H) C.fullCopyIsometry :=
  IsHilbertSum.mk C.fullCopyIsometry_orthogonal C.fullCopyIsometry_total

def fullCopyUnitary : CountableHilbertSum H ≃ₗᵢ[ℂ] H :=
  C.fullCopyHilbertSum.linearIsometryEquiv.symm

end CountableProjectionCopies

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularConjugationData
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The modular conjugation data used in preparing a pair

For a cyclic separating vector, Tomita--Takesaki gives `J M J = M′`.
The vector identity `J(r* Ω) = r Ω` is needed only for elements in the
vector-state centralizer. It is not imposed on the whole algebra.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

structure ModularConjugationData (M : VonNeumannAlgebra H) (Ω : H) where
  conjugation : H ≃ₗᵢ⋆[ℂ] H
  involutive : Function.Involutive conjugation
  fixes_vector : conjugation Ω = Ω
  commutant : conjugateRightAlgebra conjugation involutive M = M.commutant
  centralizer_vector : ∀ r : Algebra M,
    (∀ x : Algebra M, inner ℂ Ω ((r.val * x.val) Ω) = inner ℂ Ω ((x.val * r.val) Ω)) →
      conjugationOperator conjugation (star r.val) Ω = r.val Ω

namespace ModularConjugationData

variable {M R : VonNeumannAlgebra H} {Ω : H} (d : ModularConjugationData M Ω)

/-- The full commutant theorem supplies the right inclusion for every
subalgebra, without requiring a trace on the source algebra. -/
theorem right_mem (hRM : R ≤ M) (r : Algebra R) :
    conjugationOperator d.conjugation r.val ∈ M.commutant := by
  change conjugationOperator d.conjugation r.val ∈ (M.commutant : Set (H →L[ℂ] H))
  rw [← d.commutant, conjugateRightAlgebra_coe]
  exact ⟨r.val, hRM r.property, rfl⟩

end ModularConjugationData

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularRightAction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The bounded right action in a modular representation -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H} {Ω : H}

namespace ModularConjugationData

variable (d : ModularConjugationData M Ω)

def rightAction (a : Algebra M) : H →L[ℂ] H :=
  conjugationOperator d.conjugation (star a.val)

end ModularConjugationData

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PointedWordReduction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSignedGroup_finite _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.Generator.MatrixUnitSystem.adaptedBasis_apply _root_.OAI.Generator.MatrixUnitSystem.initialColumn_apply _root_.OAI.Generator.orthonormalMatrixUnits_entry_apply _root_.OAI.KadisonKastler.conjugateMatrixUnits_entry _root_.OAI.KadisonKastler.conjugatedMatrixUnits_entry _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.spatialMatrixUnits_entry _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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

namespace PointedMatrixSites

variable {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {Ω : H} {ν : I → ℝ}

noncomputable def wordOperator (S : PointedMatrixSites M Ω ν) (w : MatrixSiteWord I) : H →L[ℂ] H :=
  MatrixSiteWord.eval S.site w

noncomputable def wordVector (S : PointedMatrixSites M Ω ν) (w : MatrixSiteWord I) : H :=
  S.wordOperator w Ω

@[simp] theorem wordOperator_nil (S : PointedMatrixSites M Ω ν) : S.wordOperator [] = 1 := rfl
@[simp] theorem wordOperator_cons (S : PointedMatrixSites M Ω ν)
    (a : MatrixSiteLetter I) (w : MatrixSiteWord I) :
    S.wordOperator (a :: w) = (S.site a.1).entry a.2.1 a.2.2 * S.wordOperator w := rfl
@[simp] theorem wordOperator_append (S : PointedMatrixSites M Ω ν)
    (w v : MatrixSiteWord I) : S.wordOperator (w ++ v) = S.wordOperator w * S.wordOperator v :=
  MatrixSiteWord.eval_append S.site w v
@[simp] theorem wordOperator_star (S : PointedMatrixSites M Ω ν) (w : MatrixSiteWord I) :
    S.wordOperator (MatrixSiteWord.star w) = star (S.wordOperator w) :=
  MatrixSiteWord.eval_star S.site w
@[simp] theorem wordVector_nil (S : PointedMatrixSites M Ω ν) : S.wordVector [] = Ω := rfl
@[simp] theorem wordVector_cons (S : PointedMatrixSites M Ω ν)
    (a : MatrixSiteLetter I) (w : MatrixSiteWord I) :
    S.wordVector (a :: w) = (S.site a.1).entry a.2.1 a.2.2 (S.wordVector w) := rfl

end PointedMatrixSites

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PointedFiniteBlock
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSignedGroup_finite _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.Generator.MatrixUnitSystem.adaptedBasis_apply _root_.OAI.Generator.MatrixUnitSystem.initialColumn_apply _root_.OAI.Generator.orthonormalMatrixUnits_entry_apply _root_.OAI.KadisonKastler.conjugateMatrixUnits_entry _root_.OAI.KadisonKastler.conjugatedMatrixUnits_entry _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.spatialMatrixUnits_entry _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {Ω : H} {ν : I → ℝ}

namespace PointedMatrixSites

variable (S : PointedMatrixSites M Ω ν)

def blockEntry : (l : List I) → MatrixSiteBlockIndex l → MatrixSiteBlockIndex l →
    (H →L[ℂ] H)
  | [], _, _ => 1
  | i :: l, r, c => (S.site i).entry r.1 c.1 * blockEntry l r.2 c.2

theorem blockEntry_ofFunction (l : List I) (r c : I → Fin 2) :
    S.blockEntry l (matrixSiteBlockIndexOfFunction l r)
      (matrixSiteBlockIndexOfFunction l c) =
      (l.map fun i => (S.site i).entry (r i) (c i)).prod := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [blockEntry, matrixSiteBlockIndexOfFunction,
      List.map_cons, List.prod_cons, ih]

theorem blockEntry_moment (l : List I) (hl : l.Nodup) (r c : MatrixSiteBlockIndex l) :
    inner ℂ Ω (S.blockEntry l r c Ω) = matrixSiteBlockWeight ν l r c := by
  obtain ⟨r, rfl⟩ := matrixSiteBlockIndexOfFunction_surjective l hl r
  obtain ⟨c, rfl⟩ := matrixSiteBlockIndexOfFunction_surjective l hl c
  rw [S.blockEntry_ofFunction, matrixSiteBlockWeight_ofFunction]
  exact S.moments l hl r c

theorem site_commutes_blockEntry (i : I) (a b : Fin 2) (l : List I)
    (hi : i ∉ l) (r c : MatrixSiteBlockIndex l) :
    Commute ((S.site i).entry a b) (S.blockEntry l r c) := by
  induction l with
  | nil => exact Commute.one_right _
  | cons j l ih =>
    exact (S.commuting i j (fun h => hi (by simp [h])) a b r.1 c.1).mul_right
      (ih (fun h => hi (List.mem_cons_of_mem _ h)) r.2 c.2)

theorem blockEntry_star (l : List I) (hl : l.Nodup)
    (r c : MatrixSiteBlockIndex l) : star (S.blockEntry l r c) = S.blockEntry l c r := by
  induction l with
  | nil => simp [blockEntry]
  | cons i l ih =>
    rw [blockEntry, star_mul, ih (List.nodup_cons.mp hl).2, (S.site i).star_entry]
    exact (S.site_commutes_blockEntry i c.1 r.1 l
      (List.nodup_cons.mp hl).1 c.2 r.2).eq.symm

theorem blockEntry_mul (l : List I) (hl : l.Nodup)
    (r c a b : MatrixSiteBlockIndex l) :
    S.blockEntry l r c * S.blockEntry l a b =
      if c = a then S.blockEntry l r b else 0 := by
  induction l with
  | nil => simp [blockEntry, MatrixSiteBlockIndex]
  | cons i l ih =>
    rw [blockEntry, blockEntry,
      (S.site_commutes_blockEntry i a.1 b.1 l
        (List.nodup_cons.mp hl).1 r.2 c.2).symm.mul_mul_mul_comm]
    rw [(S.site i).mul_entry, ih (List.nodup_cons.mp hl).2]
    by_cases h₁ : c.1 = a.1 <;> by_cases h₂ : c.2 = a.2 <;>
      simp [h₁, h₂, Prod.ext_iff, blockEntry]

theorem blockEntry_total (l : List I) :
    ∑ r, S.blockEntry l r r = 1 := by
  induction l with
  | nil => simp [blockEntry, MatrixSiteBlockIndex]
  | cons i l ih =>
    change (∑ r : Fin 2 × MatrixSiteBlockIndex l,
      (S.site i).entry r.1 r.1 * S.blockEntry l r.2 r.2) = 1
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, ih, mul_one, (S.site i).total]

def finiteBlock (l : List I) (hl : l.Nodup) :
    MatrixUnitSystem (MatrixSiteBlockIndex l) (H →L[ℂ] H) where
  entry := S.blockEntry l
  star_entry := S.blockEntry_star l hl
  mul_entry := S.blockEntry_mul l hl
  total := S.blockEntry_total l

theorem finiteBlock_le (l : List I) (hl : l.Nodup) :
    (S.finiteBlock l hl).algebra ≤ M.toStarSubalgebra := by
  apply ((S.finiteBlock l hl).algebra_le_iff _).mpr
  intro r c
  change S.blockEntry l r c ∈ M
  induction l with
  | nil => exact M.one_mem
  | cons i l ih =>
    apply M.mul_mem
    · have he := subset_generatedVonNeumannAlgebra _
        ((le_iSup (fun j => (S.site j).algebra) i) ((S.site i).entry_mem r.1 c.1))
      exact Eq.mpr (congrArg (fun N : VonNeumannAlgebra H =>
        (S.site i).entry r.1 c.1 ∈ N) S.generates) he
    · exact ih (List.nodup_cons.mp hl).2 r.2 c.2

theorem finiteBlock_le_of_sites_le (l : List I) (hl : l.Nodup)
    (T : StarSubalgebra ℂ (H →L[ℂ] H))
    (hT : ∀ i ∈ l, (S.site i).algebra ≤ T) : (S.finiteBlock l hl).algebra ≤ T := by
  apply ((S.finiteBlock l hl).algebra_le_iff _).mpr
  intro r c
  change S.blockEntry l r c ∈ T
  induction l with
  | nil => exact T.one_mem
  | cons i l ih =>
    exact T.mul_mem (hT i (by simp) ((S.site i).entry_mem _ _))
      (ih (List.nodup_cons.mp hl).2 (fun j hj => hT j (List.mem_cons_of_mem _ hj)) r.2 c.2)

theorem site_le_finiteBlock (l : List I) (hl : l.Nodup) (i : I) (hi : i ∈ l) :
    (S.site i).algebra ≤ (S.finiteBlock l hl).algebra := by
  induction l with
  | nil => simp at hi
  | cons j l ih =>
    let E := S.finiteBlock (j :: l) hl
    have htail : (S.finiteBlock l (List.nodup_cons.mp hl).2).algebra ≤ E.algebra := by
      apply ((S.finiteBlock l (List.nodup_cons.mp hl).2).algebra_le_iff _).mpr
      intro a b
      have he : (S.finiteBlock l (List.nodup_cons.mp hl).2).entry a b =
          ∑ r : Fin 2, E.entry (r, a) (r, b) := by
        change S.blockEntry l a b = ∑ r : Fin 2,
          (S.site j).entry r r * S.blockEntry l a b
        rw [← Finset.sum_mul, (S.site j).total, one_mul]
      rw [he]
      exact E.algebra.sum_mem fun r _ => E.entry_mem _ _
    rcases List.mem_cons.mp hi with hij | hi
    · subst i
      apply ((S.site j).algebra_le_iff _).mpr
      intro a b
      have he : (S.site j).entry a b =
          ∑ r : MatrixSiteBlockIndex l, E.entry (a, r) (b, r) := by
        change (S.site j).entry a b = ∑ r : MatrixSiteBlockIndex l,
          (S.site j).entry a b * S.blockEntry l r r
        rw [← Finset.mul_sum, S.blockEntry_total, mul_one]
      rw [he]
      exact E.algebra.sum_mem fun r _ => E.entry_mem _ _
    · exact (ih (List.nodup_cons.mp hl).2 hi).trans htail

theorem finiteBlock_mono {l k : List I} (hl : l.Nodup) (hk : k.Nodup)
    (h : ∀ i ∈ l, i ∈ k) :
    (S.finiteBlock l hl).algebra ≤ (S.finiteBlock k hk).algebra :=
  S.finiteBlock_le_of_sites_le l hl _ (fun i hi => S.site_le_finiteBlock k hk i (h i hi))

theorem finiteBlock_commuting {l k : List I} (h : List.Disjoint l k)
    (r c : MatrixSiteBlockIndex l) (a b : MatrixSiteBlockIndex k) :
    Commute (S.blockEntry l r c) (S.blockEntry k a b) := by
  induction l with
  | nil => exact Commute.one_left _
  | cons i l ih =>
    apply Commute.mul_left
    · exact S.site_commutes_blockEntry i r.1 c.1 k
        (fun hi => (List.disjoint_left.mp h) (by simp) hi) a b
    · exact ih (List.disjoint_left.mpr (fun j hj hk =>
        (List.disjoint_left.mp h) (List.mem_cons_of_mem _ hj) hk)) r.2 c.2

end PointedMatrixSites

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TwoRatioFiniteMatrix
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSignedGroup_finite _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {Ω : H}

namespace PointedMatrixSites

variable (S : PointedMatrixSites M Ω twoRatioSiteParameter)

def twoRatioMatrix (n : ℕ) : MatrixUnitSystem (Fin (twoRatioMatrixSize n)) (H →L[ℂ] H) :=
  (S.finiteBlock (twoRatioFiniteSites n) (twoRatioFiniteSites_nodup n)).reindex
    (Fintype.equivFin (MatrixSiteBlockIndex (twoRatioFiniteSites n))).symm

theorem twoRatioMatrix_algebra (n : ℕ) :
    (S.twoRatioMatrix n).algebra =
      (S.finiteBlock (twoRatioFiniteSites n) (twoRatioFiniteSites_nodup n)).algebra :=
  MatrixUnitSystem.reindex_algebra _ _

theorem twoRatioMatrix_increasing : Monotone (fun n => (S.twoRatioMatrix n).algebra) := by
  intro n m h
  change (S.twoRatioMatrix n).algebra ≤ (S.twoRatioMatrix m).algebra
  rw [S.twoRatioMatrix_algebra, S.twoRatioMatrix_algebra]
  exact S.finiteBlock_mono _ _ (twoRatioFiniteSites_mono h)

theorem twoRatioMatrix_le (n : ℕ) : (S.twoRatioMatrix n).algebra ≤ M.toStarSubalgebra := by
  rw [S.twoRatioMatrix_algebra]
  exact S.finiteBlock_le _ _

theorem twoRatioMatrix_generates :
    generatedVonNeumannAlgebra (⨆ n, (S.twoRatioMatrix n).algebra) = M := by
  apply le_antisymm
  · exact generatedVonNeumannAlgebra_le_of_le _ M (iSup_le S.twoRatioMatrix_le)
  · calc
      M = generatedVonNeumannAlgebra (⨆ i, (S.site i).algebra) := S.generates
      _ ≤ generatedVonNeumannAlgebra (⨆ n, (S.twoRatioMatrix n).algebra) := by
        apply generatedVonNeumannAlgebra_le_of_le _ _
        apply iSup_le
        intro i x hx
        obtain ⟨n, hn⟩ := twoRatioFiniteSites_exhausts i
        have hm : x ∈ (S.twoRatioMatrix n).algebra := by
          rw [S.twoRatioMatrix_algebra]
          exact S.site_le_finiteBlock _ _ i hn hx
        have hle : (S.twoRatioMatrix n).algebra ≤
            ⨆ n, (S.twoRatioMatrix n).algebra :=
          le_iSup (fun n : ℕ => (S.twoRatioMatrix n).algebra) n
        exact subset_generatedVonNeumannAlgebra _ (hle hm)

theorem twoRatioMatrix_local_cyclic : DenseRange
    (fun p : Σ n, (S.twoRatioMatrix n).algebra => (p.2 : H →L[ℂ] H) Ω) := by
  classical
  apply Metric.denseRange_iff.mpr
  intro x ε hε
  obtain ⟨a, ha⟩ := Metric.denseRange_iff.mp S.cyclic x (ε / 2) (by positivity)
  change dist x (a.val Ω) < ε / 2 at ha
  have hax : dist (a.val Ω) x < ε / 2 := by
    simpa only [dist_comm] using ha
  let A : StarSubalgebra ℂ (H →L[ℂ] H) := ⨆ n, (S.twoRatioMatrix n).algebra
  have ham : a.val ∈ Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H))) := by
    rw [← generatedVonNeumannAlgebra_coe, S.twoRatioMatrix_generates]
    exact a.property
  obtain ⟨b, hb⟩ := Generator.bicommutant_finite_strong_approximation A a.val ham
    {Ω} (ε / 2) (by positivity)
  have hbm : b.val ∈ ⋃ n, ((S.twoRatioMatrix n).algebra : Set (H →L[ℂ] H)) := by
    rw [← StarSubalgebra.coe_iSup_of_directed S.twoRatioMatrix_increasing.directed_le]
    exact b.property
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hbm
  refine ⟨⟨n, ⟨b.val, hn⟩⟩, ?_⟩
  have hbΩ : dist (b.val Ω) (a.val Ω) < ε / 2 := by
    simpa only [dist_eq_norm, norm_sub_rev] using hb Ω (Finset.mem_singleton_self _)
  rw [dist_comm]
  change dist (b.val Ω) x < ε
  calc
    dist (b.val Ω) x ≤ dist (b.val Ω) (a.val Ω) + dist (a.val Ω) x := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add hbΩ hax
    _ = ε := by ring

end PointedMatrixSites

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PointedSiteBalance
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSignedGroup_finite _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.Generator.MatrixUnitSystem.adaptedBasis_apply _root_.OAI.Generator.MatrixUnitSystem.initialColumn_apply _root_.OAI.Generator.orthonormalMatrixUnits_entry_apply _root_.OAI.KadisonKastler.conjugateMatrixUnits_entry _root_.OAI.KadisonKastler.conjugatedMatrixUnits_entry _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_twoRatioComplementSites _root_.OAI.KadisonKastler.pointedRawVacuum_apply _root_.OAI.KadisonKastler.spatialMatrixUnits_entry _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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

namespace PointedMatrixSites

variable (S : PointedMatrixSites M Ω ν)

theorem site_balance_blockEntry (i : I) (l : List I) (hl : l.Nodup) (hi : i ∉ l)
    (a b c d : Fin 2) (r s : MatrixSiteBlockIndex l) :
    (twoSiteWeight (ν i) b : ℂ) * productVectorState Ω
        ((S.site i).entry a b * S.blockEntry (i :: l) (c, r) (d, s)) =
      (twoSiteWeight (ν i) a : ℂ) * productVectorState Ω
        (S.blockEntry (i :: l) (c, r) (d, s) * (S.site i).entry a b) := by
  have hm (a b : Fin 2) :
      productVectorState Ω ((S.site i).entry a b * S.blockEntry l r s) =
        (if a = b then (twoSiteWeight (ν i) a : ℂ) else 0) *
          matrixSiteBlockWeight ν l r s :=
    S.blockEntry_moment (i :: l) (List.nodup_cons.mpr ⟨hi, hl⟩) (a, r) (b, s)
  change (twoSiteWeight (ν i) b : ℂ) * productVectorState Ω
      ((S.site i).entry a b * ((S.site i).entry c d * S.blockEntry l r s)) =
    (twoSiteWeight (ν i) a : ℂ) * productVectorState Ω
      (((S.site i).entry c d * S.blockEntry l r s) * (S.site i).entry a b)
  rw [← mul_assoc, mul_assoc ((S.site i).entry c d),
    ← (S.site_commutes_blockEntry i a b l hi r s).eq, ← mul_assoc]
  rw [(S.site i).mul_entry, (S.site i).mul_entry]
  have hz : productVectorState Ω (0 : H →L[ℂ] H) = 0 := by
    simp [productVectorState]
  by_cases hbc : b = c <;> by_cases hda : d = a
  · subst c; subst d
    simp only [ite_true, if_true, hm]
    ring
  · simp [hbc, hda, hz, hm, Ne.symm hda]
  · simp [hbc, hda, hz, hm, Ne.symm hbc]
  · simp [hbc, hda, hz]

theorem site_balance_finiteBlock (i : I) (l : List I) (hl : l.Nodup) (hi : i ∉ l)
    (a b : Fin 2) (x : H →L[ℂ] H)
    (hx : x ∈ (S.finiteBlock (i :: l) (List.nodup_cons.mpr ⟨hi, hl⟩)).algebra) :
    (twoSiteWeight (ν i) b : ℂ) * productVectorState Ω ((S.site i).entry a b * x) =
      (twoSiteWeight (ν i) a : ℂ) * productVectorState Ω (x * (S.site i).entry a b) := by
  classical
  let E := S.finiteBlock (i :: l) (List.nodup_cons.mpr ⟨hi, hl⟩)
  obtain ⟨v, rfl⟩ := (E.mem_algebra x).mp hx
  let φ := productVectorLinear Ω
  have he (r s : MatrixSiteBlockIndex (i :: l)) :
      (twoSiteWeight (ν i) b : ℂ) * φ ((S.site i).entry a b * E.entry r s) =
        (twoSiteWeight (ν i) a : ℂ) * φ (E.entry r s * (S.site i).entry a b) :=
    S.site_balance_blockEntry i l hl hi a b r.1 s.1 r.2 s.2
  change (twoSiteWeight (ν i) b : ℂ) * φ ((S.site i).entry a b * _) =
    (twoSiteWeight (ν i) a : ℂ) * φ (_ * (S.site i).entry a b)
  simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc,
    map_sum, map_smul, smul_eq_mul]
  simp_rw [← mul_assoc, mul_comm (twoSiteWeight (ν i) b : ℂ), mul_assoc,
    he, ← mul_assoc]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro s hs
  ring

/-- The weighted site identity holds against every operator in the product algebra. -/
theorem twoRatio_site_balance (T : PointedMatrixSites M Ω twoRatioSiteParameter)
    (i : TwoRatioSite) (a b : Fin 2) (x : H →L[ℂ] H) (hx : x ∈ M) :
    (twoSiteWeight (twoRatioSiteParameter i) b : ℂ) *
        productVectorState Ω ((T.site i).entry a b * x) =
      (twoSiteWeight (twoRatioSiteParameter i) a : ℂ) *
        productVectorState Ω (x * (T.site i).entry a b) := by
  classical
  rw [← T.twoRatioMatrix_generates] at hx
  apply weighted_productState_generated _ Ω ((T.site i).entry a b) _ _ ?_ x hx
  intro y hy
  have hym : y ∈ ⋃ n, ((T.twoRatioMatrix n).algebra : Set (H →L[ℂ] H)) := by
    rw [← StarSubalgebra.coe_iSup_of_directed T.twoRatioMatrix_increasing.directed_le]
    exact hy
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hym
  let l := (twoRatioFiniteSites n).filter (fun j => decide (j ≠ i))
  have hl : l.Nodup := (twoRatioFiniteSites_nodup n).filter _
  have hi : i ∉ l := by simp [l]
  apply T.site_balance_finiteBlock i l hl hi a b y
  have hle : (T.twoRatioMatrix n).algebra ≤
      (T.finiteBlock (i :: l) (List.nodup_cons.mpr ⟨hi, hl⟩)).algebra := by
    rw [T.twoRatioMatrix_algebra]
    apply T.finiteBlock_mono
    intro j hj
    by_cases hji : j = i
    · simp [hji]
    · apply List.mem_cons_of_mem i
      simpa [l] using And.intro hj hji
  exact hle hn

end PointedMatrixSites

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularSiteEigen
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

namespace PointedMatrixSites

theorem twoRatio_site_algebra_le
    (S : PointedMatrixSites M Ω twoRatioSiteParameter) (i : TwoRatioSite) :
    (S.site i).algebra ≤ M.toStarSubalgebra := by
  intro x hx
  have hmem : x ∈ ⨆ j, (S.site j).algebra :=
    (le_iSup (fun j => (S.site j).algebra) i) hx
  exact Eq.mpr (congrArg (fun N : VonNeumannAlgebra H => x ∈ N) S.generates)
    (subset_generatedVonNeumannAlgebra _ hmem)

end PointedMatrixSites

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PointedWordMoments
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSignedGroup_finite _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.Generator.MatrixUnitSystem.adaptedBasis_apply _root_.OAI.Generator.MatrixUnitSystem.initialColumn_apply _root_.OAI.Generator.orthonormalMatrixUnits_entry_apply _root_.OAI.KadisonKastler.conjugateMatrixUnits_entry _root_.OAI.KadisonKastler.conjugatedMatrixUnits_entry _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.spatialMatrixUnits_entry _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Vacuum moments of arbitrary matrix-site words

Distinct-site product moments determine repeated words as well. The
algebraic reduction is shared across representations and site reindexings.
-/

namespace KadisonKastler

noncomputable section

namespace MatrixSiteWord

variable {I J : Type*}

def letterAt (w : MatrixSiteWord I) (i : I) : MatrixSiteLetter I := by
  classical
  exact if h : ∃ a ∈ w, a.1 = i then Classical.choose h else (i, 0, 0)

theorem letterAt_eq (w : MatrixSiteWord I) (hw : (indices w).Nodup)
    (a : MatrixSiteLetter I) (ha : a ∈ w) : letterAt w a.1 = a := by
  classical
  have hex : ∃ b ∈ w, b.1 = a.1 := ⟨a, ha, rfl⟩
  simp only [letterAt, dite_eq_left hex]
  have hb := Classical.choose_spec hex
  exact List.inj_on_of_nodup_map hw hb.1 ha hb.2

def weight (ν : I → ℝ) (w : MatrixSiteWord I) : ℂ :=
  (w.map fun a => if a.2.1 = a.2.2 then (twoSiteWeight (ν a.1) a.2.1 : ℂ) else 0).prod

theorem weight_reindex (ν : I → ℝ) (η : J → ℝ) (e : I ≃ J)
    (h : ∀ i, η (e i) = ν i) (w : MatrixSiteWord I) :
    weight η (reindex e w) = weight ν w := by
  simp only [weight, reindex, List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro a ha
  simp only [h]

theorem indices_reindex (e : I ≃ J) (w : MatrixSiteWord I) :
    indices (reindex e w) = (indices w).map e := by
  simp only [indices, reindex, List.map_map, Function.comp_def]

theorem nodup_indices_reindex (e : I ≃ J) (w : MatrixSiteWord I)
    (h : (indices w).Nodup) : (indices (reindex e w)).Nodup := by
  rw [indices_reindex]
  exact h.map e.injective

end MatrixSiteWord

namespace PointedMatrixSites

variable {H K I J : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}
variable {Ω : H} {ξ : K} {ν : I → ℝ} {η : J → ℝ}

/-- The finite-site moment axiom applied to a word with distinct indices. -/
theorem word_moment_of_nodup (S : PointedMatrixSites M Ω ν)
    (w : MatrixSiteWord I) (hw : (MatrixSiteWord.indices w).Nodup) :
    inner ℂ Ω (S.wordVector w) = MatrixSiteWord.weight ν w := by
  classical
  let r : I → Fin 2 := fun i => (MatrixSiteWord.letterAt w i).2.1
  let c : I → Fin 2 := fun i => (MatrixSiteWord.letterAt w i).2.2
  have heval : ((MatrixSiteWord.indices w).map
      (fun i => (S.site i).entry (r i) (c i))).prod = S.wordOperator w := by
    unfold MatrixSiteWord.indices wordOperator MatrixSiteWord.eval
    rw [List.map_map]
    congr 1
    apply List.map_congr_left
    intro a ha
    simp only [Function.comp_apply, r, c, MatrixSiteWord.letterAt_eq w hw a ha]
  have hweight : ((MatrixSiteWord.indices w).map
      (fun i => if r i = c i then (twoSiteWeight (ν i) (r i) : ℂ) else 0)).prod =
      MatrixSiteWord.weight ν w := by
    unfold MatrixSiteWord.indices MatrixSiteWord.weight
    rw [List.map_map]
    congr 1
    apply List.map_congr_left
    intro a ha
    simp only [Function.comp_apply, r, c, MatrixSiteWord.letterAt_eq w hw a ha]
  have h := S.moments (MatrixSiteWord.indices w) hw r c
  rw [heval, hweight] at h
  exact h

/-- All vacuum word moments agree after a weight-preserving site bijection,
including words that visit the same site repeatedly. -/
theorem word_moment_eq_of_reindex (S : PointedMatrixSites M Ω ν)
    (T : PointedMatrixSites N ξ η) (e : I ≃ J) (hweight : ∀ i, η (e i) = ν i)
    (w : MatrixSiteWord I) :
    inner ℂ Ω (S.wordVector w) = inner ℂ ξ (T.wordVector (MatrixSiteWord.reindex e w)) := by
  classical
  have hT : ∀ i j, i ≠ j → ∀ a b c d,
      Commute ((T.site (e i)).entry a b) ((T.site (e j)).entry c d) := by
    intro i j hij
    exact T.commuting (e i) (e j) (fun h => hij (e.injective h))
  have hS := MatrixSiteWord.evalOption_reduce S.site S.commuting w
  have hT' := MatrixSiteWord.evalOption_reduce (T.site ∘ e) hT w
  cases hred : MatrixSiteWord.reduce w with
  | none =>
    simp only [hred, MatrixSiteWord.evalOption, Option.elim_none] at hS hT'
    change inner ℂ Ω (MatrixSiteWord.eval S.site w Ω) =
      inner ℂ ξ (MatrixSiteWord.eval T.site (MatrixSiteWord.reindex e w) ξ)
    rw [MatrixSiteWord.eval_reindex, ← hS, ← hT']
    simp
  | some v =>
    simp only [hred, MatrixSiteWord.evalOption, Option.elim_some] at hS hT'
    have hv := MatrixSiteWord.indices_reduce_nodup w v hred
    have hs : S.wordVector w = S.wordVector v := congrArg (fun a : H →L[ℂ] H => a Ω) hS.symm
    have ht : T.wordVector (MatrixSiteWord.reindex e w) =
        T.wordVector (MatrixSiteWord.reindex e v) := by
      change MatrixSiteWord.eval T.site (MatrixSiteWord.reindex e w) ξ =
        MatrixSiteWord.eval T.site (MatrixSiteWord.reindex e v) ξ
      rw [MatrixSiteWord.eval_reindex, MatrixSiteWord.eval_reindex, hT']
    rw [hs, ht, S.word_moment_of_nodup v hv,
      T.word_moment_of_nodup _ (MatrixSiteWord.nodup_indices_reindex e v hv),
      MatrixSiteWord.weight_reindex ν η e hweight]

/-- The shared word Gram matrix is determined by the product moments. -/
theorem word_inner_eq_of_reindex (S : PointedMatrixSites M Ω ν)
    (T : PointedMatrixSites N ξ η) (e : I ≃ J) (hweight : ∀ i, η (e i) = ν i)
    (w v : MatrixSiteWord I) :
    inner ℂ (S.wordVector w) (S.wordVector v) =
      inner ℂ (T.wordVector (MatrixSiteWord.reindex e w))
        (T.wordVector (MatrixSiteWord.reindex e v)) := by
  have hs : inner ℂ (S.wordVector w) (S.wordVector v) =
      inner ℂ Ω (S.wordVector (MatrixSiteWord.star w ++ v)) := by
    change inner ℂ (S.wordOperator w Ω) (S.wordOperator v Ω) = _
    rw [← ContinuousLinearMap.adjoint_inner_right]
    simp only [wordVector, wordOperator_append, wordOperator_star,
      ContinuousLinearMap.star_eq_adjoint, mul_apply_eq_comp]
  have ht : inner ℂ (T.wordVector (MatrixSiteWord.reindex e w))
      (T.wordVector (MatrixSiteWord.reindex e v)) =
      inner ℂ ξ (T.wordVector (MatrixSiteWord.reindex e (MatrixSiteWord.star w ++ v))) := by
    have he : MatrixSiteWord.reindex e (MatrixSiteWord.star w ++ v) =
        MatrixSiteWord.star (MatrixSiteWord.reindex e w) ++ MatrixSiteWord.reindex e v := by
      simp only [MatrixSiteWord.reindex, MatrixSiteWord.star, List.map_append,
        List.map_reverse, List.map_map, Function.comp_def]
    rw [he]
    change inner ℂ (T.wordOperator (MatrixSiteWord.reindex e w) ξ)
      (T.wordOperator (MatrixSiteWord.reindex e v) ξ) = _
    rw [← ContinuousLinearMap.adjoint_inner_right]
    simp only [wordVector, wordOperator_append, wordOperator_star,
      ContinuousLinearMap.star_eq_adjoint, mul_apply_eq_comp]
  rw [hs, ht]
  exact S.word_moment_eq_of_reindex T e hweight _

end PointedMatrixSites

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PointedBlockMoments
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSignedGroup_finite _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Product moments for disjoint finite matrix blocks -/

namespace KadisonKastler

noncomputable section

variable {I : Type*}

def matrixSiteBlockWord : (l : List I) →
    MatrixSiteBlockIndex l → MatrixSiteBlockIndex l → MatrixSiteWord I
  | [], _, _ => []
  | i :: l, r, c => (i, r.1, c.1) :: matrixSiteBlockWord l r.2 c.2

theorem matrixSiteBlockWord_indices (l : List I) (r c : MatrixSiteBlockIndex l) :
    MatrixSiteWord.indices (matrixSiteBlockWord l r c) = l := by
  induction l with
  | nil => rfl
  | cons i l ih => exact congrArg (List.cons i) (ih r.2 c.2)

theorem matrixSiteBlockWord_weight (ν : I → ℝ) (l : List I)
    (r c : MatrixSiteBlockIndex l) :
    MatrixSiteWord.weight ν (matrixSiteBlockWord l r c) = matrixSiteBlockWeight ν l r c := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change _ * MatrixSiteWord.weight ν (matrixSiteBlockWord l r.2 c.2) = _
    rw [ih]
    rfl

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {Ω : H} {ν : I → ℝ}

namespace PointedMatrixSites

variable (S : PointedMatrixSites M Ω ν)

theorem wordWeight_append (w v : MatrixSiteWord I) :
    MatrixSiteWord.weight ν (w ++ v) =
      MatrixSiteWord.weight ν w * MatrixSiteWord.weight ν v := by
  simp only [MatrixSiteWord.weight, List.map_append, List.prod_append]

theorem blockWord_eval (l : List I) (r c : MatrixSiteBlockIndex l) :
    MatrixSiteWord.eval S.site (matrixSiteBlockWord l r c) = S.blockEntry l r c := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change (S.site i).entry r.1 c.1 *
      MatrixSiteWord.eval S.site (matrixSiteBlockWord l r.2 c.2) =
      (S.site i).entry r.1 c.1 * S.blockEntry l r.2 c.2
    exact congrArg ((S.site i).entry r.1 c.1 * ·) (ih r.2 c.2)

theorem disjoint_blockEntry_moment {l k : List I} (hl : l.Nodup) (hk : k.Nodup)
    (hd : List.Disjoint l k) (r c : MatrixSiteBlockIndex l) (a b : MatrixSiteBlockIndex k) :
    productVectorState Ω (S.blockEntry l r c * S.blockEntry k a b) =
      matrixSiteBlockWeight ν l r c * matrixSiteBlockWeight ν k a b := by
  have hnodup : (MatrixSiteWord.indices
      (matrixSiteBlockWord l r c ++ matrixSiteBlockWord k a b)).Nodup := by
    simp only [MatrixSiteWord.indices, List.map_append]
    change (MatrixSiteWord.indices (matrixSiteBlockWord l r c) ++
      MatrixSiteWord.indices (matrixSiteBlockWord k a b)).Nodup
    rw [matrixSiteBlockWord_indices, matrixSiteBlockWord_indices]
    exact List.nodup_append'.mpr ⟨hl, hk, hd⟩
  have hm := S.word_moment_of_nodup
    (matrixSiteBlockWord l r c ++ matrixSiteBlockWord k a b) hnodup
  change productVectorState Ω (MatrixSiteWord.eval S.site
    (matrixSiteBlockWord l r c ++ matrixSiteBlockWord k a b)) = _ at hm
  rw [MatrixSiteWord.eval_append, S.blockWord_eval, S.blockWord_eval] at hm
  rw [wordWeight_append, matrixSiteBlockWord_weight, matrixSiteBlockWord_weight] at hm
  exact hm

theorem disjoint_block_algebra_independent {l k : List I} (hl : l.Nodup) (hk : k.Nodup)
    (hd : List.Disjoint l k) (r c : MatrixSiteBlockIndex l)
    (b : (S.finiteBlock k hk).algebra) :
    productVectorState Ω (S.blockEntry l r c * b.val) =
      productVectorState Ω (S.blockEntry l r c) * productVectorState Ω b.val := by
  obtain ⟨a, ha⟩ := ((S.finiteBlock k hk).mem_algebra b.val).mp b.property
  let φ := productVectorLinear Ω
  have he (i j : MatrixSiteBlockIndex k) :
      φ (S.blockEntry l r c * S.blockEntry k i j) =
        φ (S.blockEntry l r c) * φ (S.blockEntry k i j) := by
    change productVectorState Ω (S.blockEntry l r c * S.blockEntry k i j) =
      productVectorState Ω (S.blockEntry l r c) * productVectorState Ω (S.blockEntry k i j)
    rw [S.disjoint_blockEntry_moment hl hk hd]
    exact congrArg₂ (· * ·) (S.blockEntry_moment l hl r c).symm
      (S.blockEntry_moment k hk i j).symm
  change φ (S.blockEntry l r c * b.val) = φ (S.blockEntry l r c) * φ b.val
  rw [← ha]
  change φ (S.blockEntry l r c *
    ∑ i, ∑ j, a i j • S.blockEntry k i j) =
    φ (S.blockEntry l r c) * φ (∑ i, ∑ j, a i j • S.blockEntry k i j)
  simp only [Finset.mul_sum, mul_smul_comm, map_sum, map_smul, he, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem disjoint_three_blockEntry_moment {l k m : List I}
    (hl : l.Nodup) (hk : k.Nodup) (hm : m.Nodup)
    (hlk : List.Disjoint l k) (hlm : List.Disjoint l m) (hkm : List.Disjoint k m)
    (r c : MatrixSiteBlockIndex l) (a b : MatrixSiteBlockIndex k)
    (d e : MatrixSiteBlockIndex m) :
    productVectorState Ω ((S.blockEntry l r c * S.blockEntry k a b) *
      S.blockEntry m d e) = matrixSiteBlockWeight ν l r c *
        matrixSiteBlockWeight ν k a b * matrixSiteBlockWeight ν m d e := by
  have hdisj : List.Disjoint (l ++ k) m := by
    apply List.disjoint_left.mpr
    intro i hi him
    rcases List.mem_append.mp hi with hi | hi
    · exact List.disjoint_left.mp hlm hi him
    · exact List.disjoint_left.mp hkm hi him
  have hnodup : (MatrixSiteWord.indices
      ((matrixSiteBlockWord l r c ++ matrixSiteBlockWord k a b) ++
        matrixSiteBlockWord m d e)).Nodup := by
    simp only [MatrixSiteWord.indices, List.map_append]
    change ((MatrixSiteWord.indices (matrixSiteBlockWord l r c) ++
      MatrixSiteWord.indices (matrixSiteBlockWord k a b)) ++
      MatrixSiteWord.indices (matrixSiteBlockWord m d e)).Nodup
    rw [matrixSiteBlockWord_indices, matrixSiteBlockWord_indices, matrixSiteBlockWord_indices]
    exact (hl.append hk hlk).append hm hdisj
  have h := S.word_moment_of_nodup
    ((matrixSiteBlockWord l r c ++ matrixSiteBlockWord k a b) ++
      matrixSiteBlockWord m d e) hnodup
  change productVectorState Ω (MatrixSiteWord.eval S.site
    ((matrixSiteBlockWord l r c ++ matrixSiteBlockWord k a b) ++
      matrixSiteBlockWord m d e)) = _ at h
  rw [MatrixSiteWord.eval_append, MatrixSiteWord.eval_append,
    S.blockWord_eval, S.blockWord_eval, S.blockWord_eval] at h
  rw [wordWeight_append, wordWeight_append, matrixSiteBlockWord_weight,
    matrixSiteBlockWord_weight, matrixSiteBlockWord_weight] at h
  exact h

end PointedMatrixSites

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PointedCyclicEquivalence
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSignedGroup_finite _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.Generator.MatrixUnitSystem.adaptedBasis_apply _root_.OAI.Generator.MatrixUnitSystem.initialColumn_apply _root_.OAI.Generator.orthonormalMatrixUnits_entry_apply _root_.OAI.KadisonKastler.conjugateMatrixUnits_entry _root_.OAI.KadisonKastler.conjugatedMatrixUnits_entry _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.spatialMatrixUnits_entry _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Unitary reindexing of pointed matrix products

Matching finite-site moments identify the dense spans of all word
vectors. The resulting Hilbert isometry intertwines every site and
therefore the concrete von Neumann algebras they generate.
-/

namespace KadisonKastler

noncomputable section

namespace PointedMatrixSites

variable {I J H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}
  {Ω : H} {ξ : K} {ν : I → ℝ} {η : J → ℝ}

def siteGenerator (S : PointedMatrixSites M Ω ν) (a : MatrixSiteLetter I) : H →L[ℂ] H :=
  (S.site a.1).entry a.2.1 a.2.2

theorem generates_siteGenerator (S : PointedMatrixSites M Ω ν) :
    M = generatedVonNeumannAlgebra (StarAlgebra.adjoin ℂ (Set.range S.siteGenerator)) := by
  apply S.generates.trans
  apply congrArg generatedVonNeumannAlgebra
  apply le_antisymm
  · apply iSup_le
    intro i
    apply ((S.site i).algebra_le_iff _).mpr
    intro a b
    exact StarAlgebra.subset_adjoin ℂ _ ⟨(i, a, b), rfl⟩
  · apply StarAlgebra.adjoin_le
    rintro _ ⟨⟨i, a, b⟩, rfl⟩
    exact (le_iSup (fun i => (S.site i).algebra) i) ((S.site i).entry_mem a b)

/-- All finite word vectors have dense linear span. -/
theorem wordSpan_dense (S : PointedMatrixSites M Ω ν) :
    DenseRange (Finsupp.linearCombination ℂ S.wordVector) := by
  apply denseRange_linearCombination_of_cyclic_generators M Ω S.siteGenerator S.wordVector
    S.generates_siteGenerator S.cyclic
  · rintro ⟨i, a, b⟩
    exact ⟨(i, b, a), (S.site i).star_entry a b |>.symm⟩
  · exact ⟨Finsupp.single [] 1, by simp⟩
  · intro a w
    exact ⟨Finsupp.single (a :: w) 1, by simp [siteGenerator]⟩

theorem reindex_symm (e : I ≃ J) (w : MatrixSiteWord J) :
    MatrixSiteWord.reindex e (MatrixSiteWord.reindex e.symm w) = w := by
  simp only [MatrixSiteWord.reindex, List.map_map, Function.comp_def, e.apply_symm_apply]
  change w.map id = w
  exact List.map_id w

theorem reindexed_wordSpan_dense (T : PointedMatrixSites N ξ η) (e : I ≃ J) :
    DenseRange (Finsupp.linearCombination ℂ
      (fun w : MatrixSiteWord I => T.wordVector (MatrixSiteWord.reindex e w))) := by
  have hr : Set.range (fun w : MatrixSiteWord I =>
      T.wordVector (MatrixSiteWord.reindex e w)) = Set.range T.wordVector := by
    ext x
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨MatrixSiteWord.reindex e w, rfl⟩
    · rintro ⟨w, rfl⟩
      exact ⟨MatrixSiteWord.reindex e.symm w, by dsimp only; rw [reindex_symm]⟩
  change Dense ((LinearMap.range (Finsupp.linearCombination ℂ
    (fun w : MatrixSiteWord I => T.wordVector (MatrixSiteWord.reindex e w)))) : Set K)
  rw [Finsupp.range_linearCombination, hr, ← Finsupp.range_linearCombination]
  exact T.wordSpan_dense

/-- The actual Hilbert-space equivalence determined by all finite words. -/
def reindexEquivalence (S : PointedMatrixSites M Ω ν) (T : PointedMatrixSites N ξ η)
    (e : I ≃ J) (hweight : ∀ i, η (e i) = ν i) : H ≃ₗᵢ[ℂ] K :=
  cyclicGramEquivalence S.wordVector
    (fun w => T.wordVector (MatrixSiteWord.reindex e w))
    S.wordSpan_dense (reindexed_wordSpan_dense T e)
    (S.word_inner_eq_of_reindex T e hweight)

@[simp] theorem reindexEquivalence_word (S : PointedMatrixSites M Ω ν)
    (T : PointedMatrixSites N ξ η) (e : I ≃ J) (hweight : ∀ i, η (e i) = ν i)
    (w : MatrixSiteWord I) :
    S.reindexEquivalence T e hweight (S.wordVector w) =
      T.wordVector (MatrixSiteWord.reindex e w) :=
  cyclicGramEquivalence_apply _ _ _ _ _ w

theorem reindexEquivalence_intertwines (S : PointedMatrixSites M Ω ν)
    (T : PointedMatrixSites N ξ η) (e : I ≃ J) (hweight : ∀ i, η (e i) = ν i)
    (i : I) (a b : Fin 2) (x : H) :
    S.reindexEquivalence T e hweight ((S.site i).entry a b x) =
      (T.site (e i)).entry a b (S.reindexEquivalence T e hweight x) := by
  let U := S.reindexEquivalence T e hweight
  apply S.wordSpan_dense.induction_on (p := fun y =>
    U ((S.site i).entry a b y) = (T.site (e i)).entry a b (U y)) x
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro c
    have hmap : U (Finsupp.linearCombination ℂ S.wordVector c) =
        Finsupp.linearCombination ℂ
          (fun w => T.wordVector (MatrixSiteWord.reindex e w)) c :=
      cyclicGramEquivalence_linearCombination _ _ _ _ _ c
    rw [hmap]
    simp only [Finsupp.linearCombination_apply, map_finsuppSum, map_smul]
    apply Finsupp.sum_congr
    intro w hw
    congr 1
    change U ((S.site i).entry a b (S.wordVector w)) = _
    rw [← S.wordVector_cons (i, a, b) w]
    change S.reindexEquivalence T e hweight (S.wordVector ((i, a, b) :: w)) = _
    rw [reindexEquivalence_word]
    rfl

theorem reindexEquivalence_conjugate_site (S : PointedMatrixSites M Ω ν)
    (T : PointedMatrixSites N ξ η) (e : I ≃ J) (hweight : ∀ i, η (e i) = ν i)
    (i : I) (a b : Fin 2) :
    (S.reindexEquivalence T e hweight).conjStarAlgEquiv ((S.site i).entry a b) =
      (T.site (e i)).entry a b := by
  ext y
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, reindexEquivalence_intertwines,
    LinearIsometryEquiv.apply_symm_apply]

/-- The finite-word Hilbert equivalence transports the generated algebras. -/
theorem reindexEquivalence_algebra (S : PointedMatrixSites M Ω ν)
    (T : PointedMatrixSites N ξ η) (e : I ≃ J) (hweight : ∀ i, η (e i) = ν i) :
    spatialTransportAlgebra (S.reindexEquivalence T e hweight) M = N := by
  let U := S.reindexEquivalence T e hweight
  have hr : U.conjStarAlgEquiv '' Set.range S.siteGenerator = Set.range T.siteGenerator := by
    ext x
    constructor
    · rintro ⟨_, ⟨⟨i, a, b⟩, rfl⟩, rfl⟩
      exact ⟨(e i, a, b), (S.reindexEquivalence_conjugate_site T e hweight i a b).symm⟩
    · rintro ⟨⟨j, a, b⟩, rfl⟩
      refine ⟨S.siteGenerator (e.symm j, a, b), ⟨(e.symm j, a, b), rfl⟩, ?_⟩
      simpa only [U, siteGenerator, e.apply_symm_apply] using
        S.reindexEquivalence_conjugate_site T e hweight (e.symm j) a b
  change spatialTransportAlgebra U M = N
  calc
    spatialTransportAlgebra U M = spatialTransportAlgebra U
        (generatedVonNeumannAlgebra (StarAlgebra.adjoin ℂ (Set.range S.siteGenerator))) :=
      congrArg (spatialTransportAlgebra U) S.generates_siteGenerator
    _ = generatedVonNeumannAlgebra
        ((StarAlgebra.adjoin ℂ (Set.range S.siteGenerator)).map U.conjStarAlgEquiv.toStarAlgHom) :=
      spatialTransport_generated U _
    _ = generatedVonNeumannAlgebra (StarAlgebra.adjoin ℂ (Set.range T.siteGenerator)) := by
      rw [StarAlgHom.map_adjoin]
      exact congrArg (fun s => generatedVonNeumannAlgebra (StarAlgebra.adjoin ℂ s)) hr
    _ = N := T.generates_siteGenerator.symm

end PointedMatrixSites

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TypeIFactorStability
attribute [-instance] _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The type I branch and the projection dichotomy

The diffuse predicate is exactly the projection clause of
`Generator.IsII1Factor` and `TypeIIInfinityFactor`. Its alternative, for
a scalar-center algebra, is the existence of a minimal projection. This
dichotomy is proved directly. The separable type I branch uses the constructed
finite-group embedding.
-/

namespace KadisonKastler

open Generator.Tracial

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The diffuseness condition, independent of a finite
or semifinite factor structure. -/
def ProjectionDiffuse (M : VonNeumannAlgebra H) : Prop :=
  ∀ p : Algebra M, IsStarProjection p → p ≠ 0 →
    ∃ q : Algebra M, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PointedMatrixSum
attribute [-instance] _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
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

variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

namespace PointedMatrixSites

variable {I J : Type*} {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}
  {Ω : H} {ξ : K} {ν : I → ℝ} {η : J → ℝ}

/-- The actual site family on the two tensor legs. -/
def sumSite (S : PointedMatrixSites M Ω ν) (T : PointedMatrixSites N ξ η) :
    I ⊕ J → MatrixUnitSystem (Fin 2) (SpatialHilbert H K →L[ℂ] SpatialHilbert H K) :=
  Sum.elim (fun i => (S.site i).map (spatialLeft (K := K)))
    (fun j => (T.site j).map (spatialRight (H := H)))

end PointedMatrixSites

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PointedSitesTransport
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSignedGroup_finite _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.CommonTracialPositionData.rightEquiv_transportEquiv _root_.OAI.KadisonKastler.FiniteInnerAverage.algebraApply_sub _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.StandardTracialPosition.conjugation_algebraVector _root_.OAI.KadisonKastler.StandardTracialPosition.diagonalRepresentation_vector _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.concreteDerivation_apply _root_.OAI.KadisonKastler.concreteDiagonalSequenceUnitary_coe _root_.OAI.KadisonKastler.concreteDiagonalSequence_apply _root_.OAI.KadisonKastler.concreteDiagonalUnitary_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.matrixLiftUnitaryAt_coe _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.minimalCyclicRetraction_compression _root_.OAI.KadisonKastler.productBoundaryRepresentation_coe _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.rescaledGraphMap_apply _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.typeICyclicHom_apply _root_.OAI.KadisonKastler.typeICyclicOperator_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply _root_.OAI.KadisonSimilarity.predualRestriction_apply _root_.OAI.NaimarkZFC.gns_apply_coe
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

@[simp] theorem spatialTransportEquiv_vector (e : H ≃ₗᵢ[ℂ] K)
    (M : VonNeumannAlgebra H) (Ω : H) (a : Algebra M) :
    algebraVectorMap (spatialTransportAlgebra e M) (e Ω) (spatialTransportEquiv e M a) =
      e (algebraVectorMap M Ω a) := by
  change e.conjStarAlgEquiv a.val (e Ω) = e (a.val Ω)
  simp only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.symm_apply_apply]

namespace PointedMatrixSites

variable {I : Type*} {M : VonNeumannAlgebra H} {Ω : H} {ν : I → ℝ}

/-- All concrete pointed-product data survive spatial transport. -/
def transport (S : PointedMatrixSites M Ω ν) (e : H ≃ₗᵢ[ℂ] K) :
    PointedMatrixSites (spatialTransportAlgebra e M) (e Ω) ν where
  valid := S.valid
  site i := (S.site i).map e.conjStarAlgEquiv.toStarAlgHom
  commuting i j hij a b c d :=
    (S.commuting i j hij a b c d).map e.conjStarAlgEquiv.toMonoidHom
  generates := by
    calc
      spatialTransportAlgebra e M = spatialTransportAlgebra e
          (generatedVonNeumannAlgebra (⨆ i, (S.site i).algebra)) :=
        congrArg (spatialTransportAlgebra e) S.generates
      _ = _ := by
        rw [spatialTransport_generated]
        congr 1
        rw [(StarSubalgebra.gc_map_comap e.conjStarAlgEquiv.toStarAlgHom).l_iSup]
        congr 1
        funext i
        exact matrixUnit_algebra_map (S.site i) _
  unit_vector := by rw [e.norm_map, S.unit_vector]
  cyclic := by
    apply Dense.mono _ (e.surjective.denseRange.comp S.cyclic e.continuous)
    rintro _ ⟨a,rfl⟩
    exact ⟨spatialTransportEquiv e M a, spatialTransportEquiv_vector e M Ω a⟩
  separating := by
    intro a b hab
    obtain ⟨a',rfl⟩ := (spatialTransportEquiv e M).surjective a
    obtain ⟨b',rfl⟩ := (spatialTransportEquiv e M).surjective b
    change algebraVectorMap _ _ (spatialTransportEquiv e M a') =
      algebraVectorMap _ _ (spatialTransportEquiv e M b') at hab
    rw [spatialTransportEquiv_vector, spatialTransportEquiv_vector] at hab
    exact congrArg (spatialTransportEquiv e M) (S.separating (e.injective hab))
  moments l hl r c := by
    have hp : (l.map fun i =>
        ((S.site i).map e.conjStarAlgEquiv.toStarAlgHom).entry (r i) (c i)).prod =
        e.conjStarAlgEquiv ((l.map fun i => (S.site i).entry (r i) (c i)).prod) := by
      simp only [map_list_prod, List.map_map]
      rfl
    rw [hp, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
      e.symm_apply_apply, e.inner_map_map]
    exact S.moments l hl r c

end PointedMatrixSites

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PointedProductLift
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Universe lift of a concrete pointed product

The construction takes place in a separable Hilbert space in `Type`.
Spatial transport along `ULift` gives the same concrete product data in
any ambient universe required by the stability theorem.
-/

namespace KadisonKastler

open UnitalTomsWinter

noncomputable section

universe u

/-- Raise the universe without changing any product-state data. -/
def PointedMatrixProduct.universeLift {I : Type} {ν : I → ℝ}
    (P : PointedMatrixProduct.{0} ν) : PointedMatrixProduct.{u} ν := by
  letI : InnerProductSpace ℂ (ULift.{u} P.K) :=
    InnerProductSpace.induced (LinearIsometryEquiv.ulift ℂ P.K).toLinearMap
  let e : P.K ≃ₗᵢ[ℂ] ULift.{u} P.K := (LinearIsometryEquiv.ulift ℂ P.K).symm
  letI : TopologicalSpace.SeparableSpace (ULift.{u} P.K) :=
    e.surjective.denseRange.separableSpace e.continuous
  exact {
    K := ULift.{u} P.K
    algebra := spatialTransportAlgebra e P.algebra
    vector := e P.vector
    coordinates := P.coordinates.transport e }

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProjectionCentralSpace
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Vectors continuous for projection centrality -/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

def projectionVectorDefect (J : H ≃ₗᵢ⋆[ℂ] H) (p : AlgebraProjection M) : H →L[ℂ] H :=
  p.val.val-conjugationOperator J p.val.val

def ProjectionCentralVector (J : H ≃ₗᵢ⋆[ℂ] H) (ξ η : H) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ p : AlgebraProjection M,
    ‖projectionVectorDefect J p ξ‖ < δ → ‖projectionVectorDefect J p η‖ < ε

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PublishedModularCoreType
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The published factorial-core criterion

Takesaki, *Duality for crossed products and the structure of von Neumann
algebras of type III*, Acta Math. 131 (1973), Lemma 8.2 and Corollary 9.7,
identifies type III₁ by factoriality of the modular core. Blackadar,
*Operator Algebras*, III.4.8.1--4 (p.329), gives the semifinite core and
its independence of the faithful normal state. A semifinite factor has
core `M ⊗ L∞(ℝ)`, so the factorial-core criterion also excludes that case.

Only this consequence is retained. The modular action has a KMS
certificate; factoriality of the concrete core is a premise to be proved
by the application, never a field of a product-construction input.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Type III₁ expressed by the published continuous-core characterization.
The ordinary type III projection conditions are retained explicitly. -/
structure TypeIII1Factor (M : VonNeumannAlgebra H) : Prop extends TypeIIIFactor M where
  core_type : ∀ (Ω : H), ‖Ω‖ = 1 →
    DenseRange (algebraVectorMap M Ω) → Function.Injective (algebraVectorMap M Ω) →
    ∀ (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
      (hU : ∀ ξ, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) ξ)),
      (∀ t x, x ∈ M → unitaryConj (U t) x ∈ M) →
      IsModularStateGroup M Ω U → TypeIIInfinityFactor (regularCoreAlgebra U hU M)

/-- The factorial-core classification, specialized to a separably
represented factor and a faithful normal vector state. -/
def PublishedFactorialModularCore : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Nontrivial H] [TopologicalSpace.SeparableSpace H],
    ∀ (M : VonNeumannAlgebra H), ScalarCenter M →
    ∀ (Ω : H), ‖Ω‖ = 1 →
      DenseRange (algebraVectorMap M Ω) → Function.Injective (algebraVectorMap M Ω) →
    ∀ (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
      (hU : ∀ ξ, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) ξ)),
      (∀ t x, x ∈ M → unitaryConj (U t) x ∈ M) → IsModularStateGroup M Ω U →
      ScalarCenter (regularCoreAlgebra U hU M) → TypeIII1Factor M

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PublishedExpectedMatrixSubfactor
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The expected hyperfinite subfactor consequence used for preparation

Marrakchi, *Full factors, bicentralizer flow and approximately inner
automorphisms*, arXiv:1811.10253v2, Theorem D(ii), gives trivial bicentralizer
for a type III₁ factor absorbing R_lambda. Haagerup, *Connes' bicentralizer
problem and uniqueness of the injective factor of type III₁*, Acta Math.
158 (1987), Lemma 3.8 and the proof of Theorem 3.1, (2) => (3), pp.142--145,
then gives an irreducible hyperfinite II₁ subfactor with faithful normal
expectation. Its increasing full-matrix model is retained here.

The composed trace-state has a cyclic separating vector in the given
separable type III representation: Haagerup, *The standard form of von
Neumann algebras*, Math. Scand. 37 (1975), Lemma 2.10(1), p.278, and
Blackadar III.1.7.9 give the representation transfer. This input concerns
a single algebra and contains no proximity or perturbation conclusion.
-/

namespace KadisonKastler

open Generator
open UnitalTomsWinter

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Only the expected matrix subfactor data needed by preparation. The
right action, neighboring inclusion and all estimates are constructed
by the application. -/
structure ExpectedMatrixSubfactorModel (M : VonNeumannAlgebra H) where
  stage : ℕ → FiniteMatrixStage M
  increasing : Monotone (fun n => (stage n).units.concreteAlgebra)
  trace : FaithfulTracialState (Algebra (FiniteMatrixStage.generatedVonNeumann stage))
  expectation : Algebra M →L[ℂ] Algebra (FiniteMatrixStage.generatedVonNeumann stage)
  unital : expectation 1 = 1
  left_module : ∀ (r : Algebra (FiniteMatrixStage.generatedVonNeumann stage)) (x : Algebra M),
    expectation (StarSubalgebra.inclusion (FiniteMatrixStage.generatedVonNeumann_le stage) r * x) =
      r * expectation x
  right_module : ∀ (r : Algebra (FiniteMatrixStage.generatedVonNeumann stage)) (x : Algebra M),
    expectation (x * StarSubalgebra.inclusion (FiniteMatrixStage.generatedVonNeumann_le stage) r) =
      expectation x * r
  vector : H
  vector_state : ∀ x : Algebra M,
    expectedTrace trace expectation x = inner ℂ vector (x.val vector)
  cyclic : DenseRange (algebraVectorMap M vector)
  separating : Function.Injective (algebraVectorMap M vector)
  irreducible : ∀ T ∈ M,
    (∀ r ∈ FiniteMatrixStage.generatedVonNeumann stage, r * T = T * r) →
    ∃ z : ℂ, T = z • (1 : H →L[ℂ] H)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TwoRatioRemoteBlock
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSignedGroup_finite _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {Ω : H}

namespace PointedMatrixSites

variable (S : PointedMatrixSites M Ω twoRatioSiteParameter)

def twoRatioRemoteMatrix (k n : ℕ) :
    MatrixUnitSystem (Fin (twoRatioMatrixSize k)) (H →L[ℂ] H) :=
  (S.finiteBlock (twoRatioRemoteSites k n) (twoRatioRemoteSites_nodup k n)).reindex
    (twoRatioRemoteIndex k n)

theorem twoRatioRemoteMatrix_algebra (k n : ℕ) :
    (S.twoRatioRemoteMatrix k n).algebra =
      (S.finiteBlock (twoRatioRemoteSites k n) (twoRatioRemoteSites_nodup k n)).algebra :=
  MatrixUnitSystem.reindex_algebra _ _

theorem twoRatioRemoteMatrix_le (k n : ℕ) :
    (S.twoRatioRemoteMatrix k n).algebra ≤ M.toStarSubalgebra := by
  rw [S.twoRatioRemoteMatrix_algebra]
  exact S.finiteBlock_le _ _

theorem twoRatioRemoteMatrix_commutes (k n : ℕ)
    (i j a b : Fin (twoRatioMatrixSize k)) :
    Commute ((S.twoRatioMatrix k).entry i j) ((S.twoRatioRemoteMatrix k n).entry a b) :=
  S.finiteBlock_commuting (twoRatioSiteShift_disjoint (le_max_left k n) k) _ _ _ _

theorem twoRatioRemoteMatrix_moment (k n : ℕ) (i j : Fin (twoRatioMatrixSize k)) :
    productVectorState Ω ((S.twoRatioRemoteMatrix k n).entry i j) =
      productVectorState Ω ((S.twoRatioMatrix k).entry i j) := by
  change inner ℂ Ω (S.blockEntry (twoRatioRemoteSites k n)
    (twoRatioRemoteIndex k n i) (twoRatioRemoteIndex k n j) Ω) =
    inner ℂ Ω (S.blockEntry (twoRatioFiniteSites k)
      ((Fintype.equivFin _).symm i) ((Fintype.equivFin _).symm j) Ω)
  rw [S.blockEntry_moment _ (twoRatioRemoteSites_nodup k n),
    S.blockEntry_moment _ (twoRatioFiniteSites_nodup k)]
  exact matrixSiteBlockWeight_map _ _ _ (twoRatioSiteShift_parameter _) _ _ _

theorem twoRatioRemoteMatrix_independent (k n : ℕ) (i j : Fin (twoRatioMatrixSize k))
    (b : (S.twoRatioMatrix n).algebra) :
    productVectorState Ω ((S.twoRatioRemoteMatrix k n).entry i j * b.val) =
      productVectorState Ω ((S.twoRatioMatrix k).entry i j) * productVectorState Ω b.val := by
  have hb : b.val ∈
      (S.finiteBlock (twoRatioFiniteSites n) (twoRatioFiniteSites_nodup n)).algebra := by
    rw [← S.twoRatioMatrix_algebra n]
    exact b.property
  have h := S.disjoint_block_algebra_independent
    (twoRatioRemoteSites_nodup k n) (twoRatioFiniteSites_nodup n)
    (twoRatioSiteShift_disjoint (le_max_right k n) k).symm
    (twoRatioRemoteIndex k n i) (twoRatioRemoteIndex k n j) ⟨b.val, hb⟩
  change productVectorState Ω ((S.twoRatioRemoteMatrix k n).entry i j * b.val) =
    productVectorState Ω ((S.twoRatioRemoteMatrix k n).entry i j) *
      productVectorState Ω b.val at h
  rw [S.twoRatioRemoteMatrix_moment] at h
  exact h

end PointedMatrixSites

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TwoRatioRemoteComplement
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSignedGroup_finite _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {Ω : H}

namespace PointedMatrixSites

variable (S : PointedMatrixSites M Ω twoRatioSiteParameter)

def twoRatioComplementMatrix (k n m : ℕ) :
    MatrixUnitSystem (Fin (twoRatioComplementSize k n m)) (H →L[ℂ] H) :=
  (S.finiteBlock (twoRatioComplementSites k n m)
    (twoRatioComplementSites_nodup k n m)).reindex (Fintype.equivFin _).symm

theorem twoRatioComplementMatrix_algebra (k n m : ℕ) :
    (S.twoRatioComplementMatrix k n m).algebra =
      (S.finiteBlock (twoRatioComplementSites k n m)
        (twoRatioComplementSites_nodup k n m)).algebra :=
  MatrixUnitSystem.reindex_algebra _ _

theorem twoRatioComplementMatrix_commutes (k n m : ℕ)
    (i j : Fin (twoRatioMatrixSize k) × Fin (twoRatioMatrixSize k))
    (a b : Fin (twoRatioComplementSize k n m)) :
    Commute (((S.twoRatioMatrix k).product (S.twoRatioRemoteMatrix k n)
      (S.twoRatioRemoteMatrix_commutes k n)).entry i j)
        ((S.twoRatioComplementMatrix k n m).entry a b) := by
  apply Commute.mul_left
  · exact S.finiteBlock_commuting (twoRatioComplementSites_disjoint k n m).1 _ _ _ _
  · exact S.finiteBlock_commuting (twoRatioComplementSites_disjoint k n m).2 _ _ _ _

theorem twoRatioComplementMatrix_contains_stage (k n m : ℕ) :
    (S.twoRatioMatrix m).algebra ≤
      (((S.twoRatioMatrix k).product (S.twoRatioRemoteMatrix k n)
        (S.twoRatioRemoteMatrix_commutes k n)).product
          (S.twoRatioComplementMatrix k n m)
            (S.twoRatioComplementMatrix_commutes k n m)).algebra := by
  rw [MatrixUnitSystem.product_algebra_eq_sup, MatrixUnitSystem.product_algebra_eq_sup,
    S.twoRatioMatrix_algebra m]
  apply S.finiteBlock_le_of_sites_le
  intro i hi
  by_cases hk : i ∈ twoRatioFiniteSites k
  · apply le_trans (S.site_le_finiteBlock _ _ i hk)
    rw [← S.twoRatioMatrix_algebra k]
    exact le_sup_left.trans le_sup_left
  · by_cases hn : i ∈ twoRatioRemoteSites k n
    · apply le_trans (S.site_le_finiteBlock _ _ i hn)
      rw [← S.twoRatioRemoteMatrix_algebra k n]
      exact le_sup_right.trans le_sup_left
    · have hm : i ∈ twoRatioComplementSites k n m :=
        (mem_twoRatioComplementSites k n m i).mpr ⟨hi, hk, hn⟩
      apply le_trans (S.site_le_finiteBlock _ _ i hm)
      rw [← S.twoRatioComplementMatrix_algebra k n m]
      exact le_sup_right

theorem twoRatioComplementMatrix_moment (k n m : ℕ)
    (i j a b : Fin (twoRatioMatrixSize k))
    (c d : Fin (twoRatioComplementSize k n m)) :
    productVectorState Ω
      ((((S.twoRatioMatrix k).product (S.twoRatioRemoteMatrix k n)
        (S.twoRatioRemoteMatrix_commutes k n)).entry (i, j) (a, b)) *
          (S.twoRatioComplementMatrix k n m).entry c d) =
      productVectorState Ω ((S.twoRatioMatrix k).entry i a) *
        productVectorState Ω ((S.twoRatioMatrix k).entry j b) *
          productVectorState Ω ((S.twoRatioComplementMatrix k n m).entry c d) := by
  have h := S.disjoint_three_blockEntry_moment
    (twoRatioFiniteSites_nodup k) (twoRatioRemoteSites_nodup k n)
    (twoRatioComplementSites_nodup k n m)
    (twoRatioSiteShift_disjoint (le_max_left k n) k)
    (twoRatioComplementSites_disjoint k n m).1
    (twoRatioComplementSites_disjoint k n m).2
    ((Fintype.equivFin _).symm i) ((Fintype.equivFin _).symm a)
    (twoRatioRemoteIndex k n j) (twoRatioRemoteIndex k n b)
    ((Fintype.equivFin _).symm c) ((Fintype.equivFin _).symm d)
  rw [← S.blockEntry_moment _ (twoRatioFiniteSites_nodup k),
    ← S.blockEntry_moment _ (twoRatioRemoteSites_nodup k n),
    ← S.blockEntry_moment _ (twoRatioComplementSites_nodup k n m)] at h
  change productVectorState Ω
      ((((S.twoRatioMatrix k).product (S.twoRatioRemoteMatrix k n)
        (S.twoRatioRemoteMatrix_commutes k n)).entry (i, j) (a, b)) *
          (S.twoRatioComplementMatrix k n m).entry c d) =
      productVectorState Ω ((S.twoRatioMatrix k).entry i a) *
        productVectorState Ω ((S.twoRatioRemoteMatrix k n).entry j b) *
          productVectorState Ω ((S.twoRatioComplementMatrix k n m).entry c d) at h
  rw [S.twoRatioRemoteMatrix_moment] at h
  exact h

end PointedMatrixSites

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TwoRatioStages
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSignedGroup_finite _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Product matrix stages constructed from two-ratio coordinates -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {Ω : H}

namespace PointedMatrixSites

variable (S : PointedMatrixSites M Ω twoRatioSiteParameter)

def twoRatioStages : ProductMatrixStages (H := H) where
  size := twoRatioMatrixSize
  matrix := S.twoRatioMatrix
  increasing := S.twoRatioMatrix_increasing
  vector := Ω
  unit_vector := S.unit_vector
  local_cyclic := S.twoRatioMatrix_local_cyclic
  separating := by
    rw [S.twoRatioMatrix_generates]
    exact S.separating
  remote k n := ⟨{
    copy := S.twoRatioRemoteMatrix k n
    copy_mem := by
      rw [S.twoRatioMatrix_generates]
      exact S.twoRatioRemoteMatrix_le k n
    commutes := S.twoRatioRemoteMatrix_commutes k n
    independent := S.twoRatioRemoteMatrix_independent k n
    complement := fun m => ⟨twoRatioComplementSize k n m,
      S.twoRatioComplementMatrix k n m, S.twoRatioComplementMatrix_commutes k n m,
      S.twoRatioComplementMatrix_contains_stage k n m,
      (fun i j => productVectorState Ω ((S.twoRatioComplementMatrix k n m).entry i j)),
      S.twoRatioComplementMatrix_moment k n m⟩ }⟩

theorem twoRatioStages_algebra : S.twoRatioStages.algebra = M :=
  S.twoRatioMatrix_generates

def twoRatioStages_coordinates :
    PointedMatrixSites S.twoRatioStages.algebra S.twoRatioStages.vector
      twoRatioSiteParameter := by
  change PointedMatrixSites S.twoRatioStages.algebra Ω twoRatioSiteParameter
  rw [S.twoRatioStages_algebra]
  exact S

end PointedMatrixSites

end

end KadisonKastler

end OAI
end


