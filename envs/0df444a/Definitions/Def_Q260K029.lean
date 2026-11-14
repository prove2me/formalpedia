-- Prove2me | Definitions.Def_Q260K029
-- name    : Q260K029
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T07:16:19.06196+00:00
-- url     : https://prove2.me/theorems/a221dbfa-4486-4399-9031-4ea944df88cd
-- title:
--   Definitions bundle Q260K029 of the split of OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 42 declarations of OpenAI's Lean: 19 definitions, 1 inductive type or structure and 22 theorems. The definitions and types are `OAI.KadisonKastler.StandardTracialPosition.diagonalRepresentation`, `OAI.KadisonKastler.TracialSequenceFactor`, `OAI.KadisonKastler.analyticAlgebraOrder`, `OAI.KadisonKastler.centralVectorDefect`, `OAI.KadisonKastler.conjugateMatrixUnits`, `OAI.KadisonKastler.conjugateOperatorMap`, `OAI.KadisonKastler.conjugateRightStarAlgebra`, `OAI.KadisonKastler.countableDiagonalHom`, `OAI.KadisonKastler.faithfulCyclicHom`, `OAI.KadisonKastler.faithfulCyclicSpace`, `OAI.KadisonKastler.minimalCyclicRetraction`, `OAI.KadisonKastler.modularQuadratic`, `OAI.KadisonKastler.productBoundaryRepresentation`, `OAI.KadisonKastler.productBoundaryValue`, `OAI.KadisonKastler.projectionFamilyCommutationSpace`, `OAI.KadisonKastler.projectionFamilyPinching`, `OAI.KadisonKastler.projectionFamilyRemainderSpace`, `OAI.KadisonKastler.rescaledGraphMap`, `OAI.KadisonKastler.rightVectorLinear`, `OAI.KadisonKastler.typeICyclicEquiv`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `KadisonKastler_AnalyticAlgebraBounds`, `KadisonKastler_CentralDefectSelfAdjoint`, `KadisonKastler_ConjugateMatrixStages`, `KadisonKastler_ConjugateRightAlgebra`, `KadisonKastler_FaithfulCyclicConstruction`, `KadisonKastler_MatrixCentralVectorTests`, `KadisonKastler_MinimalCyclicExpectation`, `KadisonKastler_ModularPositiveCone`, `KadisonKastler_ProductBoundaryCocycle`, `KadisonKastler_ProjectionFamilySpaces`, `KadisonKastler_RescaledTomitaGraph`, `KadisonKastler_StandardTraceInvariants`, `KadisonKastler_TracialSequenceFactor`, `KadisonKastler_TypeICyclicRepresentation`, `KadisonKastler_TypeIInjectivity`.
--
--   **Imports.** It imports the bundle `Q260K064` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q260K031`, `Q260K067` and `Q260K068`; the statements `OAI.KadisonKastler.CommonTracialPositionData.conjugations_sub_le`, `OAI.KadisonKastler.CuntzFamily.exists_diagonal_average_mem`, `OAI.KadisonKastler.CuntzFamily.upperRight_eq_zero_of_typeIII_constantNorm_of_projection_countability`, `OAI.KadisonKastler.StandardTracialPosition.exists_ae_diagonal_unitary_comparison`, `OAI.KadisonKastler.StandardTracialPosition.scalar_of_diagonal_invariant`, `OAI.KadisonKastler.TypeIIIFactor.exists_cyclic_vector_same_state`, `OAI.KadisonKastler.TypeIIIFactor.exists_spatial_equiv_of_amplified_isometric`, `OAI.KadisonKastler.exists_commonTracialPosition_of_matrixStages`, `OAI.KadisonKastler.exists_corner_tracial_vector`, `OAI.KadisonKastler.exists_finite_two_vector_projection`, `OAI.KadisonKastler.exists_nondominated_two_vector_witness`, `OAI.KadisonKastler.exists_partition_projection_gap`, `OAI.KadisonKastler.exists_product_boundary_intertwiner`, `OAI.KadisonKastler.exists_projection_gap_of_finite_pinching`, `OAI.KadisonKastler.exists_selfAdjoint_two_vector_projection`, `OAI_KadisonKastler_exists_standard_finiteFactor_isomorphism`, `OAI_KadisonKastler_exists_starEquiv_of_boundary_normalization`, `OAI_KadisonKastler_minimal_row_family_right_module`, `OAI.KadisonKastler.modularCore_equiv_of_two_states`, `OAI.KadisonKastler.regularCore_not_factor_of_II1`, `OAI.KadisonKastler.regularCore_not_factor_of_typeIIInfinity`, `OAI.KadisonKastler.relative_modularQuadratic_mem_central`, `OAI.KadisonKastler.scalarCenter_regularCore_of_two_site_frequencies`, `OAI.KadisonKastler.scalarCenter_spatialProduct_of_local_swaps` and `OAI.KadisonKastler.typeIII_of_factorialCore`; the proofs of `OAI.Generator.Tracial.traceFreeHilbertClosure_isII1Factor`, `OAI.KadisonKastler.FullMatrixCorner.scalarMatrixAlgebra_isInjective`, `OAI.KadisonKastler.StandardTracialPosition.exists_ae_diagonal_unitary_comparison`, `OAI.KadisonKastler.StandardTracialPosition.scalar_of_diagonal_invariant`, `OAI_KadisonKastler_WeakOperatorField_exists_unitary_lift`, `OAI.KadisonKastler.exists_continuous_unital_transfer_of_traceDense`, `OAI.KadisonKastler.exists_near_starEquiv_of_traceDense_unitary_images`, `OAI.KadisonKastler.exists_original_irreducible_matrix_algebra`, `OAI.KadisonKastler.exists_selfAdjoint_split_of_finite_typeI_commutant`, `OAI.KadisonKastler.exists_strongly_invariant_product_of_simple`, `OAI.KadisonKastler.exists_unitary_approx_of_nearInclusion`, `OAI.KadisonKastler.exists_unitary_embedding_of_invariant_group`, `OAI_KadisonKastler_exists_unitary_embedding_of_invariant_group_in_algebra`, `OAI.KadisonKastler.exists_unitary_invariantGroup_embedding_in_algebra`, `OAI.KadisonKastler.finiteFactor_isPrimeAlgebra`, `OAI.KadisonKastler.isometry_pullback_norm_sq`, `OAI.KadisonKastler.projectionVectorWeight_mem_Ioo`, `OAI.KadisonKastler.publishedCentralPairDecomposition`, `OAI.KadisonKastler.publishedSimpleDerivationInner`, `OAI.KadisonKastler.scalarCenter_spatialProduct_of_local_swaps`, `OAI.KadisonKastler.scalar_center_of_near_II1`, `OAI.KadisonKastler.unitary_transfer_bound_of_traceDense` and `OAI.KadisonKastler.vector_state_eq_trace_of_relative_central`.
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
import Mathlib.Algebra.Group.Finsupp
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
import Mathlib.Algebra.QuadraticDiscriminant
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
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Normed.Module.RCLike.Real
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
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
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
import Mathlib.Topology.MetricSpace.Contracting
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
import Definitions.Def_Q260K064

section
-- module Solutions.OAIQ075_KS.KadisonKastler_AnalyticAlgebraBounds
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

local instance analyticAlgebraOrder (M : VonNeumannAlgebra H) : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProductBoundaryCocycle
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.CommonTracialPositionData.rightEquiv_transportEquiv _root_.OAI.KadisonKastler.FiniteInnerAverage.algebraApply_sub _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.concreteDerivation_apply _root_.OAI.KadisonKastler.concreteDiagonalSequenceUnitary_coe _root_.OAI.KadisonKastler.concreteDiagonalSequence_apply _root_.OAI.KadisonKastler.concreteDiagonalUnitary_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.matrixLiftUnitaryAt_coe _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.spatialTransportEquiv_apply _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.typeICyclicHom_apply _root_.OAI.KadisonKastler.typeICyclicOperator_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The two-sided product boundary cocycle

Standard tracial conjugation turns the second copy into a commuting right
action. The resulting product cocycle is close to the product representation
with the explicit error `2 * δ + 2 * κ`.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {G D : Type*} [Group G]

/-- The pointwise product of the left cocycle and its tracial right copy. -/
def productBoundaryValue {N : VonNeumannAlgebra H} (p : StandardTracialPosition N)
    (W : G → D → unitary (H →L[ℂ] H)) (g : G × G) (x : D × D) :
    unitary (H →L[ℂ] H) :=
  W g.1 x.1 * conjugationUnitary p.conjugation p.conjugation_involutive (W g.2 x.2)

omit [Group G] in
@[simp]
theorem productBoundaryValue_coe {N : VonNeumannAlgebra H} (p : StandardTracialPosition N)
    (W : G → D → unitary (H →L[ℂ] H)) (g : G × G) (x : D × D) :
    (productBoundaryValue p W g x : H →L[ℂ] H) =
      (W g.1 x.1 : H →L[ℂ] H) *
        conjugationOperator p.conjugation (W g.2 x.2) := rfl

/-- The commuting left and right copies form an actual representation. -/
def productBoundaryRepresentation {M : VonNeumannAlgebra H}
    (p : StandardTracialPosition M) (U : G →* unitary (Algebra M)) :
    (G × G) →* unitary (H →L[ℂ] H) where
  toFun g :=
    Unitary.map (StarMonoidHom.ofClass M.toStarSubalgebra.subtype) (U g.1) *
      conjugationUnitary p.conjugation p.conjugation_involutive
        (Unitary.map (StarMonoidHom.ofClass M.toStarSubalgebra.subtype) (U g.2))
  map_one' := by
    apply Subtype.ext
    change (U 1 : Algebra M).val *
      conjugationOperator p.conjugation (U 1 : Algebra M).val = 1
    rw [map_one]
    change 1 * conjugationOperator p.conjugation 1 = 1
    rw [conjugationOperator_one p.conjugation p.conjugation_involutive, mul_one]
  map_mul' g h := by
    apply Subtype.ext
    change (((U (g.1 * h.1) : Algebra M).val) *
      conjugationOperator p.conjugation (U (g.2 * h.2) : Algebra M).val) = _
    simp only [map_mul, MulMemClass.coe_mul,
      conjugationOperator_mul p.conjugation p.conjugation_involutive]
    have hc := p.commute_conjugationOperator (U h.1 : Algebra M).val
      (U g.2 : Algebra M).val (U h.1).val.property (U g.2).val.property
    change ((U g.1 : Algebra M).val * (U h.1 : Algebra M).val) *
        (conjugationOperator p.conjugation (U g.2 : Algebra M).val *
          conjugationOperator p.conjugation (U h.2 : Algebra M).val) =
      ((U g.1 : Algebra M).val * conjugationOperator p.conjugation (U g.2 : Algebra M).val) *
        ((U h.1 : Algebra M).val * conjugationOperator p.conjugation (U h.2 : Algebra M).val)
    calc
      _ = (U g.1 : Algebra M).val *
          ((U h.1 : Algebra M).val * conjugationOperator p.conjugation (U g.2 : Algebra M).val) *
          conjugationOperator p.conjugation (U h.2 : Algebra M).val := by noncomm_ring
      _ = _ := by rw [hc.eq]; noncomm_ring

@[simp]
theorem productBoundaryRepresentation_coe {M : VonNeumannAlgebra H}
    (p : StandardTracialPosition M) (U : G →* unitary (Algebra M)) (g : G × G) :
    (productBoundaryRepresentation p U g : H →L[ℂ] H) =
      (U g.1 : Algebra M).val * conjugationOperator p.conjugation (U g.2 : Algebra M).val := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RescaledTomitaGraph
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.CommonTracialPositionData.rightEquiv_transportEquiv _root_.OAI.KadisonKastler.FiniteInnerAverage.algebraApply_sub _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.StandardTracialPosition.conjugation_algebraVector _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.concreteDerivation_apply _root_.OAI.KadisonKastler.concreteDiagonalSequenceUnitary_coe _root_.OAI.KadisonKastler.concreteDiagonalSequence_apply _root_.OAI.KadisonKastler.concreteDiagonalUnitary_coe _root_.OAI.KadisonKastler.concreteTraceEmbedding_inner _root_.OAI.KadisonKastler.concreteTraceLeftAction_embedding _root_.OAI.KadisonKastler.concreteTraceLeftUnitary_coe _root_.OAI.KadisonKastler.concreteTraceRightAction_embedding _root_.OAI.KadisonKastler.concreteTraceRightUnitary_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.matrixAlgebraEquiv_apply _root_.OAI.KadisonKastler.matrixLiftUnitaryAt_coe _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.productBoundaryRepresentation_coe _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.spatialTransportEquiv_apply _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.typeICyclicHom_apply _root_.OAI.KadisonKastler.typeICyclicOperator_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply _root_.OAI.KadisonSimilarity.predualRestriction_apply _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Rescaled Tomita graphs in a fixed two-coordinate Hilbert space

A fixed conjugation identifies the conjugate copy of the Hilbert space
with the original one. In these coordinates the graph vector is
`(x Ω, c J (x* Ω))`. The same identification is used for both algebras.
No closability or modular spectral theorem is needed for the closed
linear graph subspace or the elementary projection comparison below.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The conjugation in the second coordinate makes the graph map
complex-linear rather than conjugate-linear. -/
def rescaledGraphMap (P : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H)
    (Ω : H) (c : ℝ) : Algebra P →ₗ[ℂ] TomitaGraphHilbert H where
  toFun x := rescaledGraphVector J Ω c x.val
  map_add' x y := by
    ext i
    fin_cases i <;> simp [rescaledGraphVector, star_add, map_add, smul_add]
  map_smul' z x := by
    ext i
    fin_cases i
    · simp [rescaledGraphVector]
    · change c • J (star (z • x.val) Ω) = z • (c • J (star x.val Ω))
      rw [star_smul, smul_apply, J.map_smulₛₗ]
      change c • (star (star z) • J (star x.val Ω)) = z • (c • J (star x.val Ω))
      rw [star_star, smul_comm]

@[simp] theorem rescaledGraphMap_apply (P : VonNeumannAlgebra H)
    (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ) (x : Algebra P) :
    rescaledGraphMap P J Ω c x = rescaledGraphVector J Ω c x.val := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ConjugateRightAlgebra
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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
theorem conjugationOperator_add (J : H ≃ₗᵢ⋆[ℂ] H) (a b : H →L[ℂ] H) :
    conjugationOperator J (a + b) = conjugationOperator J a + conjugationOperator J b := by
  ext ξ
  exact map_add J _ _

omit [CompleteSpace H] in
theorem conjugationOperator_smul (J : H ≃ₗᵢ⋆[ℂ] H) (z : ℂ) (a : H →L[ℂ] H) :
    conjugationOperator J (z • a) = star z • conjugationOperator J a := by
  ext ξ
  exact J.map_smulₛₗ z (a (J ξ))

/-- Conjugation by an involutive anti-isometry preserves operator adjoints. -/
theorem conjugationOperator_star (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (a : H →L[ℂ] H) :
    conjugationOperator J (star a) = star (conjugationOperator J a) := by
  ext x
  apply ext_inner_left ℂ
  intro y
  change inner ℂ y (conjugationOperator J (star a) x) =
    inner ℂ y ((conjugationOperator J a).adjoint x)
  rw [ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ y (J (star a (J x))) = inner ℂ (J (a (J y))) x
  have hl := conjugateIsometry_inner J (J y) (star a (J x))
  have hr := conjugateIsometry_inner J (a (J y)) (J x)
  rw [hJ y] at hl
  rw [hJ x] at hr
  rw [hl, hr]
  congr 1
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]

def conjugateRightStarAlgebra (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (R : VonNeumannAlgebra H) : StarSubalgebra ℂ (H →L[ℂ] H) where
  carrier := conjugationOperator J '' (R : Set (H →L[ℂ] H))
  zero_mem' := ⟨0, R.zero_mem, by ext ξ; simp [conjugationOperator_apply]⟩
  add_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a + b, R.add_mem ha hb, conjugationOperator_add J a b⟩
  one_mem' := ⟨1, R.one_mem, conjugationOperator_one J hJ⟩
  mul_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a * b, R.mul_mem ha hb, conjugationOperator_mul J hJ a b⟩
  algebraMap_mem' z := by
    refine ⟨star z • (1 : H →L[ℂ] H), R.toStarSubalgebra.smul_mem R.one_mem _, ?_⟩
    rw [conjugationOperator_smul, star_star, conjugationOperator_one J hJ]
    simp only [Algebra.smul_def, mul_one]
  star_mem' := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨star a, R.toStarSubalgebra.star_mem' ha, conjugationOperator_star J hJ a⟩

/-- Conjugating a complex-linear map twice restores complex linearity. -/
def conjugateOperatorMap (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (E : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H)) :
    (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H) :=
  LinearMap.mkContinuous
    { toFun := fun x => conjugationOperator J (E (conjugationOperator J x))
      map_add' := by
        intro x y
        rw [conjugationOperator_add, map_add, conjugationOperator_add]
      map_smul' := by
        intro z x
        change conjugationOperator J (E (conjugationOperator J (z • x))) =
          z • conjugationOperator J (E (conjugationOperator J x))
        rw [conjugationOperator_smul, map_smul, conjugationOperator_smul, star_star] }
    ‖E‖ (fun x => by
      change ‖conjugationOperator J (E (conjugationOperator J x))‖ ≤ ‖E‖ * ‖x‖
      rw [norm_conjugationOperator J hJ]
      exact (E.le_opNorm _).trans_eq (by rw [norm_conjugationOperator J hJ]))

@[simp]
theorem conjugateOperatorMap_apply (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (E : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H)) (x : H →L[ℂ] H) :
    conjugateOperatorMap J hJ E x = conjugationOperator J (E (conjugationOperator J x)) := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ConjugateMatrixStages
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.concrete_finiteDimensional _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSignedGroup_finite _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.Generator.MatrixUnitSystem.adaptedBasis_apply _root_.OAI.Generator.MatrixUnitSystem.initialColumn_apply _root_.OAI.Generator.orthonormalMatrixUnits_entry_apply _root_.OAI.KadisonKastler.MatrixSiteWord.eval_append _root_.OAI.KadisonKastler.MatrixSiteWord.eval_cons _root_.OAI.KadisonKastler.MatrixSiteWord.eval_nil _root_.OAI.KadisonKastler.MatrixSiteWord.eval_reindex _root_.OAI.KadisonKastler.MatrixSiteWord.eval_star _root_.OAI.KadisonKastler.conjugatedMatrixUnits_entry _root_.OAI.KadisonKastler.matrixPermutationValue_one _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.spatialMatrixUnits_entry _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Actual matrix stages in the conjugate right algebra

Conjugation changes the scalar coefficients by complex conjugation, while
the conjugated matrix-unit entries retain their usual product laws. Thus
the right algebra is generated by actual increasing full matrix stages.
This lets the same finite averaging argument transfer its irreducibility
to a nearby commutant.
-/

namespace KadisonKastler

open Generator
open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem conjugationOperator_zero (J : H ≃ₗᵢ⋆[ℂ] H) :
    conjugationOperator J (0 : H →L[ℂ] H) = 0 := by
  ext ξ
  exact map_zero J

omit [CompleteSpace H] in
theorem conjugationOperator_sum_p0 (J : H ≃ₗᵢ⋆[ℂ] H)
    {ι : Type*} (s : Finset ι) (f : ι → H →L[ℂ] H) :
    conjugationOperator J (∑ i ∈ s, f i) = ∑ i ∈ s, conjugationOperator J (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, conjugationOperator_zero]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, conjugationOperator_add, ih]

/-- Actual full matrix units in the conjugate right algebra. -/
def conjugateMatrixUnits (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : MatrixUnitSystem ι (H →L[ℂ] H)) : MatrixUnitSystem ι (H →L[ℂ] H) where
  entry i j := conjugationOperator J (E.entry i j)
  star_entry i j := by rw [← conjugationOperator_star J hJ, E.star_entry]
  mul_entry i j k l := by
    rw [← conjugationOperator_mul J hJ, E.mul_entry]
    split_ifs <;> simp only [conjugationOperator_zero]
  total := by
    rw [← conjugationOperator_sum_p0, E.total, conjugationOperator_one J hJ]

@[simp]
theorem conjugateMatrixUnits_entry (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : MatrixUnitSystem ι (H →L[ℂ] H)) (i j : ι) :
    (conjugateMatrixUnits J hJ E).entry i j = conjugationOperator J (E.entry i j) := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TypeICyclicRepresentation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

/-- Evaluation at a nonzero vector in a minimal projection is faithful on
the right ideal supported by that projection. -/
theorem minimal_right_ideal_separating (p : AlgebraProjection M)
    (hp : IsMinimalProjectionIn M p) (ξ : H) (hξ : ξ ≠ 0)
    (hpξ : p.val.val ξ = ξ) (a : Algebra M) (hap : a * p.val = a)
    (haξ : a.val ξ = 0) : a = 0 := by
  have hpa : p.val * star a = star a := by
    simpa only [star_mul, p.property.isSelfAdjoint.star_eq] using congrArg star hap
  obtain ⟨z, hz⟩ := minimal_corner_scalar p hp (star a * a)
    (by rw [← mul_assoc, hpa]) (by rw [mul_assoc, hap])
  have he : z • ξ = 0 := by
    have he := congrArg (fun b : Algebra M => b.val ξ) hz
    change star a.val (a.val ξ) = z • p.val.val ξ at he
    rw [haξ, map_zero, hpξ] at he
    exact he.symm
  have hz0 : z = 0 := (smul_eq_zero.mp he).resolve_right hξ
  apply (CStarRing.star_mul_self_eq_zero_iff a).mp
  rw [hz, hz0, zero_smul]

/-- The cyclic restriction of a factor at a minimal projection is faithful. -/
theorem typeICyclicHom_injective (hM : ScalarCenter M) (p : AlgebraProjection M)
    (hp : IsMinimalProjectionIn M p) (ξ : H) (hξ : ξ ≠ 0)
    (hpξ : p.val.val ξ = ξ) : Function.Injective (typeICyclicHom (M := M) ξ) := by
  have hker (a : Algebra M) (ha : typeICyclicHom ξ a = 0) : a = 0 := by
    have hlink (b : Algebra M) : a * b * p.val = 0 := by
      apply minimal_right_ideal_separating p hp ξ hξ hpξ
      · rw [mul_assoc, p.property.isIdempotentElem.eq]
      · have he := congrArg (fun T : typeICyclicSpace M ξ →L[ℂ] typeICyclicSpace M ξ =>
          (T (typeICyclicHom ξ b (typeICyclicVector M ξ)) : H)) ha
        change a.val (b.val ξ) = 0 at he
        change a.val (b.val (p.val.val ξ)) = 0
        rwa [hpξ]
    have hK : projectionOrbitClosure p ≤ a.val.ker := by
      apply Submodule.topologicalClosure_minimal
      · apply Submodule.span_le.mpr
        rintro y ⟨b, x, rfl⟩
        exact congrArg (fun c : Algebra M => c.val x) (hlink b)
      · exact a.val.isClosed_ker
    have he : a * (centralSupport p).val = 0 := by
      apply Subtype.ext
      apply ContinuousLinearMap.ext
      intro x
      exact hK ((projectionOrbitClosure p).starProjection_apply_mem x)
    have hfactor (c : Algebra M) (hc : ∀ b : Algebra M, b * c = c * b) :
        ∃ z : ℂ, c = z • (1 : Algebra M) := by
      obtain ⟨z, hz⟩ := hM c.val c.property (fun b hb =>
        congrArg Subtype.val (hc ⟨b, hb⟩))
      exact ⟨z, Subtype.ext hz⟩
    rwa [centralSupport_eq_one_of_factor hfactor p hp.1, mul_one] at he
  intro a b hab
  apply sub_eq_zero.mp
  apply hker
  rw [map_sub, hab, sub_self]

theorem typeICyclicHom_norm (hM : ScalarCenter M) (p : AlgebraProjection M)
    (hp : IsMinimalProjectionIn M p) (ξ : H) (hξ : ξ ≠ 0)
    (hpξ : p.val.val ξ = ξ) (a : Algebra M) : ‖typeICyclicHom ξ a‖ = ‖a‖ := by
  let : CStarAlgebra (Algebra M) := {}
  let : CStarAlgebra (typeICyclicSpace M ξ →L[ℂ] typeICyclicSpace M ξ) := {}
  exact NonUnitalStarAlgHom.norm_map (typeICyclicHom ξ)
    (typeICyclicHom_injective hM p hp ξ hξ hpξ) a

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TypeIInjectivity
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Injectivity of type I factors in their given representation

The cyclic restriction at a minimal projection is faithful and irreducible.
Kaplansky approximation and weak compactness of the original operator ball
make it surjective onto all operators on that cyclic space.  Compression,
followed by the inverse restriction, is therefore an ambient contractive
projection onto the original algebra.
-/

namespace KadisonKastler

open Generator Generator.Tracial Filter
open scoped Topology

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

/-- Every operator on the minimal cyclic space comes from the original
factor; the assertion includes the closed unit ball without norm loss. -/
theorem typeICyclicHom_surjective_unitBall (hM : ScalarCenter M)
    (p : AlgebraProjection M) (hp : IsMinimalProjectionIn M p)
    (ξ : H) (hξ : ξ ≠ 0) (hpξ : p.val.val ξ = ξ)
    (T : typeICyclicSpace M ξ →L[ℂ] typeICyclicSpace M ξ) (hT : ‖T‖ ≤ 1) :
    ∃ a : Algebra M, ‖a‖ ≤ 1 ∧ typeICyclicHom ξ a = T := by
  classical
  let K := typeICyclicSpace M ξ
  let ρ : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K) := typeICyclicHom ξ
  let A : StarSubalgebra ℂ (K →L[ℂ] K) := ρ.range
  have hcomm : T ∈ Set.centralizer (Set.centralizer (A : Set (K →L[ℂ] K))) := by
    intro S hS
    obtain ⟨z, hscalar⟩ := typeICyclicHom_commutant p hp ξ hpξ S
      (fun a => hS (ρ a) ⟨a, rfl⟩)
    change S * T = T * S
    rw [hscalar]
    simpa only [Algebra.algebraMap_eq_smul_one] using Algebra.commutes z T
  have hnet := publishedKaplanskyDensity.exists_weak_contraction_net (H := K)
    A T hcomm hT
  let c : Finset K × ℕ → A := Classical.choose hnet
  have hc : ∀ d, ‖c d‖ ≤ 1 := (Classical.choose_spec hnet).1
  have hlim : ∀ x y : K, Tendsto (fun d => inner ℂ y ((c d).val x)) atTop
      (𝓝 (inner ℂ y (T x))) := (Classical.choose_spec hnet).2
  choose a ha using fun d => (c d).property
  have ha' (d : Finset K × ℕ) : ρ (a d) = (c d).val := ha d
  have hn (d : Finset K × ℕ) : ‖a d‖ ≤ 1 := by
    rw [← typeICyclicHom_norm hM p hp ξ hξ hpξ]
    change ‖ρ (a d)‖ ≤ 1
    rw [ha' d]
    exact hc d
  let ω : Ultrafilter (Finset K × ℕ) := Ultrafilter.of atTop
  obtain ⟨b, hb, hweak⟩ := exists_weak_operator_ultralimit ω
    (fun d => (a d).val) 1 zero_le_one hn
  let a₀ : Algebra M := ⟨b, weak_operator_limit_mem M a b hweak⟩
  refine ⟨a₀, hb, ?_⟩
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  have h₁ : Tendsto (fun d => inner ℂ y (ρ (a d) x)) (ω : Filter (Finset K × ℕ))
      (𝓝 (inner ℂ y (ρ a₀ x))) := hweak x.val y.val
  have h₂ : Tendsto (fun d => inner ℂ y (ρ (a d) x)) (ω : Filter (Finset K × ℕ))
      (𝓝 (inner ℂ y (T x))) := by
    simpa only [ha'] using (hlim x y).mono_left (Ultrafilter.of_le atTop)
  exact tendsto_nhds_unique h₁ h₂

theorem typeICyclicHom_surjective (hM : ScalarCenter M)
    (p : AlgebraProjection M) (hp : IsMinimalProjectionIn M p)
    (ξ : H) (hξ : ξ ≠ 0) (hpξ : p.val.val ξ = ξ) :
    Function.Surjective (typeICyclicHom (M := M) ξ) := by
  let : CStarAlgebra (Algebra M) := {}
  let : CStarAlgebra (typeICyclicSpace M ξ →L[ℂ] typeICyclicSpace M ξ) := {}
  intro T
  by_cases hT : T = 0
  · exact ⟨0, by rw [map_zero, hT]⟩
  have hn : ‖T‖ ≠ 0 := norm_ne_zero_iff.mpr hT
  have hsmall : ‖(‖T‖ : ℂ)⁻¹ • T‖ ≤ 1 := by
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg T), inv_mul_cancel₀ hn]
  obtain ⟨a, _, ha⟩ := typeICyclicHom_surjective_unitBall hM p hp ξ hξ hpξ
    ((‖T‖ : ℂ)⁻¹ • T) hsmall
  refine ⟨(‖T‖ : ℂ) • a, ?_⟩
  calc
    typeICyclicHom ξ ((‖T‖ : ℂ) • a) =
        (‖T‖ : ℂ) • typeICyclicHom ξ a := rfl
    _ = T := by
      rw [ha, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hn), one_smul]

/-- The algebraic identification with all operators on the minimal cyclic
space, constructed in the original representation. -/
def typeICyclicEquiv (hM : ScalarCenter M) (p : AlgebraProjection M)
    (hp : IsMinimalProjectionIn M p) (ξ : H) (hξ : ξ ≠ 0)
    (hpξ : p.val.val ξ = ξ) :
    Algebra M ≃⋆ₐ[ℂ] (typeICyclicSpace M ξ →L[ℂ] typeICyclicSpace M ξ) :=
  StarAlgEquiv.ofBijective (typeICyclicHom ξ)
    ⟨typeICyclicHom_injective hM p hp ξ hξ hpξ,
      typeICyclicHom_surjective hM p hp ξ hξ hpξ⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixCentralVectorTests
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Matrix-unit tests for central vectors -/

namespace KadisonKastler

open Generator
open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

/-- Right evaluation is linear in the algebra element, despite the two conjugations. -/
def rightVectorLinear (J : H ≃ₗᵢ⋆[ℂ] H) (ξ : H) : (H →L[ℂ] H) →ₗ[ℂ] H where
  toFun a := conjugationOperator J (star a) ξ
  map_add' a b := by
    change J (star (a + b) (J ξ)) = J (star a (J ξ)) + J (star b (J ξ))
    rw [star_add, add_apply, map_add]
  map_smul' c a := by
    change J (star (c • a) (J ξ)) = c • J (star a (J ξ))
    rw [star_smul, smul_apply, J.map_smulₛₗ]
    simp

@[simp] theorem rightVectorLinear_apply (J : H ≃ₗᵢ⋆[ℂ] H) (ξ : H) (a : H →L[ℂ] H) :
    rightVectorLinear J ξ a = conjugationOperator J (star a) ξ := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CentralDefectSelfAdjoint
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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

def centralVectorDefect (J : H ≃ₗᵢ⋆[ℂ] H) (ξ : H) : (H →L[ℂ] H) →ₗ[ℂ] H where
  toFun a := a ξ - rightVectorLinear J ξ a
  map_add' a b := by
    simp only [add_apply,map_add]
    abel
  map_smul' c a := by
    simp only [smul_apply,map_smul,smul_sub,RingHom.id_apply]

@[simp] theorem centralVectorDefect_apply (J : H ≃ₗᵢ⋆[ℂ] H) (ξ : H) (a : H →L[ℂ] H) :
    centralVectorDefect J ξ a = a ξ - conjugationOperator J (star a) ξ := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FaithfulCyclicConstruction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A faithful cyclic representation from a countable amplification

The weighted dense vector is separating for the diagonal action. Its
closed orbit gives a faithful cyclic restriction. Kaplansky density and
weak compactness of the original operator ball show that the restricted
image is already a von Neumann algebra.
-/

namespace KadisonKastler

open Generator Generator.Tracial Filter TopologicalSpace
open scoped Topology

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H] [SeparableSpace H]

def countableDiagonalHom (M : VonNeumannAlgebra H) :
    Algebra M →⋆ₐ[ℂ] (CountableHilbertSum H →L[ℂ] CountableHilbertSum H) :=
  l2DiagonalHom.comp M.toStarSubalgebra.subtype

abbrev faithfulCyclicSpace (M : VonNeumannAlgebra H) :=
  vectorOrbitClosure (countableDiagonalHom M).range (denseSeparatingUnitVector (H := H))

def faithfulCyclicHom (M : VonNeumannAlgebra H) :
    Algebra M →⋆ₐ[ℂ] (faithfulCyclicSpace M →L[ℂ] faithfulCyclicSpace M) :=
  (reducingRestriction (faithfulCyclicSpace M) (countableDiagonalHom M).range
    (fun a _ hy => vectorOrbitClosure_invariant _ _ a hy)).comp
      (countableDiagonalHom M).rangeRestrict

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MinimalCyclicExpectation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.CommonTracialPositionData.rightEquiv_transportEquiv _root_.OAI.KadisonKastler.FiniteInnerAverage.algebraApply_sub _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.StandardTracialPosition.conjugation_algebraVector _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.concreteDerivation_apply _root_.OAI.KadisonKastler.concreteDiagonalSequenceUnitary_coe _root_.OAI.KadisonKastler.concreteDiagonalSequence_apply _root_.OAI.KadisonKastler.concreteDiagonalUnitary_coe _root_.OAI.KadisonKastler.concreteTraceEmbedding_inner _root_.OAI.KadisonKastler.concreteTraceLeftAction_embedding _root_.OAI.KadisonKastler.concreteTraceLeftUnitary_coe _root_.OAI.KadisonKastler.concreteTraceRightAction_embedding _root_.OAI.KadisonKastler.concreteTraceRightUnitary_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.matrixLiftUnitaryAt_coe _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.productBoundaryRepresentation_coe _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.rescaledGraphMap_apply _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.dyadicCornerHom_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply _root_.OAI.KadisonSimilarity.predualRestriction_apply _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Explicit retractions through a minimal cyclic space

The compression proof of type-I injectivity gives a specific contractive
retraction. Its coefficients on the minimal cyclic space agree with the
original ambient operator. These identities allow the trace-preserving
finite-stage construction to retain the original vector state.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (N : VonNeumannAlgebra H) (hN : ScalarCenter N)
  (p : AlgebraProjection N) (hp : IsMinimalProjectionIn N p)
  (ξ : H) (hξ : ξ ≠ 0) (hpξ : p.val.val ξ = ξ)

theorem typeICyclicEquiv_symm_norm (T : typeICyclicSpace N ξ →L[ℂ] typeICyclicSpace N ξ) :
    ‖(typeICyclicEquiv hN p hp ξ hξ hpξ).symm T‖ = ‖T‖ := by
  rw [← typeICyclicHom_norm hN p hp ξ hξ hpξ]
  change ‖typeICyclicEquiv hN p hp ξ hξ hpξ
    ((typeICyclicEquiv hN p hp ξ hξ hpξ).symm T)‖ = ‖T‖
  rw [(typeICyclicEquiv hN p hp ξ hξ hpξ).apply_symm_apply]

/-- The concrete ambient-to-algebra retraction supplied by a minimal projection. -/
def minimalCyclicRetraction : (H →L[ℂ] H) →L[ℂ] Algebra N := by
  let e := typeICyclicEquiv hN p hp ξ hξ hpξ
  let F : (H →L[ℂ] H) →ₗ[ℂ] Algebra N :=
    e.symm.toAlgEquiv.toLinearMap.comp (cornerCompression (typeICyclicSpace N ξ))
  exact F.mkContinuous 1 (fun T => by
    change ‖e.symm (cornerCompression (typeICyclicSpace N ξ) T)‖ ≤ 1 * ‖T‖
    rw [typeICyclicEquiv_symm_norm, one_mul]
    exact norm_cornerCompression_le _ T)

@[simp] theorem minimalCyclicRetraction_compression (T : H →L[ℂ] H) :
    typeICyclicHom ξ (minimalCyclicRetraction N hN p hp ξ hξ hpξ T) =
      cornerCompression (typeICyclicSpace N ξ) T := by
  change typeICyclicEquiv hN p hp ξ hξ hpξ
    ((typeICyclicEquiv hN p hp ξ hξ hpξ).symm
      (cornerCompression (typeICyclicSpace N ξ) T)) = _
  exact (typeICyclicEquiv hN p hp ξ hξ hpξ).apply_symm_apply _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularPositiveCone
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

def modularQuadratic (J : H ≃ₗᵢ⋆[ℂ] H) (a : Algebra M) : H →L[ℂ] H :=
  a.val * conjugationOperator J a.val

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_StandardTraceInvariants
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.CommonTracialPositionData.rightEquiv_transportEquiv _root_.OAI.KadisonKastler.FiniteInnerAverage.algebraApply_sub _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.centralVectorDefect_apply _root_.OAI.KadisonKastler.concreteDerivation_apply _root_.OAI.KadisonKastler.concreteDiagonalSequenceUnitary_coe _root_.OAI.KadisonKastler.concreteDiagonalSequence_apply _root_.OAI.KadisonKastler.concreteDiagonalUnitary_coe _root_.OAI.KadisonKastler.conjugateMatrixUnits_entry _root_.OAI.KadisonKastler.conjugateOperatorMap_apply _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.matrixLiftUnitaryAt_coe _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.minimalCyclicRetraction_compression _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.rescaledGraphMap_apply _root_.OAI.KadisonKastler.rightVectorLinear_apply _root_.OAI.KadisonKastler.spatialTransportEquiv_apply _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.typeICyclicHom_apply _root_.OAI.KadisonKastler.typeICyclicOperator_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply _root_.OAI.KadisonSimilarity.predualRestriction_apply _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Scalar invariant vectors in common standard position -/

namespace KadisonKastler

noncomputable section

variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Group G] {M : VonNeumannAlgebra H}

namespace StandardTracialPosition

variable (p : StandardTracialPosition M) (U : G →* unitary (Algebra M))

/-- Restrict the actual product representation to the diagonal group. -/
def diagonalRepresentation : G →* unitary (H →L[ℂ] H) :=
  (productBoundaryRepresentation p U).comp
    { toFun := fun g => (g, g)
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

@[simp]
theorem diagonalRepresentation_vector (g : G) (x : Algebra M) :
    (p.diagonalRepresentation U g : H →L[ℂ] H) (algebraVectorMap M p.vector x) =
      algebraVectorMap M p.vector ((U g : Algebra M) * x * star (U g : Algebra M)) := by
  change ((productBoundaryRepresentation p U (g, g) : H →L[ℂ] H)) (x.val p.vector) = _
  rw [productBoundaryRepresentation_coe]
  change (U g : Algebra M).val
    (conjugationOperator p.conjugation (U g : Algebra M).val (x.val p.vector)) = _
  rw [conjugationOperator_algebraVector M p.conjugation p.vector p.conjugation_algebraVector]
  change (((U g : Algebra M) * (x * star (U g : Algebra M))).val p.vector) = _
  rw [← mul_assoc]
  rfl

end StandardTracialPosition

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TracialSequenceFactor
attribute [-instance] _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The common represented factor for the two tracial sequence inputs -/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

universe u

variable {B : ℕ → Type u} [∀ j, CStarAlgebra (B j)] [∀ j, Nontrivial (B j)]

structure TracialSequenceFactor (τ : ∀ j, FaithfulTracialState (B j)) (ω : Ultrafilter ℕ) where
  H : Type u
  [normedAddCommGroup : NormedAddCommGroup H]
  [innerProductSpace : InnerProductSpace ℂ H]
  [completeSpace : CompleteSpace H]
  algebra : VonNeumannAlgebra H
  factor : Generator.IsII1Factor algebra.toStarSubalgebra
  quotient : VaryingBoundedSequence B →⋆ₐ[ℂ] Algebra algebra
  surjective : Function.Surjective quotient
  trace_limit : ∀ x : VaryingBoundedSequence B,
    Tendsto (fun j => (τ j).toLinearMap (x j)) (ω : Filter ℕ)
    (𝓝 ((concreteFactorTrace factor).toLinearMap (quotient x)))

attribute [instance] TracialSequenceFactor.normedAddCommGroup
  TracialSequenceFactor.innerProductSpace TracialSequenceFactor.completeSpace

attribute [local irreducible] tracialSequenceAlgebra

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProjectionFamilySpaces
attribute [-instance] _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Closed spaces attached to a family of projection cuts

The remaining left corner and the simultaneous commutation space are
intersections of concrete operator kernels. Their projections therefore
exist also for infinite families.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

def projectionFamilyRemainderSpace (S : Set (AlgebraProjection M)) : ClosedSubmodule ℂ H :=
  ⨅ p : S, operatorKernelClosed p.val.val.val

def projectionFamilyCommutationSpace (J : H ≃ₗᵢ⋆[ℂ] H)
    (S : Set (AlgebraProjection M)) : ClosedSubmodule ℂ H :=
  ⨅ p : S, operatorKernelClosed (p.val.val.val-conjugationOperator J p.val.val.val)

@[simp] theorem mem_projectionFamilyRemainderSpace (S : Set (AlgebraProjection M)) (x : H) :
    x ∈ projectionFamilyRemainderSpace S ↔ ∀ p ∈ S, p.val.val x=0 := by
  simp only [projectionFamilyRemainderSpace,ClosedSubmodule.mem_iInf,operatorKernelClosed,
    ClosedSubmodule.mem_mk,LinearMap.mem_ker,ContinuousLinearMap.coe_coe,Subtype.forall]

@[simp] theorem mem_projectionFamilyCommutationSpace (J : H ≃ₗᵢ⋆[ℂ] H)
    (S : Set (AlgebraProjection M)) (x : H) :
    x ∈ projectionFamilyCommutationSpace J S ↔
      ∀ p ∈ S, p.val.val x=conjugationOperator J p.val.val x := by
  simp only [projectionFamilyCommutationSpace,ClosedSubmodule.mem_iInf,operatorKernelClosed,
    ClosedSubmodule.mem_mk,LinearMap.mem_ker,ContinuousLinearMap.coe_coe,Subtype.forall,
    sub_apply,sub_eq_zero]

def projectionFamilyPinching (J : H ≃ₗᵢ⋆[ℂ] H) (S : Set (AlgebraProjection M)) : H →L[ℂ] H :=
  (projectionFamilyCommutationSpace J S).toSubmodule.starProjection

end

end KadisonKastler

end OAI
end


