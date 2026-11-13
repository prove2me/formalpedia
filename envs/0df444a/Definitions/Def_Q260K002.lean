-- Prove2me | Definitions.Def_Q260K002
-- name    : Q260K002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T04:34:11.055771+00:00
-- url     : https://prove2.me/theorems/ee457dcc-6ad4-41a1-ad23-ca8a987c36e1
-- title:
--   Definitions bundle Q260K002 of the split of OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 196 declarations of OpenAI's Lean: 67 definitions, 3 inductive types or structures, 1 instance and 125 theorems. The definitions and types are `OAI.IsUnital.toCStarAlgebra`, `OAI.KadisonKastler.Algebra`, `OAI.KadisonKastler.BoundedSequence`, `OAI.KadisonKastler.CountableHilbertSum`, `OAI.KadisonKastler.FaithfulTracialState`, `OAI.KadisonKastler.FullMatrixCorner`, `OAI.KadisonKastler.FullMatrixCorner.column`, `OAI.KadisonKastler.FullMatrixCorner.columnLinear`, `OAI.KadisonKastler.FullMatrixCorner.coordinates`, `OAI.KadisonKastler.FullMatrixCorner.inflateHom`, `OAI.KadisonKastler.FullMatrixCorner.inflateUnitary`, `OAI.KadisonKastler.NearInclusion`, `OAI.KadisonKastler.PublishedKaplanskyDensity`, `OAI.KadisonKastler.ScalarCenter`, `OAI.KadisonKastler.ScalarInvariantMean`, `OAI.KadisonKastler.ScalarInvariantMean.coefficient`, `OAI.KadisonKastler.ScalarInvariantMean.operatorValue`, `OAI.KadisonKastler.ScalarInvariantMean.testFunctional`, `OAI.KadisonKastler.ScalarLInfinity`, `OAI.KadisonKastler.TomitaGraphHilbert`, `OAI.KadisonKastler.VaryingBoundedSequence`, `OAI.KadisonKastler.blockDiagonal`, `OAI.KadisonKastler.blockFlip`, `OAI.KadisonKastler.blockOffDiagonal`, `OAI.KadisonKastler.boundedSequenceEval`, `OAI.KadisonKastler.coefficientMatrixMap`, `OAI.KadisonKastler.conjugationOperator`, `OAI.KadisonKastler.conjugationUnitary`, `OAI.KadisonKastler.cornerCompression`, `OAI.KadisonKastler.cornerExtension`, `OAI.KadisonKastler.diagonalStarAlgHom`, `OAI.KadisonKastler.entryMatrixAlgebra`, `OAI.KadisonKastler.finiteAverage`, `OAI.KadisonKastler.finiteTraceOrder`, `OAI.KadisonKastler.finiteUnitaryAverage`, `OAI.KadisonKastler.generatedVonNeumannAlgebra`, `OAI.KadisonKastler.hilbertExtendLeft`, `OAI.KadisonKastler.hilbertExtendRight`, `OAI.KadisonKastler.hilbertMatrix`, `OAI.KadisonKastler.hilbertMatrixHom` and 30 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `FactorGeneration_Bicommutant`, `KadisonKastler_Algebra`, `KadisonKastler_Amenable`, `KadisonKastler_Basic`, `KadisonKastler_BlockMatrices`, `KadisonKastler_BoundedSequence`, `KadisonKastler_CanonicalAmplification`, `KadisonKastler_ClippedCoefficients`, `KadisonKastler_CommonRightAction`, `KadisonKastler_CommonRightProjection`, `KadisonKastler_ConcreteFiniteTrace`, `KadisonKastler_ConjugateRightAlgebra`, `KadisonKastler_FaithfulRepresentation`, `KadisonKastler_FiniteAveraging`, `KadisonKastler_FiniteSignFourthMoment`, `KadisonKastler_FreeHaarClosure`, `KadisonKastler_HilbertMatrix`, `KadisonKastler_InfiniteCornerInflation`, `KadisonKastler_InvariantOperatorMean`, `KadisonKastler_KaplanskyDensity`, `KadisonKastler_KaplanskyRational`, `KadisonKastler_KaplanskyResolvent`, `KadisonKastler_KaplanskySelfAdjoint`, `KadisonKastler_KaplanskySelfAdjointBall`, `KadisonKastler_KaplanskyTransform`, `KadisonKastler_MatrixOperatorGeneration`, `KadisonKastler_MatrixVonNeumann`, `KadisonKastler_NormClosureUnitBall`, `KadisonKastler_PoissonKernelFormula`, `KadisonKastler_ProductBoundaryCocycle`, `KadisonKastler_ProjectionFamilySpaces`, `KadisonKastler_PublishedCentralDecomposition`, `KadisonKastler_PublishedFock`, `KadisonKastler_PublishedKaplansky`, `KadisonKastler_RectangularHilbert`, `KadisonKastler_RegularCoreMatrixData`, `KadisonKastler_RepresentedCorner`, `KadisonKastler_RescaledTomitaGraph`, `KadisonKastler_ScalarBoundaryMean`, `KadisonKastler_TraceLimits`, `KadisonKastler_TracialCauchySchwarz`, `KadisonKastler_TracialHilbertConjugation`, `KadisonKastler_TracialProducts`, `KadisonKastler_VaryingSequence`.
--
--   **Imports.** It imports the published bundle `Def_StrongKadisonKastler`; the bundles `OAIQ075A008` and `OAIQ075A009` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q260K010`, `Q260K011`, `Q260K012`, `Q260K013`, `Q260K014` and `Q260K015`; the statements `OAI_KadisonKastler_FullMatrixCorner_exists_localized_embedding`, `OAI.KadisonKastler.PreservesJordan.multiplicative_of_close_of_II1`, `OAI.KadisonKastler.cochain_coboundary_weak_limit`, `OAI_KadisonKastler_coisometry_norm_le`, `OAI.KadisonKastler.constructed_finiteFactor_spatial_of_near_starEquiv`, `OAI_KadisonKastler_exists_ambient_product_state_of_simple`, `OAI_KadisonKastler_exists_commutant_projection_of_finite_gap`, `OAI.KadisonKastler.exists_localized_unitary_finiteStage_embedding`, `OAI_KadisonKastler_exists_localized_unitary_matrixUnits_embedding`, `OAI.KadisonKastler.exists_original_irreducible_matrix_algebra`, `OAI_KadisonKastler_exists_selfAdjoint_split_of_factor`, `OAI.KadisonKastler.exists_selfAdjoint_split_of_factor_commutant`, `OAI_KadisonKastler_exists_unitary_approx_of_kkDistance`, `OAI.KadisonKastler.exists_unitary_approx_of_nearInclusion`, `OAI.KadisonKastler.exists_unitary_embedding_of_invariant_group`, `OAI_KadisonKastler_exists_unitary_embedding_of_invariant_group_in_algebra`, `OAI.KadisonKastler.exists_unitary_finiteMatrix_embedding`, `OAI.KadisonKastler.exists_unitary_invariantGroup_embedding_in_algebra`, `OAI.KadisonKastler.extension_implementer_mem_of_spatial_split`, `OAI.KadisonKastler.factor_of_extreme_signed_derivation_extension`, `OAI.KadisonKastler.finiteFactor_isPrimeAlgebra`, `OAI_KadisonKastler_finite_factor_of_near_II1`, `OAI.KadisonKastler.map_star_square_of_map_unitary`, `OAI.KadisonKastler.nearInclusion_of_representation_comparison`, `OAI.KadisonKastler.opNorm_le_of_finite_covariance_families`, `OAI.KadisonKastler.preservesJordan_of_map_unitary`, `OAI.KadisonKastler.relative_irreducibility_of_near_increasing_matrices`, `OAI.KadisonKastler.representationVonNeumannAlgebra_eq_generated`, `OAI.KadisonKastler.representation_joint_eq_center_commutant`, `OAI.KadisonKastler.reverse_nearInclusion_of_representation_comparison`, `OAI.KadisonKastler.right_module_of_factor_diagonal_norm`, `OAI.KadisonKastler.scalar_center_of_near_II1`, `OAI.KadisonKastler.spatialTransportAlgebra_trans`, `OAI.KadisonKastler.transported_algebra_field_decompose`, `OAI.KadisonKastler.transported_commutant_fields_of_field_inclusion` and `OAI.KadisonKastler.vector_state_eq_trace_of_relative_central`; the proofs of `OAI.KadisonKastler.cochain_coboundary_weak_limit`, `OAI.KadisonKastler.map_star_square_of_map_unitary`, `OAI.KadisonKastler.preservesJordan_of_map_unitary`, `OAI.KadisonKastler.representationVonNeumannAlgebra_eq_generated` and `OAI.KadisonKastler.representation_joint_eq_center_commutant`.
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
import Definitions.Def_StrongKadisonKastler
import Definitions.Def_OAIQ075A008
import Definitions.Def_OAIQ075A009

section
-- module Solutions.OAIQ075_KS.Compat
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.CStarCorner.instIsUnitalSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.UltrapowerBridge.instStarTracialQuotient
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434

/-- d13f23b's `IsUnital.toCStarAlgebra`: a non-unital C⋆-algebra with an identity is a C⋆-algebra (weak infiniteness, q246). -/
@[instance_reducible]
noncomputable def IsUnital.toCStarAlgebra {A : Type*} [NonUnitalCStarAlgebra A] [IsUnital A] :
    CStarAlgebra A :=
  letI : NormedRing A := IsUnital.toNormedRing
  letI : Algebra ℂ A := Algebra.ofModule (fun r x y => smul_mul_assoc r x y)
    (fun r x y => mul_smul_comm r x y)
  letI : NormedAlgebra ℂ A := { (inferInstance : Algebra ℂ A) with
    norm_smul_le := fun r x => norm_smul_le r x }
  { (inferInstance : NormedRing A), (inferInstance : NormedAlgebra ℂ A) with
    toStarRing := inferInstance
    toCompleteSpace := inferInstance
    toCStarRing := inferInstance
    toStarModule := inferInstance }
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_Bicommutant
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! Finite diagonal amplification and the projection onto a simultaneous
operator orbit. These are the analytic ingredients of the bicommutant theorem. -/

/-! The double commutant theorem for actual unital star subalgebras of B(H).
Finite simultaneous strong approximation constructs a WOT-convergent net.
No bounded approximation or separable-predual theorem is claimed here. -/

/-! Countable algebraic generators give a separable star algebra using only
continuous addition and scalar multiplication. No multiplication continuity is
required, so the result applies to the two-norm on a tracial quotient. -/

theorem countable_monoid_closure {A : Type*} [Monoid A] {s : Set A}
    (hs : s.Countable) : (Submonoid.closure s : Set A).Countable := by
  let : Countable s := hs.to_subtype
  let : Countable (FreeMonoid s) := inferInstanceAs (Countable (List s))
  rw [Submonoid.closure_eq_mrange, MonoidHom.coe_mrange]
  exact Set.countable_range _

theorem separable_countable_star_adjoin {A : Type*} [Ring A] [StarRing A]
    [Algebra ℂ A] [StarModule ℂ A] [TopologicalSpace A]
    [ContinuousAdd A] [ContinuousSMul ℂ A] {s : Set A} (hs : s.Countable) :
    TopologicalSpace.IsSeparable (StarAlgebra.adjoin ℂ s : Set A) := by
  change TopologicalSpace.IsSeparable
    ((StarAlgebra.adjoin ℂ s).toSubalgebra.toSubmodule : Set A)
  rw [StarAlgebra.adjoin_eq_span]
  apply TopologicalSpace.IsSeparable.span
  apply Set.Countable.isSeparable
  apply countable_monoid_closure
  exact hs.union (by simpa only [Set.image_star] using hs.image star)

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_Basic
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.PopaCorner.instOne _root_.OAI.UltrapowerBridge.instStarTracialQuotient
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
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

@[simp] theorem mem_unitBall (M : VonNeumannAlgebra H) (x : H →L[ℂ] H) :
    x ∈ unitBall M ↔ x ∈ M ∧ ‖x‖ ≤ 1 := Iff.rfl

@[simp] theorem zero_mem_unitBall (M : VonNeumannAlgebra H) :
    0 ∈ unitBall M := ⟨zero_mem M, by simp⟩

@[simp] theorem unitaryConj_one (x : H →L[ℂ] H) : unitaryConj 1 x = x := by
  simp [unitaryConj]

@[simp] theorem norm_unitaryConj (v : unitary (H →L[ℂ] H)) (x : H →L[ℂ] H) :
    ‖unitaryConj v x‖ = ‖x‖ := by
  simp [unitaryConj, ← Unitary.coe_star]

@[simp] theorem unitaryConj_star_unitaryConj (v : unitary (H →L[ℂ] H))
    (x : H →L[ℂ] H) : unitaryConj (star v) (unitaryConj v x) = x := by
  simp only [unitaryConj, Unitary.coe_star, star_star]
  calc
    star (v : H →L[ℂ] H) * ((v : H →L[ℂ] H) * x * star (v : H →L[ℂ] H)) * v =
        (star (v : H →L[ℂ] H) * v) * x * (star (v : H →L[ℂ] H) * v) := by
      noncomm_ring
    _ = x := by rw [Unitary.star_mul_self_of_mem v.property]; simp

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_Algebra
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.PopaCorner.instCStarAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# Norm topology on concrete von Neumann algebras

The bicommutant definition used by Mathlib implies norm closedness directly.
This supplies the complete C*-algebra structures needed for matrix norms and
for the perturbation maps in the manuscript's UCP criterion.
-/

namespace KadisonKastler

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem isClosed_algebra (M : VonNeumannAlgebra H) :
    IsClosed (M : Set (H →L[ℂ] H)) := by
  rw [← M.centralizer_centralizer]
  exact Set.isClosed_centralizer _

/-- The ordinary complete C*-algebra underlying the concrete algebra. -/
abbrev Algebra (M : VonNeumannAlgebra H) := M.toStarSubalgebra

noncomputable instance algebraCStarAlgebra (M : VonNeumannAlgebra H) :
    CStarAlgebra (Algebra M) :=
  StarSubalgebra.cstarAlgebra M.toStarSubalgebra (h_closed := isClosed_algebra M)

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_Amenable
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
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

/-- The strict near-inclusion convention of the published input. Approximants
belong to the algebra, but need not lie in its unit ball. -/
def NearInclusion (M N : VonNeumannAlgebra H) (γ : ℝ) : Prop :=
  ∃ γ' : ℝ, γ' < γ ∧ ∀ x ∈ unitBall M,
    Metric.infDist x (N : Set (H →L[ℂ] H)) ≤ γ'

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FaithfulRepresentation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient
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

/-- The scalar isometry underlying a faithful representation. -/
theorem injective_starAlgHom_norm (φ : A →⋆ₐ[ℂ] B) (hφ : Function.Injective φ)
    (a : A) : ‖φ a‖ = ‖a‖ :=
  NonUnitalStarAlgHom.norm_map φ hφ a

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BlockMatrices
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.UltrapowerBridge.instStarTracialQuotient
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# Two-by-two C⋆-matrix norm formulas

The diagonal embedding is a faithful star representation, so its norm is
the supremum norm. Multiplying by the flip unitary gives the corresponding
off-diagonal formula.
-/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The diagonal star representation of a finite product of C⋆-algebras. -/
def diagonalStarAlgHom (n : Type*) [Fintype n] [DecidableEq n] :
    (n → A) →⋆ₐ[ℂ] CStarMatrix n n A :=
  { Matrix.diagonalAlgHom ℂ with
    map_star' d := by
      ext i j
      change (if i = j then star (d i) else 0) =
        star (if j = i then d j else 0)
      by_cases hij : i = j
      · subst j
        simp
      · simp [hij, Ne.symm hij] }

omit [PartialOrder A] [StarOrderedRing A] in
@[simp]
theorem diagonalStarAlgHom_apply (n : Type*) [Fintype n] [DecidableEq n]
    (d : n → A) (i j : n) :
    diagonalStarAlgHom n d i j = if i = j then d i else 0 := rfl

omit [PartialOrder A] [StarOrderedRing A] in
theorem diagonalStarAlgHom_injective (n : Type*) [Fintype n] [DecidableEq n] :
    Function.Injective (diagonalStarAlgHom (A := A) n) := by
  intro d e h
  funext i
  have hi := congrArg (fun M : CStarMatrix n n A => M i i) h
  simpa only [diagonalStarAlgHom_apply, ↓reduceIte] using hi

/-- The operator norm of a diagonal matrix is the finite-product norm. -/
theorem norm_diagonalStarAlgHom (n : Type*) [Fintype n] [DecidableEq n] (d : n → A) :
    ‖diagonalStarAlgHom n d‖ = ‖d‖ :=
  injective_starAlgHom_norm _ (diagonalStarAlgHom_injective n) d

/-- The diagonal matrix with entries `a` and `b`. -/
def blockDiagonal (a b : A) : CStarMatrix (Fin 2) (Fin 2) A :=
  diagonalStarAlgHom (Fin 2) ![a, b]

theorem norm_blockDiagonal (a b : A) : ‖blockDiagonal a b‖ = max ‖a‖ ‖b‖ := by
  rw [blockDiagonal, norm_diagonalStarAlgHom]
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (le_trans (norm_nonneg a) (le_max_left _ _))).mpr
    intro i
    fin_cases i <;> simp
  · exact max_le (norm_le_pi_norm ![a, b] 0) (norm_le_pi_norm ![a, b] 1)

/-- The unitary that swaps the two coordinates. -/
def blockFlip : unitary (CStarMatrix (Fin 2) (Fin 2) A) :=
  let S : CStarMatrix (Fin 2) (Fin 2) A := fun i j => if i = j then 0 else 1
  ⟨S, by
    change star S * S = 1 ∧ S * star S = 1
    constructor <;> ext i j
    all_goals
      simp only [CStarMatrix.mul_apply, CStarMatrix.star_apply, Fin.sum_univ_two]
      fin_cases i <;> fin_cases j <;> simp [S]⟩

/-- The off-diagonal matrix with entries `a` and `b`. -/
def blockOffDiagonal (a b : A) : CStarMatrix (Fin 2) (Fin 2) A :=
  !![0, a; b, 0]

omit [PartialOrder A] [StarOrderedRing A] in
theorem blockOffDiagonal_eq_mul_flip (a b : A) :
    blockOffDiagonal a b =
      blockDiagonal a b * (blockFlip (A := A) : CStarMatrix (Fin 2) (Fin 2) A) := by
  ext i j
  simp only [CStarMatrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;>
    simp [blockOffDiagonal, blockDiagonal, blockFlip]

theorem norm_blockOffDiagonal (a b : A) : ‖blockOffDiagonal a b‖ = max ‖a‖ ‖b‖ := by
  rw [blockOffDiagonal_eq_mul_flip, CStarRing.norm_mul_coe_unitary, norm_blockDiagonal]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_HilbertMatrix
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.UltrapowerBridge.instStarTracialQuotient
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# Operator-valued matrices on finite Hilbert direct sums

This identifies the abstract C⋆-matrix norm with the operator norm on
the finite Hilbert direct sum, through a faithful star representation.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {n : Type*} [Fintype n] [DecidableEq n]

local instance hilbertMatrixOperatorPartialOrder : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
local instance hilbertMatrixOperatorStarOrderedRing : StarOrderedRing (H →L[ℂ] H) := CStarAlgebra.spectralOrderedRing _

/-- The action of an operator-valued matrix on a finite Hilbert direct sum. -/
def hilbertMatrix (M : CStarMatrix n n (H →L[ℂ] H)) :
    Generator.FiniteHilbert n H →L[ℂ] Generator.FiniteHilbert n H :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : n => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i =>
      ∑ j, (M i j).comp (PiLp.proj 2 (fun _ : n => H) j)))

omit [CompleteSpace H] [DecidableEq n] in
@[simp]
theorem hilbertMatrix_apply (M : CStarMatrix n n (H →L[ℂ] H))
    (x : Generator.FiniteHilbert n H) (i : n) :
    hilbertMatrix M x i = ∑ j, M i j (x j) := by
  simp [hilbertMatrix]

omit [CompleteSpace H] [DecidableEq n] in
theorem hilbertMatrix_mul (M N : CStarMatrix n n (H →L[ℂ] H)) :
    hilbertMatrix (M * N) = hilbertMatrix M * hilbertMatrix N := by
  ext x i
  simp only [hilbertMatrix_apply, CStarMatrix.mul_apply, sum_apply,
    mul_apply_eq_comp, map_sum]
  rw [Finset.sum_comm]

omit [DecidableEq n] in
theorem hilbertMatrix_star (M : CStarMatrix n n (H →L[ℂ] H)) :
    hilbertMatrix (star M) = star (hilbertMatrix M) := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  simp only [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
    PiLp.inner_apply, hilbertMatrix_apply, CStarMatrix.star_apply, inner_sum, sum_inner]
  rw [Finset.sum_comm]

/-- The usual matrix action is a star representation. -/
def hilbertMatrixHom : CStarMatrix n n (H →L[ℂ] H) →⋆ₐ[ℂ]
    (Generator.FiniteHilbert n H →L[ℂ] Generator.FiniteHilbert n H) where
  toFun := hilbertMatrix
  map_one' := by
    ext x i
    simp only [hilbertMatrix_apply, CStarMatrix.one_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Ne.symm hji]
    · simp
  map_mul' := hilbertMatrix_mul
  map_zero' := by ext x i; simp [hilbertMatrix_apply]
  map_add' M N := by
    ext x i
    simp [hilbertMatrix_apply, CStarMatrix.add_apply, Finset.sum_add_distrib]
  commutes' z := by
    ext x i
    simp only [hilbertMatrix_apply, CStarMatrix.algebraMap_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Ne.symm hji]
    · simp
  map_star' := hilbertMatrix_star

theorem hilbertMatrixHom_injective : Function.Injective (hilbertMatrixHom (H := H) (n := n)) := by
  intro M N hMN
  ext i j x
  have h := congrArg (fun T : Generator.FiniteHilbert n H →L[ℂ] Generator.FiniteHilbert n H =>
    T (Generator.tupleSingle j x) i) hMN
  simpa [hilbertMatrixHom, hilbertMatrix_apply, Generator.tupleSingle_apply, Pi.single_apply, apply_ite] using h

/-- Abstract C⋆-matrix norms are the concrete direct-sum operator norms. -/
theorem norm_hilbertMatrix (M : CStarMatrix n n (H →L[ℂ] H)) : ‖hilbertMatrix M‖ = ‖M‖ :=
  NonUnitalStarAlgHom.norm_map hilbertMatrixHom hilbertMatrixHom_injective M

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RectangularHilbert
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Rectangular operator matrices on finite Hilbert sums -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {m n : Type*} [Fintype m] [Fintype n]

local instance rectangularHilbertOperatorOrder_radea18_1 : PartialOrder (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrder _
local instance rectangularHilbertOperatorStarOrder_radea18_1 : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _
def rectangularHilbertMatrix (M : CStarMatrix m n (H →L[ℂ] H)) :
    Generator.FiniteHilbert n H →L[ℂ] Generator.FiniteHilbert m H :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : m => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i =>
      ∑ j, (M i j).comp (PiLp.proj 2 (fun _ : n => H) j)))

omit [CompleteSpace H] [Fintype m] in
@[simp]
theorem rectangularHilbertMatrix_apply (M : CStarMatrix m n (H →L[ℂ] H))
    (x : Generator.FiniteHilbert n H) (i : m) :
    rectangularHilbertMatrix M x i = ∑ j, M i j (x j) := by
  simp [rectangularHilbertMatrix]

def hilbertExtendLeft (x : Generator.FiniteHilbert m H) : Generator.FiniteHilbert (m ⊕ n) H :=
  WithLp.toLp 2 (Sum.elim x fun _ => 0)

def hilbertExtendRight (x : Generator.FiniteHilbert n H) : Generator.FiniteHilbert (m ⊕ n) H :=
  WithLp.toLp 2 (Sum.elim (fun _ => 0) x)

omit [CompleteSpace H] [InnerProductSpace ℂ H] in
@[simp]
theorem norm_hilbertExtendLeft (x : Generator.FiniteHilbert m H) :
    ‖hilbertExtendLeft (n := n) x‖ = ‖x‖ := by
  simp [PiLp.norm_eq_of_L2, hilbertExtendLeft, Fintype.sum_sum_type]

omit [CompleteSpace H] [InnerProductSpace ℂ H] in
@[simp]
theorem norm_hilbertExtendRight (x : Generator.FiniteHilbert n H) :
    ‖hilbertExtendRight (m := m) x‖ = ‖x‖ := by
  simp [PiLp.norm_eq_of_L2, hilbertExtendRight, Fintype.sum_sum_type]

omit [CompleteSpace H] in
@[simp]
theorem norm_tupleSingle [DecidableEq n] (i : n) (x : H) :
    ‖Generator.tupleSingle i x‖ = ‖x‖ := by
  change ‖PiLp.single (β := fun _ : n => H) 2 i x‖ = ‖x‖
  exact PiLp.norm_single 2 (fun _ : n => H) i x

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteAveraging
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Finite averages of unitary conjugations -/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {G : Type*} [Fintype G] [Nonempty G]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- Uniform average over a nonempty finite set. -/
def finiteAverage (f : G → V) : V := (Fintype.card G : ℂ)⁻¹ • ∑ g, f g

@[simp]
theorem finiteAverage_const (v : V) : finiteAverage (fun _ : G => v) = v := by
  simp [finiteAverage, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, Fintype.card_ne_zero]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Average over the image of a finite unitary representation. -/
def finiteUnitaryAverage (π : G → unitary (H →L[ℂ] H)) (h : H →L[ℂ] H) : H →L[ℂ] H :=
  finiteAverage (fun g => unitaryConj (π g) h)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PublishedFock
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# The published faithful free-product representation input

The only input here is the standard faithful reduced-free-product
representation of a scalar-free family with a faithful tracial state.
The creation, annihilation and preservation formulas are those of
Ricard–Xu, *Khintchine type inequalities for reduced free products and
applications*, J. reine angew. Math. 599 (2006), §1 and Fact 2.6
(arXiv:math/0505302v2, printed pp. 3 and 7).

We use only finite diagonal algebras with equal trace projections. The
input supplies their representation and structural identities, without
assuming any projection-word norm estimate. The latter has been proved
in `FreeProjectionWords` from those identities.
-/

namespace KadisonKastler

open Finset

noncomputable section

universe u

/-- The state data needed for faithful reduced free products. -/
structure FaithfulTracialState (B : Type u) [CStarAlgebra B] where
  toLinearMap : B →ₗ[ℂ] ℂ
  map_one : toLinearMap 1 = 1
  positive : ∀ x, 0 ≤ (toLinearMap (star x * x)).re
  positive_im : ∀ x, (toLinearMap (star x * x)).im = 0
  faithful : ∀ x, toLinearMap (star x * x) = 0 → x = 0
  tracial : ∀ x y, toLinearMap (x * y) = toLinearMap (y * x)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BoundedSequence
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.UltrapowerBridge.instStarTracialQuotient
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# Bounded sequences, spectral clipping and trace-to-strong transfer

The sequence algebra is the ordinary C*-algebra of bounded functions on
the discrete natural numbers. Evaluation commutes with the spectral
cutoff. A trace quotient therefore kills the discarded part as soon as
the quotient norm satisfies the desired cutoff bound.
-/

namespace KadisonKastler

open Filter
open scoped Topology BoundedContinuousFunction

noncomputable section

abbrev BoundedSequence (B : Type*) [CStarAlgebra B] := ℕ →ᵇ B

def boundedSequenceEval {B : Type*} [CStarAlgebra B] (j : ℕ) :
    BoundedSequence B →⋆ₐ[ℂ] B where
  toFun x := x j
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

@[simp]
theorem boundedSequenceEval_apply {B : Type*} [CStarAlgebra B]
    (j : ℕ) (x : BoundedSequence B) : boundedSequenceEval j x = x j := rfl

/-- The tracial two-seminorm, on the faithful tracial algebra in use. -/
def traceTwoNorm {B : Type*} [CStarAlgebra B] (τ : FaithfulTracialState B) (x : B) : ℝ :=
  Real.sqrt ((τ.toLinearMap (star x * x)).re)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RepresentedCorner
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
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

/-- Extension by zero on the orthogonal complement. -/
def cornerExtension : (E →L[ℂ] E) →ₗ[ℂ] (H →L[ℂ] H) where
  toFun T := E.subtypeL.comp (T.comp E.orthogonalProjectionOnto)
  map_add' T S := by ext x; rfl
  map_smul' c T := by ext x; rfl

/-- Compression of an arbitrary ambient operator. -/
def cornerCompression : (H →L[ℂ] H) →ₗ[ℂ] (E →L[ℂ] E) where
  toFun T := E.orthogonalProjectionOnto.comp (T.comp E.subtypeL)
  map_add' T S := by ext x; simp
  map_smul' c T := by ext x; simp

@[simp] theorem cornerExtension_apply (T : E →L[ℂ] E) (x : H) :
    cornerExtension E T x = (T (E.orthogonalProjectionOnto x) : H) := rfl

@[simp] theorem cornerCompression_apply (T : H →L[ℂ] H) (x : E) :
    cornerCompression E T x = E.orthogonalProjectionOnto (T x) := rfl

@[simp] theorem cornerCompression_extension (T : E →L[ℂ] E) :
    cornerCompression E (cornerExtension E T) = T := by
  ext x
  simp only [cornerCompression_apply, cornerExtension_apply,
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]

theorem norm_cornerCompression_le (T : H →L[ℂ] H) : ‖cornerCompression E T‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
  intro x
  exact (E.norm_orthogonalProjectionOnto_apply_le (T x)).trans (T.le_opNorm x)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_InfiniteCornerInflation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
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

section Diagonal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

abbrev CountableHilbertSum (E : Type*) [NormedAddCommGroup E] := lp (fun _ : ℕ => E) 2

def l2DiagonalLinear (T : E →L[ℂ] E) :
    CountableHilbertSum E →ₗ[ℂ] CountableHilbertSum E where
  toFun x := ⟨fun i => T (x i),
    ((lp.memℓp x).norm.const_mul ‖T‖).mono (fun i => T.le_opNorm (x i))⟩
  map_add' x y := by ext i; exact map_add T (x i) (y i)
  map_smul' c x := by ext i; exact map_smul T c (x i)

theorem norm_l2DiagonalLinear_le (T : E →L[ℂ] E) (x : CountableHilbertSum E) :
    ‖l2DiagonalLinear T x‖ ≤ ‖T‖ * ‖x‖ := by
  have h : ‖l2DiagonalLinear T x‖ ≤ ‖(‖T‖ : ℝ) • x‖ :=
    lp.norm_mono (by norm_num) (fun i => by
      change ‖T (x i)‖ ≤ ‖(‖T‖ : ℝ) • x i‖
      simpa only [lp.coeFn_smul, Pi.smul_apply, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg T)] using T.le_opNorm (x i))
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg T)] using h

def l2Diagonal (T : E →L[ℂ] E) : CountableHilbertSum E →L[ℂ] CountableHilbertSum E :=
  (l2DiagonalLinear T).mkContinuous ‖T‖ (norm_l2DiagonalLinear_le T)

@[simp] theorem l2Diagonal_apply (T : E →L[ℂ] E) (x : CountableHilbertSum E) (i : ℕ) :
    l2Diagonal T x i = T (x i) := rfl

@[simp] theorem l2Diagonal_single (T : E →L[ℂ] E) (i : ℕ) (x : E) :
    l2Diagonal T (lp.single 2 i x) = lp.single 2 i (T x) := by
  ext j
  by_cases h : j = i <;> simp [l2Diagonal_apply, lp.single_apply, h]

variable [CompleteSpace E]

theorem l2Diagonal_star (T : E →L[ℂ] E) :
    l2Diagonal (star T) = star (l2Diagonal T) := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  simp only [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
    lp.inner_eq_tsum, l2Diagonal_apply]

def l2DiagonalHom : (E →L[ℂ] E) →⋆ₐ[ℂ]
    (CountableHilbertSum E →L[ℂ] CountableHilbertSum E) where
  toFun := l2Diagonal
  map_one' := by ext x i; rfl
  map_mul' T S := by ext x i; rfl
  map_zero' := by ext x i; rfl
  map_add' T S := by ext x i; rfl
  commutes' c := by ext x i; rfl
  map_star' := l2Diagonal_star

end Diagonal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (E : Submodule ℂ H) [CompleteSpace E]

/-- Actual countable matrix units with initial corner `E` and strong sum one. -/
structure FullMatrixCorner where
  entry : ℕ → ℕ → (H →L[ℂ] H)
  star_entry : ∀ i j, star (entry i j) = entry j i
  mul_entry : ∀ i j k l, entry i j * entry k l = if j = k then entry i l else 0
  zero_zero : entry 0 0 = E.starProjection
  total : ∀ x : H, HasSum (fun i => entry i i x) x

namespace FullMatrixCorner

variable {E} (F : FullMatrixCorner E)

def columnLinear (i : ℕ) : E →ₗ[ℂ] H := (F.entry i 0).toLinearMap.comp E.subtype

theorem inner_columns (i j : ℕ) (x y : E) :
    inner ℂ (F.entry i 0 x) (F.entry j 0 y) =
      if i = j then inner ℂ x y else 0 := by
  calc
    inner ℂ (F.entry i 0 x) (F.entry j 0 y) =
        inner ℂ (x : H) ((star (F.entry i 0) * F.entry j 0) (y : H)) := by
      rw [mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
        ContinuousLinearMap.adjoint_inner_right]
    _ = if i = j then inner ℂ x y else 0 := by
      rw [F.star_entry, F.mul_entry]
      split_ifs with h
      · rw [F.zero_zero, Submodule.starProjection_mem_subspace_eq_self]
        rfl
      · simp

def column (i : ℕ) : E →ₗᵢ[ℂ] H where
  toLinearMap := F.columnLinear i
  norm_map' := (LinearMap.norm_map_iff_inner_map_map (F.columnLinear i)).mpr
    (fun x y => by simpa [columnLinear] using
      F.inner_columns i i x y)

@[simp] theorem column_apply (i : ℕ) (x : E) : F.column i x = F.entry i 0 x := rfl

theorem columns_orthogonal : OrthogonalFamily ℂ (fun _ : ℕ => E) F.column := by
  intro i j hij x y
  simpa only [column_apply, ite_eq_right hij] using F.inner_columns i j x y

theorem diagonal_apply (i : ℕ) (x : H) :
    F.entry i i x = F.column i (E.orthogonalProjectionOnto (F.entry 0 i x)) := by
  change F.entry i i x = (F.entry i 0 * E.starProjection * F.entry 0 i) x
  rw [← F.zero_zero, F.mul_entry, ite_eq_left rfl, F.mul_entry, ite_eq_left rfl]

theorem columns_total :
    ⊤ ≤ (⨆ i, LinearMap.range (F.column i).toLinearMap).topologicalClosure := by
  intro x _
  apply mem_closure_of_tendsto (F.total x)
  apply Eventually.of_forall
  intro s
  apply Submodule.sum_mem
  intro i _
  apply le_iSup (fun j => LinearMap.range (F.column j).toLinearMap) i
  exact ⟨E.orthogonalProjectionOnto (F.entry 0 i x), (F.diagonal_apply i x).symm⟩

theorem hilbertSum : IsHilbertSum ℂ (fun _ : ℕ => E) F.column :=
  IsHilbertSum.mk F.columns_orthogonal F.columns_total

/-- The coordinate equivalence obtained from the actual matrix units. -/
def coordinates : H ≃ₗᵢ[ℂ] CountableHilbertSum E := F.hilbertSum.linearIsometryEquiv

@[simp] theorem coordinates_symm_single (i : ℕ) (x : E) :
    F.coordinates.symm (lp.single 2 i x) = F.column i x :=
  F.hilbertSum.linearIsometryEquiv_symm_apply_single x

@[simp] theorem coordinates_column (i : ℕ) (x : E) :
    F.coordinates (F.column i x) = lp.single 2 i x := by
  rw [← F.coordinates_symm_single, F.coordinates.apply_symm_apply]

/-- Inflate a corner operator by the same operator on every matrix summand. -/
def inflateHom : (E →L[ℂ] E) →⋆ₐ[ℂ] (H →L[ℂ] H) :=
  F.coordinates.symm.conjStarAlgEquiv.toStarAlgHom.comp l2DiagonalHom

theorem inflateHom_apply (T : E →L[ℂ] E) (x : H) :
    F.inflateHom T x = F.coordinates.symm (l2Diagonal T (F.coordinates x)) := rfl

@[simp] theorem inflateHom_column (T : E →L[ℂ] E) (i : ℕ) (x : E) :
    F.inflateHom T (F.column i x) = F.column i (T x) := by
  rw [F.inflateHom_apply, F.coordinates_column, l2Diagonal_single,
    F.coordinates_symm_single]

/-- The actual unitary on the whole Hilbert space obtained from a corner unitary. -/
def inflateUnitary (v : unitary (E →L[ℂ] E)) : unitary (H →L[ℂ] H) :=
  Unitary.map ({
    toFun := F.inflateHom
    map_one' := F.inflateHom.map_one'
    map_mul' := F.inflateHom.map_mul'
    map_star' := F.inflateHom.map_star' } : (E →L[ℂ] E) →⋆* (H →L[ℂ] H)) v

@[simp] theorem coe_inflateUnitary (v : unitary (E →L[ℂ] E)) :
    (F.inflateUnitary v : H →L[ℂ] H) = F.inflateHom (v : E →L[ℂ] E) := rfl

end FullMatrixCorner

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CanonicalAmplification
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.PopaCorner.instRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
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

theorem centralizer_image_spatial (e : H ≃ₗᵢ[ℂ] K) (S : Set (H →L[ℂ] H)) :
    Set.centralizer (e.conjStarAlgEquiv '' S) =
      e.conjStarAlgEquiv '' Set.centralizer S := by
  ext x
  constructor
  · intro hx
    refine ⟨e.conjStarAlgEquiv.symm x, ?_, e.conjStarAlgEquiv.apply_symm_apply x⟩
    intro y hy
    apply e.conjStarAlgEquiv.injective
    rw [map_mul, map_mul]
    change e.conjStarAlgEquiv y * e.conjStarAlgEquiv (e.conjStarAlgEquiv.symm x) =
      e.conjStarAlgEquiv (e.conjStarAlgEquiv.symm x) * e.conjStarAlgEquiv y
    rw [e.conjStarAlgEquiv.apply_symm_apply]
    exact hx (e.conjStarAlgEquiv y) ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩ z ⟨w, hw, rfl⟩
    simpa only [map_mul] using congrArg e.conjStarAlgEquiv (hy w hw)

/-- The concrete algebra transported by a Hilbert-space isometry. -/
def spatialTransportAlgebra (e : H ≃ₗᵢ[ℂ] K) (M : VonNeumannAlgebra H) :
    VonNeumannAlgebra K where
  toStarSubalgebra := M.toStarSubalgebra.map e.conjStarAlgEquiv.toStarAlgHom
  centralizer_centralizer' := by
    change Set.centralizer (Set.centralizer
      (e.conjStarAlgEquiv '' (M : Set (H →L[ℂ] H)))) =
      e.conjStarAlgEquiv '' (M : Set (H →L[ℂ] H))
    rw [centralizer_image_spatial, centralizer_image_spatial, M.centralizer_centralizer]

def spatialTransportHom (e : H ≃ₗᵢ[ℂ] K) (M : VonNeumannAlgebra H) :
    Algebra M →⋆ₐ[ℂ] Algebra (spatialTransportAlgebra e M) :=
  (e.conjStarAlgEquiv.toStarAlgHom.comp M.toStarSubalgebra.subtype).codRestrict
    (spatialTransportAlgebra e M).toStarSubalgebra (fun x => ⟨x.val, x.property, rfl⟩)

theorem spatialTransportHom_bijective (e : H ≃ₗᵢ[ℂ] K) (M : VonNeumannAlgebra H) :
    Function.Bijective (spatialTransportHom e M) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply e.conjStarAlgEquiv.injective
    exact congrArg Subtype.val hxy
  · intro y
    obtain ⟨x, hx, hxy⟩ := y.property
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

def spatialTransportEquiv (e : H ≃ₗᵢ[ℂ] K) (M : VonNeumannAlgebra H) :
    Algebra M ≃⋆ₐ[ℂ] Algebra (spatialTransportAlgebra e M) :=
  StarAlgEquiv.ofBijective (spatialTransportHom e M) (spatialTransportHom_bijective e M)

@[simp] theorem spatialTransportEquiv_apply (e : H ≃ₗᵢ[ℂ] K)
    (M : VonNeumannAlgebra H) (x : Algebra M) :
    (spatialTransportEquiv e M x : K →L[ℂ] K) = e.conjStarAlgEquiv x := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ClippedCoefficients
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.UltrapowerBridge.instStarTracialQuotient
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# Spectrally clipped coefficient columns

The actual cutoff preserves the coefficient-column bound, right support,
and the relevant quotient image. The final theorem substitutes that
cutoff directly into the coefficient drift estimate.
-/

namespace KadisonKastler

open scoped BigOperators CStarAlgebra

noncomputable section

universe u

section MatrixMap

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Entrywise application of a unital star homomorphism to square matrices. -/
def coefficientMatrixMap (π : A →⋆ₐ[ℂ] B) :
    CStarMatrix n n A →⋆ₐ[ℂ] CStarMatrix n n B where
  toFun := CStarMatrix.mapₙₐ π.toNonUnitalStarAlgHom
  map_one' := by
    apply CStarMatrix.ext
    intro i j
    simp [CStarMatrix.mapₙₐ, CStarMatrix.one_apply]
  map_mul' := map_mul (CStarMatrix.mapₙₐ π.toNonUnitalStarAlgHom)
  map_zero' := map_zero (CStarMatrix.mapₙₐ π.toNonUnitalStarAlgHom)
  map_add' := map_add (CStarMatrix.mapₙₐ π.toNonUnitalStarAlgHom)
  commutes' z := by
    apply CStarMatrix.ext
    intro i j
    change π (if i = j then algebraMap ℂ A z else 0) =
      if i = j then algebraMap ℂ B z else 0
    by_cases hij : i = j
    · simpa only [hij, ite_true, if_true] using AlgHomClass.commutes π z
    · simp [hij]
  map_star' := map_star (CStarMatrix.mapₙₐ π.toNonUnitalStarAlgHom)

@[simp]
theorem coefficientMatrixMap_apply (π : A →⋆ₐ[ℂ] B) (K : CStarMatrix n n A) (i j : n) :
    coefficientMatrixMap π K i j = π (K i j) := rfl

end MatrixMap

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TracialCauchySchwarz
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.UltrapowerBridge.instStarTracialQuotient
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
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

/-- Polarization of real positive-square values makes the trace
pairing Hermitian. -/
theorem FaithfulTracialState.star_pair_symm (τ : FaithfulTracialState B) (x y : B) :
    star (τ.toLinearMap (star y * x)) = τ.toLinearMap (star x * y) := by
  have hadd := τ.positive_im (x + y)
  simp only [star_add, add_mul, mul_add, map_add, Complex.add_im,
    τ.positive_im, zero_add, add_zero] at hadd
  have hI := τ.positive_im (x + Complex.I • y)
  simp [star_smul, add_mul, mul_add,
    Complex.mul_re, Complex.mul_im, τ.positive_im] at hI
  apply Complex.ext
  · simp only [Complex.star_def, Complex.conj_re]
    linarith
  · simp only [Complex.star_def, Complex.conj_im]
    linarith

@[instance_reducible]
def tracialInnerCore (τ : FaithfulTracialState B) :
    PreInnerProductSpace.Core ℂ B where
  inner x y := τ.toLinearMap (star x * y)
  conj_inner_symm x y := by
    change star (τ.toLinearMap (star y * x)) = τ.toLinearMap (star x * y)
    exact τ.star_pair_symm x y
  re_inner_nonneg x := τ.positive x
  add_left x y z := by simp [star_add, add_mul]
  smul_left x y c := by
    change τ.toLinearMap (star (c • x) * y) = star c * τ.toLinearMap (star x * y)
    simp [star_smul]

/-- The tracial two-norm is nonnegative. -/
theorem traceTwoNorm_nonneg (τ : FaithfulTracialState B) (x : B) :
    0 ≤ traceTwoNorm τ x := Real.sqrt_nonneg _

/-- Its square is the real positive-square trace. -/
theorem traceTwoNorm_sq (τ : FaithfulTracialState B) (x : B) :
    traceTwoNorm τ x ^ 2 = (τ.toLinearMap (star x * x)).re :=
  Real.sq_sqrt (τ.positive x)

@[simp]
theorem traceTwoNorm_one (τ : FaithfulTracialState B) : traceTwoNorm τ (1 : B) = 1 := by
  simp [traceTwoNorm, τ.map_one]

@[simp]
theorem traceTwoNorm_star (τ : FaithfulTracialState B) (x : B) :
    traceTwoNorm τ (star x) = traceTwoNorm τ x := by
  simp only [traceTwoNorm, star_star, τ.tracial x (star x)]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteSignFourthMoment
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Fourth moments of finite independent signs

The finite probability space is the set of all Boolean sign assignments.
The four-sign identity and tracial Cauchy–Schwarz give the estimate used
in the bounded-vector test in manuscript §5.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable {B : Type*} [CStarAlgebra B]

/-- The real part of the trace, viewed as a real-linear functional. -/
def realTrace (τ : FaithfulTracialState B) : B →ₗ[ℝ] ℝ :=
  Complex.reLm.comp (τ.toLinearMap.restrictScalars ℝ)

@[simp]
theorem realTrace_apply (τ : FaithfulTracialState B) (x : B) :
    realTrace τ x = (τ.toLinearMap x).re := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TracialProducts
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient
attribute [-simp] _root_.OAI.KadisonKastler.realTrace_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Multiplication estimates for the tracial two-norm -/

namespace KadisonKastler

noncomputable section

universe u

variable {B : Type u} [CStarAlgebra B]

/-- A unitary on the left preserves the tracial two-norm exactly. -/
@[simp]
theorem traceTwoNorm_unitary_mul (τ : FaithfulTracialState B) (u : unitary B) (x : B) :
    traceTwoNorm τ ((u : B) * x) = traceTwoNorm τ x := by
  have he : star ((u : B) * x) * ((u : B) * x) = star x * x := by
    rw [star_mul]
    calc
      star x * star (u : B) * ((u : B) * x) =
          star x * (star (u : B) * (u : B)) * x := by noncomm_ring
      _ = star x * x := by rw [Unitary.star_mul_self_of_mem u.property, mul_one]
  simp only [traceTwoNorm, he]

/-- A unitary on the right preserves the tracial two-norm by traciality. -/
@[simp]
theorem traceTwoNorm_mul_unitary (τ : FaithfulTracialState B) (u : unitary B) (x : B) :
    traceTwoNorm τ (x * (u : B)) = traceTwoNorm τ x := by
  calc
    traceTwoNorm τ (x * (u : B)) = traceTwoNorm τ (star (u : B) * star x) := by
      rw [← star_mul, traceTwoNorm_star]
    _ = traceTwoNorm τ (star x) := by
      exact traceTwoNorm_unitary_mul τ (star u) (star x)
    _ = traceTwoNorm τ x := traceTwoNorm_star τ x

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FreeHaarClosure
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero
attribute [-simp] _root_.OAI.KadisonKastler.realTrace_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The two free-projection moments under tracial approximation

Finite Laurent-polynomial moments follow from the alternating Haar
moments. Cauchy--Schwarz then extends the required degree-two and
degree-four identities under trace-two-norm approximation. In these
degrees no uniform operator bound on the approximants is needed.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

universe u

variable {B : Type u} [CStarAlgebra B]

/-- Subtraction of the scalar trace is a complex-linear operation. -/
def traceCenter (τ : FaithfulTracialState B) : B →ₗ[ℂ] B :=
  LinearMap.id - τ.toLinearMap.smulRight (1 : B)

@[simp]
theorem traceCenter_apply (τ : FaithfulTracialState B) (x : B) :
    traceCenter τ x = x - τ.toLinearMap x • (1 : B) := rfl

@[simp]
theorem trace_traceCenter (τ : FaithfulTracialState B) (x : B) :
    τ.toLinearMap (traceCenter τ x) = 0 := by
  simp [traceCenter_apply, τ.map_one]

@[simp]
theorem traceTwoNorm_neg (τ : FaithfulTracialState B) (x : B) :
    traceTwoNorm τ (-x) = traceTwoNorm τ x := by
  simp [traceTwoNorm]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TraceLimits
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.UltrapowerBridge.instStarTracialQuotient
attribute [-simp] _root_.OAI.KadisonKastler.realTrace_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Limits in the faithful tracial two-norm -/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {B : Type*} [CStarAlgebra B]

@[simp]
theorem traceTwoNorm_zero (τ : FaithfulTracialState B) : traceTwoNorm τ 0 = 0 := by
  simp [traceTwoNorm]

@[simp]
theorem traceTwoNorm_eq_zero_iff (τ : FaithfulTracialState B) (x : B) :
    traceTwoNorm τ x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    apply τ.faithful
    apply Complex.ext
    · have h := traceTwoNorm_sq τ x
      rw [hx, zero_pow (by decide : (2 : ℕ) ≠ 0)] at h
      simpa only [Complex.zero_re] using h.symm
    · simpa only [Complex.zero_im] using τ.positive_im x
  · rintro rfl
    exact traceTwoNorm_zero τ

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ConcreteFiniteTrace
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The faithful normal trace of a concrete finite diffuse factor

The projection-dimension trace gives a faithful normal tracial state
on a concrete finite diffuse factor.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

local instance finiteTraceOrder : PartialOrder (Algebra M) := CStarAlgebra.spectralOrder _
local instance finiteTracePreorder_radea18_1 : Preorder (Algebra M) := (CStarAlgebra.spectralOrder _).toPreorder
local instance finiteTraceLE_radea18_1 : LE (Algebra M) := (CStarAlgebra.spectralOrder _).toLE
local instance finiteTraceStarOrder : StarOrderedRing (Algebra M) := CStarAlgebra.spectralOrderedRing _

theorem factor_central (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (c : Algebra M) (hc : ∀ a : Algebra M, a * c = c * a) :
    ∃ z : ℂ, c = z • (1 : Algebra M) := by
  obtain ⟨z, hz⟩ := hM.factor c hc
  exact ⟨z, by simpa only [Algebra.algebraMap_eq_smul_one] using hz⟩

theorem factor_one_ne_zero (hM : Generator.IsII1Factor M.toStarSubalgebra) :
    (1 : Algebra M) ≠ 0 := by
  intro h
  exact hM.nonzero (congrArg Subtype.val h).symm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_VaryingSequence
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Bounded products for the finite-matrix model

The matrix sizes in the preliminary free model vary with the coordinate.
The existing `lp` space at infinity supplies its ordinary bounded-product
C*-algebra, without identifying the operator norm with a tracial norm.
-/

namespace KadisonKastler

noncomputable section

universe u v

variable (B : ℕ → Type u) [∀ j, CStarAlgebra (B j)] [∀ j, Nontrivial (B j)]

abbrev VaryingBoundedSequence := lp B (⊤ : ENNReal)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CommonRightAction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
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

/-- Conjugating a linear operator by a conjugate-linear isometry gives
a complex-linear operator. -/
def conjugationOperator (J : H ≃ₗᵢ⋆[ℂ] H) (a : H →L[ℂ] H) : H →L[ℂ] H :=
  (J : H →L⋆[ℂ] H).comp (a.comp (J : H →L⋆[ℂ] H))

@[simp]
theorem conjugationOperator_apply (J : H ≃ₗᵢ⋆[ℂ] H) (a : H →L[ℂ] H) (ξ : H) :
    conjugationOperator J a ξ = J (a (J ξ)) := rfl

theorem conjugationOperator_twice (J : H ≃ₗᵢ⋆[ℂ] H)
    (hJ : Function.Involutive J) (a : H →L[ℂ] H) :
    conjugationOperator J (conjugationOperator J a) = a := by
  ext ξ
  change J (J (a (J (J ξ)))) = a ξ
  rw [hJ ξ, hJ (a ξ)]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CommonRightProjection
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Right actions and the common subalgebra projection

The right action of a common unitary reduces the closed subspace generated
by the common algebra and the standard vector. Thus equality of the two
basic constructions gives the cross-commutant membership required for the
common right-action argument, without identifying the whole commutant.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Conjugating a unitary by an involutive conjugation is unitary. -/
def conjugationUnitary (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (u : unitary (H →L[ℂ] H)) : unitary (H →L[ℂ] H) :=
  Unitary.linearIsometryEquiv.symm
    { (conjugationOperator J u).toLinearMap with
      norm_map' := by
        intro ξ
        change ‖J ((u : H →L[ℂ] H) (J ξ))‖ = ‖ξ‖
        rw [J.norm_map, Unitary.norm_map, J.norm_map]
      invFun := conjugationOperator J (star (u : H →L[ℂ] H))
      left_inv := by
        intro ξ
        change J (star (u : H →L[ℂ] H) (J (J ((u : H →L[ℂ] H) (J ξ))))) = ξ
        rw [hJ ((u : H →L[ℂ] H) (J ξ))]
        change J ((star (u : H →L[ℂ] H) * (u : H →L[ℂ] H)) (J ξ)) = ξ
        rw [Unitary.star_mul_self_of_mem u.property, one_apply_eq_self, hJ ξ]
      right_inv := by
        intro ξ
        change J ((u : H →L[ℂ] H) (J (J (star (u : H →L[ℂ] H) (J ξ))))) = ξ
        rw [hJ (star (u : H →L[ℂ] H) (J ξ))]
        change J (((u : H →L[ℂ] H) * star (u : H →L[ℂ] H)) (J ξ)) = ξ
        rw [Unitary.mul_star_self_of_mem u.property, one_apply_eq_self, hJ ξ] }

@[simp]
theorem conjugationUnitary_coe (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (u : unitary (H →L[ℂ] H)) :
    (conjugationUnitary J hJ u : H →L[ℂ] H) = conjugationOperator J u := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PublishedKaplansky
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.PopaCorner.instNormedRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The published bounded-density input

Irving Kaplansky, *A theorem on rings of operators*, Pacific Journal of
Mathematics 1 (1951), 227--232, Theorem 1, p. 227:
https://msp.org/pjm/1951/1-2/pjm-v1-n2-p06-s.pdf

The paper's terminology "unit sphere" is the closed unit ball, as the
norm bounds in the proof on pp. 228 and 230--231 explicitly show.
The input below is its finite-strong-neighborhood specialization to a
unital star algebra and its bicommutant. The already proved double
commutant theorem supplies the required strong density. No statement
comparing two algebras or their Kadison--Kastler distances is assumed.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

universe u

/-- Kaplansky's published unit-ball density theorem, retaining only finite
vector tests needed in the nonseparable reduction. -/
def PublishedKaplanskyDensity : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
    ∀ (A : StarSubalgebra ℂ (H →L[ℂ] H)) (T : H →L[ℂ] H),
      T ∈ Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H))) → ‖T‖ ≤ 1 →
      ∀ (V : Finset H) (ε : ℝ), 0 < ε →
        ∃ a : A, ‖a‖ ≤ 1 ∧ ∀ x ∈ V, ‖T x - (a : H →L[ℂ] H) x‖ < ε

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The actual von Neumann algebra generated by a unital star algebra. -/
def generatedVonNeumannAlgebra (A : StarSubalgebra ℂ (H →L[ℂ] H)) :
    VonNeumannAlgebra H where
  toStarSubalgebra := StarSubalgebra.centralizer ℂ
    (StarSubalgebra.centralizer ℂ (A : Set (H →L[ℂ] H)) : Set (H →L[ℂ] H))
  centralizer_centralizer' := by
    let S := (StarSubalgebra.centralizer ℂ (A : Set (H →L[ℂ] H)) :
      Set (H →L[ℂ] H))
    change (S ∪ star S).centralizer.centralizer.centralizer = (S ∪ star S).centralizer
    exact Set.centralizer_centralizer_centralizer _

@[simp] theorem generatedVonNeumannAlgebra_coe
    (A : StarSubalgebra ℂ (H →L[ℂ] H)) :
    (generatedVonNeumannAlgebra A : Set (H →L[ℂ] H)) =
      Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H))) := by
  change (StarSubalgebra.centralizer ℂ
    (StarSubalgebra.centralizer ℂ (A : Set (H →L[ℂ] H)) : Set (H →L[ℂ] H)) :
      Set (H →L[ℂ] H)) = _
  rw [StarSubalgebra.coe_centralizer_centralizer, StarMemClass.star_coe_eq, Set.union_self]

theorem subset_generatedVonNeumannAlgebra (A : StarSubalgebra ℂ (H →L[ℂ] H)) :
    (A : Set (H →L[ℂ] H)) ⊆ generatedVonNeumannAlgebra A := by
  rw [generatedVonNeumannAlgebra_coe]
  exact Set.subset_centralizer_centralizer

/-- A concrete von Neumann algebra contains the generated algebra of
each of its star subalgebras. -/
theorem generatedVonNeumannAlgebra_le_of_le
    (A : StarSubalgebra ℂ (H →L[ℂ] H)) (B : VonNeumannAlgebra H)
    (hAB : A ≤ B.toStarSubalgebra) : generatedVonNeumannAlgebra A ≤ B := by
  intro x hx
  change x ∈ (generatedVonNeumannAlgebra A : Set (H →L[ℂ] H)) at hx
  rw [generatedVonNeumannAlgebra_coe] at hx
  change x ∈ (B : Set (H →L[ℂ] H))
  rw [← B.centralizer_centralizer]
  exact Set.centralizer_subset (Set.centralizer_subset hAB) hx

/-- Turn the finite-neighborhood published statement into an actual
strongly convergent net of contractions. -/
theorem PublishedKaplanskyDensity.exists_strong_contraction_net
    (hK : PublishedKaplanskyDensity.{u})
    (A : StarSubalgebra ℂ (H →L[ℂ] H)) (T : H →L[ℂ] H)
    (hT : T ∈ Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H))))
    (hn : ‖T‖ ≤ 1) :
    ∃ a : Finset H × ℕ → A, (∀ d, ‖a d‖ ≤ 1) ∧
      ∀ x : H, Tendsto (fun d => (a d : H →L[ℂ] H) x) atTop (𝓝 (T x)) := by
  classical
  have hex (d : Finset H × ℕ) :=
    hK H A T hT hn d.1 (1 / ((d.2 : ℝ) + 1)) (by positivity)
  choose a hn ha using hex
  refine ⟨a, hn, ?_⟩
  intro x
  apply (tendsto_iff_dist_tendsto_zero).mpr
  have hsnd : Tendsto (fun d : Finset H × ℕ => d.2) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_snd
  apply squeeze_zero' (Eventually.of_forall (fun d => dist_nonneg)) ?_
    (tendsto_one_div_add_atTop_nhds_zero_nat.comp hsnd)
  filter_upwards [eventually_ge_atTop (({x} : Finset H), 0)] with d hd
  rw [dist_comm, dist_eq_norm]
  exact (ha d x (hd.1 (Finset.mem_singleton_self x))).le

/-- The same actual net converges on every matrix coefficient. -/
theorem PublishedKaplanskyDensity.exists_weak_contraction_net
    (hK : PublishedKaplanskyDensity.{u})
    (A : StarSubalgebra ℂ (H →L[ℂ] H)) (T : H →L[ℂ] H)
    (hT : T ∈ Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H))))
    (hn : ‖T‖ ≤ 1) :
    ∃ a : Finset H × ℕ → A, (∀ d, ‖a d‖ ≤ 1) ∧
      ∀ x y : H, Tendsto (fun d => inner ℂ y ((a d : H →L[ℂ] H) x))
        atTop (𝓝 (inner ℂ y (T x))) := by
  obtain ⟨a, ha, hlim⟩ := hK.exists_strong_contraction_net A T hT hn
  exact ⟨a, ha, fun x y =>
    (continuous_const.inner continuous_id).continuousAt.tendsto.comp (hlim x)⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixVonNeumann
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient
attribute [-simp] _root_.OAI.KadisonKastler.spatialTransportEquiv_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
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

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [Fintype ι] [DecidableEq ι]

def matrixVonNeumann (M : VonNeumannAlgebra H) : VonNeumannAlgebra (Generator.FiniteHilbert ι H) where
  toStarSubalgebra := StarSubalgebra.centralizer ℂ
    (Set.range fun a : Algebra M.commutant => Generator.diagonalOperator (ι := ι) a.val)
  centralizer_centralizer' := Set.centralizer_centralizer_centralizer _

omit [DecidableEq ι] in
theorem mem_matrixVonNeumann_iff_diagonal (M : VonNeumannAlgebra H)
    (T : Generator.FiniteHilbert ι H →L[ℂ] Generator.FiniteHilbert ι H) :
    T ∈ matrixVonNeumann M ↔ ∀ a : Algebra M.commutant,
      T * Generator.diagonalOperator a.val = Generator.diagonalOperator a.val * T := by
  change T ∈ StarSubalgebra.centralizer ℂ
    (Set.range fun a : Algebra M.commutant => Generator.diagonalOperator (ι := ι) a.val) ↔ _
  rw [StarSubalgebra.mem_centralizer_iff]
  constructor
  · intro h a
    exact (h _ ⟨a, rfl⟩).1.symm
  · intro h g hg
    obtain ⟨a, rfl⟩ := hg
    refine ⟨(h a).symm, ?_⟩
    rw [← Generator.diagonalOperator_star]
    exact (h (star a)).symm

theorem mem_matrixVonNeumann_iff_entries (M : VonNeumannAlgebra H)
    (T : Generator.FiniteHilbert ι H →L[ℂ] Generator.FiniteHilbert ι H) :
    T ∈ matrixVonNeumann M ↔ ∀ i j, Generator.operatorEntry T i j ∈ M := by
  rw [mem_matrixVonNeumann_iff_diagonal]
  constructor
  · intro h i j
    have he := Generator.operatorEntry_mem_centralizer M.commutant.toStarSubalgebra T h i j
    change Generator.operatorEntry T i j ∈ (M : Set (H →L[ℂ] H))
    simpa only [VonNeumannAlgebra.coe_toStarSubalgebra, VonNeumannAlgebra.coe_commutant,
      M.centralizer_centralizer] using he
  · intro h a
    exact Generator.diagonalOperator_commutes_of_entries a.val T
      (fun i j => VonNeumannAlgebra.mem_commutant_iff.mp a.property _ (h i j))

local instance matrixVNOperatorOrder : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
local instance matrixVNOperatorStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _
local instance matrixVNAlgebraOrder (M : VonNeumannAlgebra H) : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance matrixVNAlgebraStarOrder (M : VonNeumannAlgebra H) : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _

def matrixOperatorHom (M : VonNeumannAlgebra H) :
    CStarMatrix ι ι (Algebra M) →⋆ₐ[ℂ]
      (Generator.FiniteHilbert ι H →L[ℂ] Generator.FiniteHilbert ι H) :=
  hilbertMatrixHom.comp (coefficientMatrixMap M.toStarSubalgebra.subtype)

theorem matrixOperatorHom_apply (M : VonNeumannAlgebra H)
    (x : CStarMatrix ι ι (Algebra M)) :
    matrixOperatorHom M x = hilbertMatrix (x.map M.toStarSubalgebra.subtype) := rfl

theorem operatorEntry_matrixOperatorHom (M : VonNeumannAlgebra H)
    (x : CStarMatrix ι ι (Algebra M)) (i j : ι) :
    Generator.operatorEntry (matrixOperatorHom M x) i j = (x i j).val := by
  ext ξ
  simp [Generator.operatorEntry, matrixOperatorHom_apply, hilbertMatrix_apply,
    Generator.tupleSingle_apply, Pi.single_apply, apply_ite]

theorem matrixOperatorHom_mem (M : VonNeumannAlgebra H)
    (x : CStarMatrix ι ι (Algebra M)) : matrixOperatorHom M x ∈ matrixVonNeumann M := by
  rw [mem_matrixVonNeumann_iff_entries]
  intro i j
  rw [operatorEntry_matrixOperatorHom]
  exact (x i j).property

theorem matrixOperatorHom_injective (M : VonNeumannAlgebra H) :
    Function.Injective (matrixOperatorHom (ι := ι) M) := by
  intro x y h
  apply CStarMatrix.ext
  intro i j
  apply Subtype.ext
  simpa only [operatorEntry_matrixOperatorHom] using
    congrArg (fun T => Generator.operatorEntry T i j) h

def matrixFromOperator (M : VonNeumannAlgebra H)
    (T : Generator.FiniteHilbert ι H →L[ℂ] Generator.FiniteHilbert ι H)
    (hT : T ∈ matrixVonNeumann M) : CStarMatrix ι ι (Algebra M) :=
  CStarMatrix.ofMatrix fun i j =>
    ⟨Generator.operatorEntry T i j, (mem_matrixVonNeumann_iff_entries M T).mp hT i j⟩

theorem matrixOperatorHom_matrixFromOperator (M : VonNeumannAlgebra H)
    (T : Generator.FiniteHilbert ι H →L[ℂ] Generator.FiniteHilbert ι H)
    (hT : T ∈ matrixVonNeumann M) :
    matrixOperatorHom M (matrixFromOperator M T hT) = T := by
  ext ξ i
  simp only [matrixOperatorHom_apply, hilbertMatrix_apply, CStarMatrix.map_apply,
    matrixFromOperator]
  change (∑ j, T (Generator.tupleSingle j (ξ j)) i) = T ξ i
  have h := congrArg (fun ζ => T ζ i) (Generator.tuple_eq_sum_single ξ)
  simpa only [map_sum, WithLp.ofLp_sum, Finset.sum_apply] using h.symm

def matrixAlgebraHom (M : VonNeumannAlgebra H) :
    CStarMatrix ι ι (Algebra M) →⋆ₐ[ℂ] Algebra (matrixVonNeumann (ι := ι) M) where
  toFun x := ⟨matrixOperatorHom M x, matrixOperatorHom_mem M x⟩
  map_one' := Subtype.ext (map_one (matrixOperatorHom M))
  map_mul' x y := Subtype.ext (map_mul (matrixOperatorHom M) x y)
  map_zero' := Subtype.ext (map_zero (matrixOperatorHom M))
  map_add' x y := Subtype.ext (map_add (matrixOperatorHom M) x y)
  commutes' z := Subtype.ext (AlgHomClass.commutes (matrixOperatorHom M) z)
  map_star' x := Subtype.ext (map_star (matrixOperatorHom M) x)

def matrixAlgebraEquiv (M : VonNeumannAlgebra H) :
    CStarMatrix ι ι (Algebra M) ≃⋆ₐ[ℂ] Algebra (matrixVonNeumann (ι := ι) M) :=
  StarAlgEquiv.ofBijective (matrixAlgebraHom (ι := ι) M)
    ⟨fun _x _y h => matrixOperatorHom_injective M (congrArg Subtype.val h),
      fun T => ⟨matrixFromOperator M T.val T.property,
        Subtype.ext (matrixOperatorHom_matrixFromOperator M T.val T.property)⟩⟩

@[simp]
theorem matrixAlgebraEquiv_apply (M : VonNeumannAlgebra H)
    (x : CStarMatrix ι ι (Algebra M)) :
    (matrixAlgebraEquiv (ι := ι) M x).val = matrixOperatorHom M x := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TracialHilbertConjugation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
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

def starVectorMap (J : A →ₗ[ℂ] E) : A →ₗ⋆[ℂ] E :=
  J.comp (starLinearEquiv ℂ : A ≃ₗ⋆[ℂ] A).toLinearMap

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProductBoundaryCocycle
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerOrder
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
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

omit [CompleteSpace H] in
@[simp]
theorem conjugationOperator_one (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J) :
    conjugationOperator J (1 : H →L[ℂ] H) = 1 := by
  ext ξ
  exact hJ ξ

omit [CompleteSpace H] in
theorem conjugationOperator_mul (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (a b : H →L[ℂ] H) :
    conjugationOperator J (a * b) = conjugationOperator J a * conjugationOperator J b := by
  ext ξ
  change J (a (b (J ξ))) = J (a (J (J (b (J ξ)))))
  rw [hJ (b (J ξ))]

omit [CompleteSpace H] in
/-- Conjugation by a conjugate-linear isometry preserves the operator norm. -/
theorem norm_conjugationOperator (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (a : H →L[ℂ] H) : ‖conjugationOperator J a‖ = ‖a‖ := by
  have hle (b : H →L[ℂ] H) : ‖conjugationOperator J b‖ ≤ ‖b‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro ξ
    change ‖J (b (J ξ))‖ ≤ ‖b‖ * ‖ξ‖
    rw [J.norm_map]
    simpa only [J.norm_map] using b.le_opNorm (J ξ)
  have hback := hle (conjugationOperator J a)
  rw [conjugationOperator_twice J hJ] at hback
  exact le_antisymm (hle a) hback

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RescaledTomitaGraph
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
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

/-- The fixed Hilbert space in which the two rescaled graphs are compared. -/
abbrev TomitaGraphHilbert (H : Type*) := Generator.FiniteHilbert (Fin 2) H

/-- Graph coordinates after identifying the conjugate Hilbert space by `J`. -/
def rescaledGraphVector (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ)
    (x : H →L[ℂ] H) : TomitaGraphHilbert H :=
  WithLp.toLp 2 ![x Ω, c • J (star x Ω)]

@[simp] theorem rescaledGraphVector_zero (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ)
    (x : H →L[ℂ] H) : rescaledGraphVector J Ω c x 0 = x Ω := rfl

@[simp] theorem rescaledGraphVector_one (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ)
    (x : H →L[ℂ] H) : rescaledGraphVector J Ω c x 1 = c • J (star x Ω) := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ConjugateRightAlgebra
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero
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
theorem conjugateIsometry_inner (J : H ≃ₗᵢ⋆[ℂ] H) (x y : H) :
    inner ℂ (J x) (J y) = star (inner ℂ x y) := by
  have hp : J x + Complex.I • J y = J (x - Complex.I • y) := by
    rw [map_sub, J.map_smulₛₗ]
    simp only [Complex.conj_I, neg_smul, sub_neg_eq_add]
  have hm : J x - Complex.I • J y = J (x + Complex.I • y) := by
    rw [map_add, J.map_smulₛₗ]
    simp only [Complex.conj_I, neg_smul, sub_eq_add_neg]
  apply Complex.ext
  · rw [Complex.star_def, Complex.conj_re]
    simp only [← RCLike.re_eq_complex_re]
    rw [
      re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four (𝕜 := ℂ),
      re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four (𝕜 := ℂ)]
    rw [← map_add J, ← map_sub J, J.norm_map, J.norm_map]
  · rw [Complex.star_def, Complex.conj_im]
    simp only [← RCLike.im_eq_complex_im]
    rw [
      im_inner_eq_norm_sub_i_smul_mul_self_sub_norm_add_i_smul_mul_self_div_four (𝕜 := ℂ),
      im_inner_eq_norm_sub_i_smul_mul_self_sub_norm_add_i_smul_mul_self_div_four (𝕜 := ℂ)]
    simp only [RCLike.I_to_complex]
    rw [hm, hp, J.norm_map, J.norm_map]
    ring

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_InvariantOperatorMean
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.UltrapowerBridge.instStarTracialQuotient
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
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

def scalarMeanTranslate (g : G) (f : G →ᵇ ℂ) : G →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete (fun t => f (g⁻¹ * t)) ‖f‖
    (fun _ => f.norm_coe_le_norm _)

/-- The usual scalar invariant-mean data, with no assertion of existence. -/
structure ScalarInvariantMean (G : Type*) [Group G] [TopologicalSpace G] [DiscreteTopology G] where
  toCLM : (G →ᵇ ℂ) →L[ℂ] ℂ
  map_const_one : toCLM (BoundedContinuousFunction.const G 1) = 1
  norm_le : ∀ f, ‖toCLM f‖ ≤ ‖f‖
  positive : ∀ f, (∀ g, (f g).im = 0 ∧ 0 ≤ (f g).re) →
    (toCLM f).im = 0 ∧ 0 ≤ (toCLM f).re
  invariant : ∀ g f, toCLM (scalarMeanTranslate g f) = toCLM f

namespace ScalarInvariantMean

variable (m : ScalarInvariantMean G)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The bounded scalar coefficient to which the scalar mean is applied. -/
def coefficient (F : G →ᵇ (H →L[ℂ] H)) (x y : H) : G →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun g => inner ℂ y (F g x)) (‖F‖ * ‖x‖ * ‖y‖) (fun g => by
      calc
        ‖inner ℂ y (F g x)‖ ≤ ‖y‖ * ‖F g x‖ := norm_inner_le_norm _ _
        _ ≤ ‖y‖ * (‖F‖ * ‖x‖) := mul_le_mul_of_nonneg_left
          (((F g).le_opNorm x).trans (mul_le_mul_of_nonneg_right
            (F.norm_coe_le_norm g) (norm_nonneg x))) (norm_nonneg y)
        _ = _ := by ring)

omit [Group G] [CompleteSpace H] in
@[simp] theorem coefficient_apply (F : G →ᵇ (H →L[ℂ] H)) (x y : H) (g : G) :
    coefficient F x y g = inner ℂ y (F g x) := rfl

omit [Group G] [CompleteSpace H] in
theorem norm_coefficient_le (F : G →ᵇ (H →L[ℂ] H)) (x y : H) :
    ‖coefficient F x y‖ ≤ ‖F‖ * ‖x‖ * ‖y‖ :=
  (BoundedContinuousFunction.norm_le (by positivity)).mpr (fun g => by
    calc
      ‖coefficient F x y g‖ ≤ ‖y‖ * ‖F g x‖ := norm_inner_le_norm _ _
      _ ≤ ‖y‖ * (‖F‖ * ‖x‖) := mul_le_mul_of_nonneg_left
        (((F g).le_opNorm x).trans (mul_le_mul_of_nonneg_right
          (F.norm_coe_le_norm g) (norm_nonneg x))) (norm_nonneg y)
      _ = _ := by ring)

omit [Group G] [CompleteSpace H] in
theorem coefficient_add_input (F : G →ᵇ (H →L[ℂ] H)) (x z y : H) :
    coefficient F (x + z) y = coefficient F x y + coefficient F z y := by
  ext g
  simp only [coefficient_apply, BoundedContinuousFunction.add_apply, map_add, inner_add_right]

omit [Group G] [CompleteSpace H] in
theorem coefficient_add_test (F : G →ᵇ (H →L[ℂ] H)) (x y z : H) :
    coefficient F x (y + z) = coefficient F x y + coefficient F x z := by
  ext g
  simp only [coefficient_apply, BoundedContinuousFunction.add_apply, inner_add_left]

omit [Group G] [CompleteSpace H] in
theorem coefficient_smul_test (F : G →ᵇ (H →L[ℂ] H)) (c : ℂ) (x y : H) :
    coefficient F x (c • y) = star c • coefficient F x y := by
  ext g
  simp only [coefficient_apply, BoundedContinuousFunction.smul_apply, inner_smul_left,
    smul_eq_mul]
  rfl

/-- A genuine continuous linear scalar functional in the test-vector slot. -/
def testFunctional (F : G →ᵇ (H →L[ℂ] H)) (x : H) : H →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun y => star (m.toCLM (coefficient F x y))
      map_add' := fun y z => by rw [coefficient_add_test, map_add, star_add]
      map_smul' := fun c y => by
        rw [coefficient_smul_test, map_smul, star_smul, star_star]
        rfl }
    (‖F‖ * ‖x‖) (fun y => by
      change ‖star (m.toCLM (coefficient F x y))‖ ≤ _
      rw [norm_star]
      exact (m.norm_le _).trans (norm_coefficient_le F x y))

def operatorValue (F : G →ᵇ (H →L[ℂ] H)) (x : H) : H :=
  (InnerProductSpace.toDual ℂ H).symm (m.testFunctional F x)

end ScalarInvariantMean

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_KaplanskySelfAdjoint
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Self-adjoint strong approximation

This is the first step in discharging bounded density. The existing
bicommutant theorem gives unbounded strong approximation. Taking real
parts preserves weak convergence; orthogonal complements of the finite
tuple orbit then recover strong approximation by self-adjoint elements.
-/

namespace KadisonKastler

open Generator Filter
open scoped Topology ComplexOrder BigOperators

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem inner_realPart (a : H →L[ℂ] H) (x y : H) :
    inner ℂ y ((realPart a : H →L[ℂ] H) x) =
      (2 : ℂ)⁻¹ * (inner ℂ y (a x) + inner ℂ (a y) x) := by
  rw [realPart_apply_coe]
  simp only [smul_apply, add_apply]
  norm_num
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  ring


/-- Strong convergence implies weak convergence of the real parts, even
when no uniform norm bound on the original net is available. -/
theorem tendsto_inner_realPart_of_strong
    {ι : Type*} {l : Filter ι} {a : ι → H →L[ℂ] H} {T : H →L[ℂ] H}
    (ha : ∀ x, Tendsto (fun i => a i x) l (𝓝 (T x))) (x y : H) :
    Tendsto (fun i => inner ℂ y ((realPart (a i) : H →L[ℂ] H) x)) l
      (𝓝 (inner ℂ y ((realPart T : H →L[ℂ] H) x))) := by
  simp only [inner_realPart]
  exact (((continuous_const.inner continuous_id).continuousAt.tendsto.comp (ha x)).add
    ((continuous_id.inner continuous_const).continuousAt.tendsto.comp (ha y))).const_mul _

def selfAdjointTupleMap {ι : Type*} [Fintype ι]
    (A : StarSubalgebra ℂ (H →L[ℂ] H)) (x : FiniteHilbert ι H) :
    selfAdjoint A →ₗ[ℝ] FiniteHilbert ι H where
  toFun a := diagonalOperator (a.val : H →L[ℂ] H) x
  map_add' a b := by ext i; rfl
  map_smul' c a := by
    ext i
    change (c • (a.val : H →L[ℂ] H)) (x i) = c • ((a.val : H →L[ℂ] H) (x i))
    rfl

/-- The finite tuple of values of a self-adjoint bicommutant element lies
in the real-linear closure of the self-adjoint algebra orbit. -/
theorem selfAdjoint_bicommutant_tuple_mem_closure
    {ι : Type*} [Fintype ι] (A : StarSubalgebra ℂ (H →L[ℂ] H))
    (T : H →L[ℂ] H) (hT : T ∈ Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H))))
    (hsa : IsSelfAdjoint T) (x : FiniteHilbert ι H) :
    diagonalOperator T x ∈ (selfAdjointTupleMap A x).range.topologicalClosure := by
  classical
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  let W := (selfAdjointTupleMap A x).range.topologicalClosure
  have hW : IsClosed (W : Set (FiniteHilbert ι H)) := Submodule.isClosed_topologicalClosure _
  change diagonalOperator T x ∈ W
  have hWW : Wᗮᗮ = W := Submodule.orthogonal_orthogonal W
  rw [← hWW]
  apply (W.orthogonal.mem_orthogonal _).mpr
  intro y hy
  obtain ⟨a, ha⟩ := bicommutant_exists_strong_net A T hT
  have hlim : Tendsto
      (fun d => inner ℝ (diagonalOperator ((realPart (a d) : A) : H →L[ℂ] H) x) y)
      atTop (𝓝 (inner ℝ (diagonalOperator T x) y)) := by
    simp only [PiLp.inner_apply]
    apply tendsto_finsetSum
    intro i _
    have h := tendsto_inner_realPart_of_strong (fun z => ha z) (x i) (y i)
    have he (d) : (((realPart (a d) : A) : H →L[ℂ] H)) =
        (realPart ((a d).val) : H →L[ℂ] H) := by
      simp only [realPart_apply_coe, ← Complex.coe_smul]
      rfl
    simp only [diagonalOperator_apply, he]
    have hr := Complex.continuous_re.continuousAt.tendsto.comp h
    simpa only [hsa.coe_realPart, real_inner_eq_re_inner, inner_re_symm, RCLike.re_eq_complex_re, Function.comp_def] using hr
  have hzero : ∀ d, inner ℝ
      (diagonalOperator ((realPart (a d) : A) : H →L[ℂ] H) x) y = 0 := by
    intro d
    exact (W.mem_orthogonal y).mp hy _
      (Submodule.le_topologicalClosure _ ⟨realPart (a d), rfl⟩)
  have hz := tendsto_nhds_unique (hlim.congr hzero) tendsto_const_nhds
  exact (real_inner_comm _ _).trans hz

/-- Finite strong tests can be met by a self-adjoint element of the original
algebra. This step has no bounded-density hypothesis. -/
theorem selfAdjoint_bicommutant_finite_strong_approximation
    (A : StarSubalgebra ℂ (H →L[ℂ] H)) (T : H →L[ℂ] H)
    (hT : T ∈ Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H))))
    (hsa : IsSelfAdjoint T) (V : Finset H) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : A, IsSelfAdjoint (a : H →L[ℂ] H) ∧
      ∀ x ∈ V, ‖T x - (a : H →L[ℂ] H) x‖ < ε := by
  classical
  let x : FiniteHilbert V H := WithLp.toLp 2 (fun i : V => i.val)
  have hc := selfAdjoint_bicommutant_tuple_mem_closure A T hT hsa x
  obtain ⟨z, ⟨a, rfl⟩, ha⟩ := Metric.mem_closure_iff.mp hc ε hε
  refine ⟨a.val, ?_, ?_⟩
  · change star (a.val : H →L[ℂ] H) = (a.val : H →L[ℂ] H)
    exact congrArg (fun b : A => (b : H →L[ℂ] H)) a.property
  · intro y hy
    have hb := PiLp.norm_apply_le
      (diagonalOperator T x - selfAdjointTupleMap A x a) (⟨y, hy⟩ : V)
    exact hb.trans_lt (by simpa only [dist_eq_norm] using ha)

/-- A self-adjoint strongly convergent net, indexed independently of any
norm bound. Bounded transforms will supply the missing norm control. -/
theorem selfAdjoint_bicommutant_exists_strong_net
    (A : StarSubalgebra ℂ (H →L[ℂ] H)) (T : H →L[ℂ] H)
    (hT : T ∈ Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H))))
    (hsa : IsSelfAdjoint T) :
    ∃ a : Finset H × ℕ → A,
      (∀ i, IsSelfAdjoint (a i : H →L[ℂ] H)) ∧
      ∀ x : H, Tendsto (fun i => (a i : H →L[ℂ] H) x) atTop (𝓝 (T x)) := by
  classical
  have hex (i : Finset H × ℕ) := selfAdjoint_bicommutant_finite_strong_approximation
    A T hT hsa i.1 (show 0 < 1 / ((i.2 : ℝ) + 1) by positivity)
  choose a hsa' ha using hex
  refine ⟨a, hsa', ?_⟩
  intro x
  apply (tendsto_iff_dist_tendsto_zero).mpr
  have hsnd : Tendsto (fun i : Finset H × ℕ => i.2) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_snd
  apply squeeze_zero' (Eventually.of_forall (fun _ => dist_nonneg)) ?_
    (tendsto_one_div_add_atTop_nhds_zero_nat.comp hsnd)
  filter_upwards [eventually_ge_atTop (({x} : Finset H), 0)] with i hi
  rw [dist_comm, dist_eq_norm]
  exact (ha i x (hi.1 (Finset.mem_singleton_self x))).le

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_KaplanskyResolvent
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.UltrapowerBridge.instStarTracialQuotient
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Bounded resolvents for the Kaplansky argument

Off-real resolvents are uniformly bounded on all self-adjoint operators.
Their strong continuity therefore does not require a norm bound on the
approximating self-adjoint net. This is the bounded-transform step used in
Kaplansky's proof (Pacific J. Math. 1 (1951), Lemma 4, pp.229--230).
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem spectral_im_eq_zero {a : H →L[ℂ] H} (ha : IsSelfAdjoint a)
    {w : ℂ} (hw : w ∈ spectrum ℂ a) : w.im = 0 := by
  have h := SpectrumRestricts.real_iff.mp ha.spectrumRestricts w hw
  simpa using congrArg Complex.im h

/-- Every nonreal point belongs to the resolvent set of a self-adjoint operator. -/
theorem nonreal_mem_resolventSet {a : H →L[ℂ] H} (ha : IsSelfAdjoint a)
    {z : ℂ} (hz : z.im ≠ 0) : z ∈ resolventSet ℂ a := by
  classical
  change IsUnit (algebraMap ℂ (H →L[ℂ] H) z - a)
  by_contra hs
  exact hz (spectral_im_eq_zero ha hs)

theorem resolvent_eq_cfc_of_selfAdjoint {a : H →L[ℂ] H} (ha : IsSelfAdjoint a)
    {z : ℂ} (hz : z.im ≠ 0) :
    resolvent a z = cfc (fun w : ℂ => (z - w)⁻¹) a := by
  have hn : ∀ w ∈ spectrum ℂ a, z - w ≠ 0 := by
    intro w hw he
    have he' : z = w := sub_eq_zero.mp he
    apply hz
    rw [he']
    exact spectral_im_eq_zero ha hw
  rw [cfc_inv (fun w : ℂ => z - w) a hn
    ((continuous_const.sub continuous_id).continuousOn) ha.isStarNormal]
  rw [cfc_sub (fun _ : ℂ => z) (fun w : ℂ => w) a,
    cfc_const z a ha.isStarNormal, cfc_id' ℂ a ha.isStarNormal]
  rfl

/-- The resolvent norm bound is independent of the self-adjoint operator. -/
theorem norm_resolvent_le_inv_abs_im {a : H →L[ℂ] H} (ha : IsSelfAdjoint a)
    {z : ℂ} (hz : z.im ≠ 0) : ‖resolvent a z‖ ≤ |z.im|⁻¹ := by
  rw [resolvent_eq_cfc_of_selfAdjoint ha hz]
  apply norm_cfc_le (inv_nonneg.mpr (abs_nonneg _))
  intro w hw
  have hdist : |z.im| ≤ ‖z - w‖ := by
    simpa only [Complex.sub_im, spectral_im_eq_zero ha hw, sub_zero]
      using Complex.abs_im_le_norm (z - w)
  rw [norm_inv]
  exact (inv_le_inv₀ (lt_of_lt_of_le (abs_pos.mpr hz) hdist) (abs_pos.mpr hz)).mpr hdist

/-- Strong continuity of off-real resolvents, including unbounded nets. -/
theorem tendsto_resolvent_of_selfAdjoint_strong
    {ι : Type*} {l : Filter ι} {a : ι → H →L[ℂ] H} {T : H →L[ℂ] H}
    (ha : ∀ i, IsSelfAdjoint (a i)) (hT : IsSelfAdjoint T)
    (hlim : ∀ x, Tendsto (fun i => a i x) l (𝓝 (T x)))
    {z : ℂ} (hz : z.im ≠ 0) (x : H) :
    Tendsto (fun i => resolvent (a i) z x) l (𝓝 (resolvent T z x)) := by
  have hbound (i) : ‖resolvent (a i) z x - resolvent T z x‖ ≤
      |z.im|⁻¹ * ‖a i (resolvent T z x) - T (resolvent T z x)‖ := by
    have he := spectrum.resolvent_sub_resolvent
      (nonreal_mem_resolventSet (ha i) hz) (nonreal_mem_resolventSet hT hz)
    have hev := congrArg (fun b : H →L[ℂ] H => b x) he
    simp only [sub_apply, mul_apply_eq_comp] at hev
    rw [hev]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (norm_resolvent_le_inv_abs_im (ha i) hz) (norm_nonneg _))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero (fun _ => norm_nonneg _) hbound
  simpa using ((hlim (resolvent T z x)).sub_const (T (resolvent T z x))).norm.const_mul
    (|z.im|⁻¹)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_KaplanskyTransform
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.UltrapowerBridge.instStarTracialQuotient
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A bounded rational transform of self-adjoint operators

The scalar map `2t/(1+t²)` takes the real line into the closed unit interval.
Its inverse on that interval is `t/(1+sqrt(1-t²))`. Resolvent continuity
therefore gives bounded strong approximants to any self-adjoint contraction.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

universe u

def kaplanskyTransform (t : ℝ) : ℝ := 2 * t / (1 + t ^ 2)

def kaplanskyInverse (t : ℝ) : ℝ := t / (1 + Real.sqrt (1 - t ^ 2))

theorem continuous_kaplanskyTransform : Continuous kaplanskyTransform := by
  unfold kaplanskyTransform
  fun_prop (disch := intro t; positivity)

theorem continuous_kaplanskyInverse : Continuous kaplanskyInverse := by
  unfold kaplanskyInverse
  fun_prop (disch := intro t; positivity)

theorem abs_kaplanskyTransform_le_one (t : ℝ) : |kaplanskyTransform t| ≤ 1 := by
  have hd : 0 < 1 + t ^ 2 := by positivity
  unfold kaplanskyTransform
  rw [abs_le]
  constructor
  · apply (le_div_iff₀ hd).mpr
    nlinarith [sq_nonneg (t + 1)]
  · apply (div_le_iff₀ hd).mpr
    nlinarith [sq_nonneg (t - 1)]

theorem kaplanskyTransform_inverse {t : ℝ} (ht : |t| ≤ 1) :
    kaplanskyTransform (kaplanskyInverse t) = t := by
  have ht₂ : t ^ 2 ≤ 1 := by
    rcases abs_le.mp ht with ⟨hl, hu⟩
    nlinarith
  have hs : (Real.sqrt (1 - t ^ 2)) ^ 2 = 1 - t ^ 2 := Real.sq_sqrt (by linarith)
  have hd : 1 + Real.sqrt (1 - t ^ 2) ≠ 0 := by positivity
  unfold kaplanskyTransform kaplanskyInverse
  apply (div_eq_iff (by positivity : (1 : ℝ) + (t / (1 + Real.sqrt (1 - t ^ 2))) ^ 2 ≠ 0)).mpr
  field_simp
  linear_combination -t * hs

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The rational transform stays in the unit ball. -/
theorem norm_kaplanskyTransform_le_one (a : H →L[ℂ] H) :
    ‖cfc kaplanskyTransform a‖ ≤ 1 := by
  apply norm_cfc_le (by norm_num)
  intro t _
  simpa only [Real.norm_eq_abs] using abs_kaplanskyTransform_le_one t

/-- Every self-adjoint contraction is the rational transform of a
self-adjoint operator. No spectral or density input is assumed. -/
theorem exists_kaplanskyTransform_preimage (T : H →L[ℂ] H)
    (hT : IsSelfAdjoint T) (hn : ‖T‖ ≤ 1) :
    ∃ S : H →L[ℂ] H, S = cfc kaplanskyInverse T ∧
      IsSelfAdjoint S ∧ cfc kaplanskyTransform S = T := by
  let S := cfc kaplanskyInverse T
  refine ⟨S, rfl, cfc_predicate kaplanskyInverse T, ?_⟩
  dsimp [S]
  rw [← cfc_comp kaplanskyTransform kaplanskyInverse T hT
    continuous_kaplanskyTransform.continuousOn continuous_kaplanskyInverse.continuousOn]
  calc
    cfc (kaplanskyTransform ∘ kaplanskyInverse) T = cfc (id : ℝ → ℝ) T := by
      apply cfc_congr
      intro t ht
      have htn : |t| ≤ ‖T‖ := by
        simpa only [Real.norm_eq_abs] using
          IsometricContinuousFunctionalCalculus.norm_spectrum_le T ht hT
      exact kaplanskyTransform_inverse (htn.trans hn)
    _ = T := cfc_id ℝ T hT

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_KaplanskyRational
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.UltrapowerBridge.instStarTracialQuotient
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Resolvent expression and strong continuity of the bounded transform -/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

universe u

theorem rational_transform_complex (t : ℝ) :
    (kaplanskyTransform t : ℂ) =
      -(Complex.I - (t : ℂ))⁻¹ - (-Complex.I - (t : ℂ))⁻¹ := by
  have hp : Complex.I - (t : ℂ) ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    norm_num at hi
  have hm : -Complex.I - (t : ℂ) ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    norm_num at hi
  have hd : (1 : ℂ) + (t : ℂ) ^ 2 ≠ 0 := by
    exact_mod_cast (show (1 : ℝ) + t ^ 2 ≠ 0 by positivity)
  unfold kaplanskyTransform
  push_cast
  field_simp
  ring_nf
  simp only [Complex.I_sq]
  ring

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Two resolvents express the bounded real rational transform. -/
theorem kaplanskyTransform_eq_resolvents (a : H →L[ℂ] H) (ha : IsSelfAdjoint a) :
    cfc kaplanskyTransform a = -resolvent a Complex.I - resolvent a (-Complex.I) := by
  rw [cfc_real_eq_complex kaplanskyTransform ha,
    resolvent_eq_cfc_of_selfAdjoint ha (by simp), resolvent_eq_cfc_of_selfAdjoint ha (by simp)]
  have hc (w : ℂ) (hw : w.im ≠ 0) :
      ContinuousOn (fun z : ℂ => (w - z)⁻¹) (spectrum ℂ a) := by
    apply (continuous_const.sub continuous_id).continuousOn.inv₀
    intro z hz he
    have hr := SpectrumRestricts.real_iff.mp ha.spectrumRestricts z hz
    have hi := congrArg Complex.im (sub_eq_zero.mp he)
    have hz0 : z.im = 0 := by simpa only [Complex.ofReal_im] using congrArg Complex.im hr
    exact hw (hi.trans hz0)
  rw [← cfc_neg (fun z : ℂ => (Complex.I - z)⁻¹) a,
    ← cfc_sub (fun z : ℂ => -(Complex.I - z)⁻¹)
      (fun z : ℂ => (-Complex.I - z)⁻¹) a (hc Complex.I (by simp)).neg
      (hc (-Complex.I) (by simp))]
  apply cfc_congr
  intro z hz
  have hreal := SpectrumRestricts.real_iff.mp ha.spectrumRestricts z hz
  rw [hreal]
  simpa using rational_transform_complex z.re

/-- Bounded-transform strong continuity requires only self-adjointness,
not a bound on the original net. -/
theorem tendsto_kaplanskyTransform_of_strong
    {ι : Type*} {l : Filter ι} {a : ι → H →L[ℂ] H} {T : H →L[ℂ] H}
    (ha : ∀ i, IsSelfAdjoint (a i)) (hT : IsSelfAdjoint T)
    (hlim : ∀ x, Tendsto (fun i => a i x) l (𝓝 (T x))) (x : H) :
    Tendsto (fun i => cfc kaplanskyTransform (a i) x) l
      (𝓝 (cfc kaplanskyTransform T x)) := by
  simp only [kaplanskyTransform_eq_resolvents _ (ha _),
    kaplanskyTransform_eq_resolvents _ hT, sub_apply, neg_apply]
  exact (tendsto_resolvent_of_selfAdjoint_strong ha hT hlim (by simp) x).neg.sub
    (tendsto_resolvent_of_selfAdjoint_strong ha hT hlim (by simp) x)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_NormClosureUnitBall
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Unit balls and norm closure of a star subalgebra

Radial rescaling of a norm approximant preserves algebra membership and
costs at most a second copy of the approximation error.
-/

namespace KadisonKastler

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem normClosure_unitBall_approx
    (A : StarSubalgebra ℂ (H →L[ℂ] H)) {b : H →L[ℂ] H}
    (hb : b ∈ A.topologicalClosure) (hbn : ‖b‖ ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : A, ‖(a : H →L[ℂ] H)‖ ≤ 1 ∧ ‖b - (a : H →L[ℂ] H)‖ < ε := by
  change b ∈ closure (A : Set (H →L[ℂ] H)) at hb
  obtain ⟨c, hc, hcb⟩ := Metric.mem_closure_iff.mp hb (ε / 2) (half_pos hε)
  rw [dist_eq_norm] at hcb
  by_cases hcn : ‖c‖ ≤ 1
  · exact ⟨⟨c, hc⟩, hcn, by linarith⟩
  have hcpos : 0 < ‖c‖ := by linarith
  have hcone : 1 ≤ ‖c‖ := le_of_not_ge hcn
  let a : A := ⟨((‖c‖⁻¹ : ℝ) : ℂ) • c, A.smul_mem hc _⟩
  have han : ‖(a : H →L[ℂ] H)‖ = 1 := by
    change ‖((‖c‖⁻¹ : ℝ) : ℂ) • c‖ = 1
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr hcpos.le), inv_mul_cancel₀ hcpos.ne']
  have hac : ‖(a : H →L[ℂ] H) - c‖ = ‖c‖ - 1 := by
    change ‖((‖c‖⁻¹ : ℝ) : ℂ) • c - c‖ = ‖c‖ - 1
    rw [Complex.coe_smul]
    rw [show (‖c‖⁻¹ : ℝ) • c - c = (‖c‖⁻¹ - 1) • c by
      rw [sub_smul, one_smul]]
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonpos (sub_nonpos.mpr ((inv_le_one₀ hcpos).mpr hcone)), neg_sub,
      sub_mul, one_mul, inv_mul_cancel₀ hcpos.ne']
  have hdiff : ‖c‖ - 1 ≤ ‖b - c‖ := by
    have htriangle : ‖c‖ ≤ ‖c - b‖ + ‖b‖ := norm_le_norm_sub_add c b
    rw [norm_sub_rev c b] at htriangle
    linarith
  refine ⟨a, han.le, ?_⟩
  have htriangle : ‖b - (a : H →L[ℂ] H)‖ ≤ ‖b - c‖ + ‖c - (a : H →L[ℂ] H)‖ := by
    simpa only [dist_eq_norm] using dist_triangle b c (a : H →L[ℂ] H)
  rw [norm_sub_rev c (a : H →L[ℂ] H), hac] at htriangle
  linarith

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_KaplanskySelfAdjointBall
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.UltrapowerBridge.instStarTracialQuotient
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Bounded density at self-adjoint elements

The rational preimage lies in the same bicommutant. Its unbounded
self-adjoint approximants become contractions under the rational map.
A final norm approximation returns to the original star algebra.
-/

namespace KadisonKastler

open Generator Filter
open scoped Topology BigOperators

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Contractions from the norm closure approximate a self-adjoint
bicommutant contraction strongly on any finite set of vectors. -/
theorem selfAdjoint_bicommutant_closureBall_approx
    (A : StarSubalgebra ℂ (H →L[ℂ] H)) (T : H →L[ℂ] H)
    (hT : T ∈ Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H))))
    (hsa : IsSelfAdjoint T) (hn : ‖T‖ ≤ 1) (V : Finset H)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ b ∈ A.topologicalClosure, ‖b‖ ≤ 1 ∧ ∀ x ∈ V, ‖T x - b x‖ < ε := by
  classical
  let M := generatedVonNeumannAlgebra A
  have hTM : T ∈ M.toStarSubalgebra := by
    change T ∈ (generatedVonNeumannAlgebra A : Set (H →L[ℂ] H))
    rwa [generatedVonNeumannAlgebra_coe]
  let : IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := isClosed_algebra M
  obtain ⟨S, rfl, hS, hST⟩ := exists_kaplanskyTransform_preimage T hsa hn
  have hSin : cfc kaplanskyInverse T ∈ Set.centralizer
      (Set.centralizer (A : Set (H →L[ℂ] H))) := by
    have hs : cfc kaplanskyInverse T ∈ M.toStarSubalgebra := cfc_mem _ hTM
    change cfc kaplanskyInverse T ∈
      (generatedVonNeumannAlgebra A : Set (H →L[ℂ] H)) at hs
    rwa [generatedVonNeumannAlgebra_coe] at hs
  obtain ⟨a, ha, halim⟩ := selfAdjoint_bicommutant_exists_strong_net A _ hSin hS
  have hlim (x : H) : Tendsto
      (fun i => cfc kaplanskyTransform (a i : H →L[ℂ] H) x) atTop (𝓝 (T x)) := by
    simpa only [hST] using tendsto_kaplanskyTransform_of_strong ha hS halim x
  have hevent : ∀ᶠ i in (atTop : Filter (Finset H × ℕ)),
      ∀ x ∈ V, ‖T x - cfc kaplanskyTransform (a i : H →L[ℂ] H) x‖ < ε := by
    rw [Filter.eventually_all_finset]
    intro x _
    have he := (tendsto_iff_norm_sub_tendsto_zero.mp (hlim x)).eventually (gt_mem_nhds hε)
    simpa only [norm_sub_rev] using he
  obtain ⟨i, hi⟩ := hevent.exists
  refine ⟨cfc kaplanskyTransform (a i : H →L[ℂ] H), ?_,
    norm_kaplanskyTransform_le_one _, hi⟩
  let : IsClosed (A.topologicalClosure : Set (H →L[ℂ] H)) := A.isClosed_topologicalClosure
  exact cfc_mem _ (A.le_topologicalClosure (a i).property)

/-- The original star algebra's unit ball is strongly dense at every
self-adjoint contraction in its bicommutant. -/
theorem selfAdjoint_bicommutant_unitBall_approx
    (A : StarSubalgebra ℂ (H →L[ℂ] H)) (T : H →L[ℂ] H)
    (hT : T ∈ Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H))))
    (hsa : IsSelfAdjoint T) (hn : ‖T‖ ≤ 1) (V : Finset H)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a : A, ‖(a : H →L[ℂ] H)‖ ≤ 1 ∧ ∀ x ∈ V, ‖T x - (a : H →L[ℂ] H) x‖ < ε := by
  classical
  obtain ⟨b, hb, hbn, hTb⟩ := selfAdjoint_bicommutant_closureBall_approx
    A T hT hsa hn V (half_pos hε)
  let R := 1 + ∑ x ∈ V, ‖x‖
  have hR : 0 < R := by dsimp [R] <;> positivity
  obtain ⟨a, han, hba⟩ := normClosure_unitBall_approx A hb hbn
    (div_pos hε (mul_pos (by norm_num : (0 : ℝ) < 2) hR))
  refine ⟨a, han, ?_⟩
  intro x hx
  have hxR : ‖x‖ ≤ R := by
    have hs := Finset.single_le_sum (fun y (_ : y ∈ V) => norm_nonneg y) hx
    dsimp [R]
    linarith
  have hdist : ‖b x - (a : H →L[ℂ] H) x‖ < ε / 2 := by
    have hlt : ‖b - (a : H →L[ℂ] H)‖ * R < ε / 2 := by
      have h := mul_lt_mul_of_pos_right hba hR
      have he : ε / (2 * R) * R = ε / 2 := by field_simp
      rwa [he] at h
    have hle := ContinuousLinearMap.le_opNorm (b - (a : H →L[ℂ] H)) x
    exact hle.trans_lt ((mul_le_mul_of_nonneg_left hxR (norm_nonneg _)).trans_lt hlt)
  have htriangle : ‖T x - (a : H →L[ℂ] H) x‖ ≤
      ‖T x - b x‖ + ‖b x - (a : H →L[ℂ] H) x‖ := by
    simpa only [dist_eq_norm] using dist_triangle (T x) (b x) ((a : H →L[ℂ] H) x)
  exact htriangle.trans_lt (by linarith [hTb x hx])

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixOperatorGeneration
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.UltrapowerBridge.instStarTracialQuotient
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Finite matrix algebras and von Neumann generation

These elementary finite-sum arguments are independent of spatial tensor
products and perturbation theorems. -/

namespace KadisonKastler

open Generator Filter
open scoped Topology BigOperators

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance matrixGenerationOrder : PartialOrder (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrder _
local instance matrixGenerationStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _

/-- The finite matrices whose entries belong to a specified star algebra. -/
def entryMatrixAlgebra (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    StarSubalgebra ℂ (CStarMatrix ι ι (H →L[ℂ] H)) where
  carrier := {X | ∀ i j, X i j ∈ S}
  zero_mem' := fun _ _ => S.zero_mem
  one_mem' := by
    intro i j
    change (if i = j then 1 else 0) ∈ S
    split_ifs <;> simp
  add_mem' hX hY i j := S.add_mem (hX i j) (hY i j)
  mul_mem' hX hY i j := S.sum_mem fun k _ => S.mul_mem (hX i k) (hY k j)
  algebraMap_mem' c := by
    intro i j
    change (if i = j then algebraMap ℂ (H →L[ℂ] H) c else 0) ∈ S
    split_ifs <;> simp
  star_mem' hX i j := S.star_mem' (hX j i)

/-- The same finite matrices acting on the finite Hilbert sum. -/
def matrixOperatorAlgebra (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    StarSubalgebra ℂ (FiniteHilbert ι H →L[ℂ] FiniteHilbert ι H) :=
  (entryMatrixAlgebra (ι := ι) S).map hilbertMatrixHom

omit [CompleteSpace H] in
@[simp]
theorem operatorEntry_hilbertMatrix
    (X : CStarMatrix ι ι (H →L[ℂ] H)) (i j : ι) :
    operatorEntry (hilbertMatrix X) i j = X i j := by
  ext ξ
  simp [operatorEntry, hilbertMatrix_apply, tupleSingle_apply, Pi.single_apply, apply_ite]

omit [CompleteSpace H] in
theorem hilbertMatrix_operatorEntries (T : FiniteHilbert ι H →L[ℂ] FiniteHilbert ι H) :
    hilbertMatrix (CStarMatrix.ofMatrix fun i j => operatorEntry T i j) = T := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply PiLp.ext
  intro i
  change hilbertMatrix (CStarMatrix.ofMatrix fun i j => operatorEntry T i j) ξ i = T ξ i
  rw [hilbertMatrix_apply]
  change (∑ j, T (tupleSingle j (ξ j)) i) = T ξ i
  have h := congrArg (fun η => T η i) (tuple_eq_sum_single ξ)
  simpa only [map_sum, WithLp.ofLp_sum, Finset.sum_apply] using h.symm

theorem mem_matrixOperatorAlgebra_iff (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (T : FiniteHilbert ι H →L[ℂ] FiniteHilbert ι H) :
    T ∈ matrixOperatorAlgebra (ι := ι) S ↔ ∀ i j, operatorEntry T i j ∈ S := by
  constructor
  · rintro ⟨X, hX, rfl⟩ i j
    change operatorEntry (hilbertMatrix X) i j ∈ S
    rw [operatorEntry_hilbertMatrix]
    exact hX i j
  · intro hT
    exact ⟨CStarMatrix.ofMatrix (fun i j => operatorEntry T i j), hT,
      hilbertMatrix_operatorEntries T⟩

/-- Finite matrix amplification commutes with von Neumann generation. -/
theorem generated_matrixOperatorAlgebra (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    generatedVonNeumannAlgebra (matrixOperatorAlgebra (ι := ι) S) =
      matrixVonNeumann (ι := ι) (generatedVonNeumannAlgebra S) := by
  classical
  apply le_antisymm
  · apply generatedVonNeumannAlgebra_le_of_le
    intro T hT
    change T ∈ matrixVonNeumann (ι := ι) (generatedVonNeumannAlgebra S)
    rw [mem_matrixVonNeumann_iff_entries]
    exact fun i j => subset_generatedVonNeumannAlgebra S
      ((mem_matrixOperatorAlgebra_iff S T).mp hT i j)
  · intro T hT
    have he : ∀ i j, operatorEntry T i j ∈
        Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))) := by
      intro i j
      have h := (mem_matrixVonNeumann_iff_entries _ T).mp hT i j
      change operatorEntry T i j ∈ (generatedVonNeumannAlgebra S : Set _) at h
      rwa [generatedVonNeumannAlgebra_coe] at h
    choose a ha using fun i j => bicommutant_exists_strong_net S (operatorEntry T i j) (he i j)
    let X (d : Finset H × ℕ) : CStarMatrix ι ι (H →L[ℂ] H) :=
      CStarMatrix.ofMatrix fun i j => (a i j d).val
    let b (d : Finset H × ℕ) : Algebra
        (generatedVonNeumannAlgebra (matrixOperatorAlgebra (ι := ι) S)) :=
      ⟨hilbertMatrix (X d), subset_generatedVonNeumannAlgebra _
        (show hilbertMatrix (X d) ∈ matrixOperatorAlgebra S from
          ⟨X d, fun i j => (a i j d).property, rfl⟩)⟩
    apply Generator.Tracial.weak_operator_limit_mem
      (l := (atTop : Filter (Finset H × ℕ))) _ b
    intro ξ η
    have hc (i : ι) : Tendsto (fun d => ∑ j, (a i j d).val (ξ j)) atTop
        (𝓝 (∑ j, operatorEntry T i j (ξ j))) :=
      tendsto_finsetSum _ (fun j _ => ha i j (ξ j))
    have hi (i : ι) : Tendsto
        (fun d => inner ℂ (η i) (∑ j, (a i j d).val (ξ j))) atTop
        (𝓝 (inner ℂ (η i) (∑ j, operatorEntry T i j (ξ j)))) :=
      (continuous_const.inner continuous_id).continuousAt.tendsto.comp (hc i)
    have hs := tendsto_finsetSum Finset.univ (fun i _ => hi i)
    have hrec (i : ι) : (∑ j, operatorEntry T i j (ξ j)) = T ξ i := by
      change (∑ j, T (tupleSingle j (ξ j)) i) = T ξ i
      have h := congrArg (fun ζ => T ζ i) (tuple_eq_sum_single ξ)
      simpa only [map_sum, WithLp.ofLp_sum, Finset.sum_apply] using h.symm
    have happ (d : Finset H × ℕ) (i : ι) :
        ((hilbertMatrix (X d)) ξ).ofLp i = ∑ j, (a i j d).val (ξ j) :=
      hilbertMatrix_apply (X d) ξ i
    change Tendsto (fun d => inner ℂ η ((hilbertMatrix (X d)) ξ)) atTop
      (𝓝 (inner ℂ η (T ξ)))
    simpa only [PiLp.inner_apply, happ, hrec] using hs

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_KaplanskyDensity
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.PopaCorner.instNormedRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Discharging the finite-test Kaplansky density input

The self-adjoint contraction case was proved by the rational bounded
transform. The two-by-two self-adjoint matrix trick gives the general
case without a loss in the contraction bound.
-/

namespace KadisonKastler

open Generator

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance kaplanskyOperatorOrder_radea18_1 : PartialOrder (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrder _
local instance kaplanskyOperatorStarOrder_radea18_1 : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _
theorem norm_entry_le (S : FiniteHilbert (Fin 2) H →L[ℂ] FiniteHilbert (Fin 2) H)
    (i j : Fin 2) : ‖operatorEntry S i j‖ ≤ ‖S‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  change ‖S (tupleSingle j x) i‖ ≤ ‖S‖ * ‖x‖
  have hs : ‖tupleSingle (H := H) j x‖ = ‖x‖ :=
    PiLp.norm_single 2 (fun _ : Fin 2 => H) j x
  exact (PiLp.norm_apply_le _ _).trans ((S.le_opNorm _).trans_eq (by rw [hs]))

/-- Kaplansky density in precisely the finite-test formulation used by
the conditional main theorem. This proof has no published hypotheses. -/
theorem publishedKaplanskyDensity : PublishedKaplanskyDensity.{u} := by
  intro H _ _ _ A T hT hn V ε hε
  classical
  let D := hilbertMatrix (blockOffDiagonal T (star T))
  have hDsa : IsSelfAdjoint D := by
    change star (hilbertMatrix (blockOffDiagonal T (star T))) = _
    rw [← hilbertMatrix_star]
    congr 1
    ext i j : 2
    simp only [CStarMatrix.star_apply]
    fin_cases i <;> fin_cases j <;> simp [blockOffDiagonal]
  have hDn : ‖D‖ ≤ 1 := by
    change ‖hilbertMatrix (blockOffDiagonal T (star T))‖ ≤ 1
    rw [norm_hilbertMatrix, norm_blockOffDiagonal, norm_star, max_self]
    exact hn
  have hD : D ∈ Set.centralizer (Set.centralizer
      (matrixOperatorAlgebra (ι := Fin 2) A : Set _)) := by
    rw [← generatedVonNeumannAlgebra_coe, generated_matrixOperatorAlgebra]
    change D ∈ matrixVonNeumann (generatedVonNeumannAlgebra A)
    apply (mem_matrixVonNeumann_iff_entries _ _).mpr
    intro i j
    change operatorEntry (hilbertMatrix (blockOffDiagonal T (star T))) i j ∈
      generatedVonNeumannAlgebra A
    rw [operatorEntry_hilbertMatrix]
    have ht : T ∈ generatedVonNeumannAlgebra A := by
      change T ∈ (generatedVonNeumannAlgebra A : Set (H →L[ℂ] H))
      rwa [generatedVonNeumannAlgebra_coe]
    fin_cases i <;> fin_cases j
    · exact (generatedVonNeumannAlgebra A).zero_mem
    · exact ht
    · exact (generatedVonNeumannAlgebra A).toStarSubalgebra.star_mem' ht
    · exact (generatedVonNeumannAlgebra A).zero_mem
  obtain ⟨a, han, ha⟩ := selfAdjoint_bicommutant_unitBall_approx
    (matrixOperatorAlgebra (ι := Fin 2) A) D hD hDsa hDn
    (V.image (tupleSingle (H := H) (1 : Fin 2))) hε
  let b := operatorEntry (a : FiniteHilbert (Fin 2) H →L[ℂ] FiniteHilbert (Fin 2) H) 0 1
  refine ⟨⟨b, (mem_matrixOperatorAlgebra_iff A a.val).mp a.property 0 1⟩,
    (norm_entry_le _ 0 1).trans han, ?_⟩
  intro x hx
  have ha' := ha (tupleSingle (1 : Fin 2) x) (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  have hentry : (D (tupleSingle (1 : Fin 2) x) - a.val (tupleSingle (1 : Fin 2) x)) 0 =
      T x - b x := by
    change D (tupleSingle (1 : Fin 2) x) 0 - a.val (tupleSingle (1 : Fin 2) x) 0 = _
    congr 1
    change operatorEntry (hilbertMatrix (blockOffDiagonal T (star T))) 0 1 x = T x
    rw [operatorEntry_hilbertMatrix]
    rfl
  have hle := PiLp.norm_apply_le
    (D (tupleSingle (1 : Fin 2) x) - a.val (tupleSingle (1 : Fin 2) x)) (0 : Fin 2)
  rw [hentry] at hle
  exact hle.trans_lt ha'

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PoissonKernelFormula
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The actual half-plane Poisson kernel

The fixed-law vector averages agree with integration against
`r / (π ((t-s)²+r²))` for every positive height.
-/

namespace KadisonKastler

open MeasureTheory ProbabilityTheory

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def realPoissonKernel (t r s : ℝ) : ℝ := r / (Real.pi * ((t - s) ^ 2 + r ^ 2))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PublishedCentralDecomposition
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero
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

def ScalarCenter {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (M : VonNeumannAlgebra K) : Prop :=
  ∀ T ∈ M, (∀ S ∈ M, S * T = T * S) → ∃ z : ℂ, T = z • (1 : K →L[ℂ] K)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCoreMatrixData
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.PopaCorner.instRing
attribute [-simp] _root_.OAI.KadisonKastler.matrixAlgebraEquiv_apply _root_.OAI.KadisonKastler.spatialTransportEquiv_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Countable equivalent projection families give full matrix corners

The input here is actual projection and partial-isometry data in a represented
von Neumann algebra.  No existence of a semifinite decomposition is assumed as
a published input.  Once such a decomposition has been constructed, the
matrix-corner machinery applies to the explicit operators `v i * star (v j)`.
-/

namespace KadisonKastler

open Generator.Tracial
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

/-- The matrix entries associated to partial isometries with a common initial
projection. -/
def projectionFamilyEntry (v : ℕ → Algebra M) (i j : ℕ) : Algebra M :=
  v i * star (v j)

@[simp] theorem projectionFamilyEntry_star (v : ℕ → Algebra M) (i j : ℕ) :
    star (projectionFamilyEntry v i j) = projectionFamilyEntry v j i := by
  simp only [projectionFamilyEntry, star_mul, star_star]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ScalarBoundaryMean
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
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

abbrev ScalarLInfinity (μ : Measure D) := Lp ℂ ⊤ μ

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProjectionFamilySpaces
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

def operatorKernelClosed (T : H →L[ℂ] H) : ClosedSubmodule ℂ H := ⟨T.ker,T.isClosed_ker⟩

end

end KadisonKastler

end OAI
end


