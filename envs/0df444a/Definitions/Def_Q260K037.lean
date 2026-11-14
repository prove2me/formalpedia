-- Prove2me | Definitions.Def_Q260K037
-- name    : Q260K037
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T08:39:36.875689+00:00
-- url     : https://prove2.me/theorems/28d7aa5f-9be7-46d0-ad86-4be10bf173f6
-- title:
--   Definitions bundle Q260K037 of the split of OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 90 declarations of OpenAI's Lean: 21 definitions and 69 theorems. The definitions and types are `OAI.KadisonKastler.PointedMatrixSites.remoteCopy`, `OAI.KadisonKastler.PointedMatrixSites.remoteDoubleUnitary`, `OAI.KadisonKastler.PointedMatrixSites.sum`, `OAI.KadisonKastler.PublishedModularSpectralResolution`, `OAI.KadisonKastler.UniversalModularCoisometries`, `OAI.KadisonKastler.canonicalModularPositiveCone`, `OAI.KadisonKastler.concreteTwoRatioProductModel`, `OAI.KadisonKastler.constantPointedMatrixProduct`, `OAI.KadisonKastler.fixedPowersProduct`, `OAI.KadisonKastler.modularCyclicPhaseOperator`, `OAI.KadisonKastler.modularOrbit`, `OAI.KadisonKastler.modularOrbitAverage`, `OAI.KadisonKastler.modularStrongGroup`, `OAI.KadisonKastler.modularStrongLimit`, `OAI.KadisonKastler.modularStrongUnitary`, `OAI.KadisonKastler.tomitaCoreCoordinate`, `OAI.KadisonKastler.tomitaGraphComplementRoot`, `OAI.KadisonKastler.tomitaMiddleOperator`, `OAI.KadisonKastler.twoRatioPointedProduct`, `OAI.KadisonKastler.weightedStripCoefficient`, `OAI.KadisonKastler.weightedStripOperator`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `KadisonKastler_CanonicalPositiveCone`, `KadisonKastler_CyclicGaugeKernel`, `KadisonKastler_GraphResolventFunctionalCalculus`, `KadisonKastler_ModularCyclicGroup`, `KadisonKastler_ModularCyclicPhase`, `KadisonKastler_ModularOrbit`, `KadisonKastler_ModularPhaseFunctionalCalculus`, `KadisonKastler_ModularRootCommutation`, `KadisonKastler_ModularStrongContinuity`, `KadisonKastler_ModularStrongLimit`, `KadisonKastler_NormalRepresentationRange`, `KadisonKastler_PointedMatrixSum`, `KadisonKastler_PointedPowerProduct`, `KadisonKastler_PositiveReferenceHaagerup`, `KadisonKastler_PublishedModularSpectral`, `KadisonKastler_ReducingCommutantCorner`, `KadisonKastler_RemoteProductCopy`, `KadisonKastler_StateCentralSequenceAlgebra`, `KadisonKastler_StateCommutatorAlgebra`, `KadisonKastler_TomitaClosedOperator`, `KadisonKastler_TomitaComplementaryRoot`, `KadisonKastler_TomitaCoreCoordinates`, `KadisonKastler_TomitaGraphInvolution`, `KadisonKastler_TomitaLinearPolarCoordinates`, `KadisonKastler_TomitaMiddleCore`, `KadisonKastler_TomitaPolarResolventSymmetry`, `KadisonKastler_TomitaResolventDenseRange`, `KadisonKastler_TomitaResolventEndpoints`, `KadisonKastler_TwoRatioPointedConstruction`, `KadisonKastler_TwoRatioProductConstruction`, `KadisonKastler_WeightedStripAverage`, `KadisonKastler_WeightedStripFactorization`, `KadisonKastler_WeightedStripOperator`.
--
--   **Imports.** It imports the bundles `Q260K034` and `Q260K035` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q260K042`, `Q260K043` and `Q260K044`; the statements `OAI.KadisonKastler.PointedMatrixSites.remoteCopy_scales`, `OAI.KadisonKastler.PointedMatrixSites.spatial_remote_adjoint_commutator_tendsto`, `OAI.KadisonKastler.PointedMatrixSites.spatial_remote_commutator_tendsto`, `OAI.KadisonKastler.PointedMatrixSites.spatial_universal_modular_coisometries`, `OAI_KadisonKastler_TwoRatioProductModel_tensor_typeIII1`, `OAI.KadisonKastler.TwoRatioProductModel.tensor_typeIII1_general`, `OAI.KadisonKastler.TypeIIIFactor.exists_positive_unit_state_representative`, `OAI_KadisonKastler_algebra_strong_tendsto_of_reference`, `OAI_KadisonKastler_commutant_cyclic_of_separating_reference`, `OAI_KadisonKastler_commuting_kms_actions_eq`, `OAI.KadisonKastler.constructedCore_equiv_of_statePreserving`, `OAI.KadisonKastler.constructedCore_equiv_of_two_states`, `OAI.KadisonKastler.constructedCore_not_finite`, `OAI.KadisonKastler.constructedCore_not_typeI`, `OAI.KadisonKastler.constructedCore_traceSymmetry`, `OAI.KadisonKastler.constructedFactorialCore_projectionSemifinite`, `OAI.KadisonKastler.constructedFactorialCore_typeIIInfinity`, `OAI.KadisonKastler.coreTraceEmbedding_vector_symmetry`, `OAI.KadisonKastler.exists_strict_pinching_refinement`, `OAI.KadisonKastler.exists_uniform_pinching_gap`, `OAI.KadisonKastler.exists_uniform_projection_gap`, `OAI.KadisonKastler.kmsGroup_eq_constructed`, `OAI_KadisonKastler_local_scaling_commutator_tendsto`, `OAI_KadisonKastler_maximal_admissibleFamily_gap`, `OAI.KadisonKastler.nearly_full_corner_projection_witness`, `OAI.KadisonKastler.positive_corner_projection_witness`, `OAI.KadisonKastler.positive_reference_noncollinear_projection_witness`, `OAI.KadisonKastler.positive_unitary_orbit_dense`, `OAI_KadisonKastler_regularCore_not_factor_of_corner_trace_vector`, `OAI_KadisonKastler_regularCore_not_factor_of_tracial_vector`, `OAI.KadisonKastler.stateGroup_commutes_modular`, `OAI.KadisonKastler.stateHomogeneity_of_modular_coisometries`, `OAI.KadisonKastler.state_bicentralizer_scalar_of_modular_coisometries`, `OAI.KadisonKastler.twoStateCorner_positive`, `OAI.KadisonKastler.twoStateCorner_positive_iff`, `OAI.KadisonKastler.uniform_expected_matrix_typeIII1_stability`, `OAI.KadisonKastler.uniform_expected_models_typeIII1_stability` and `OAI.KadisonKastler.uniform_properlyInfinite_strong_stability_of_product_models`; the proofs of `OAI.KadisonKastler.PointedMatrixSites.exists_spatial_scaling_conjugations`, `OAI.KadisonKastler.PointedMatrixSites.remoteCopy_scales`, `OAI.KadisonKastler.PointedMatrixSites.spatial_remote_adjoint_commutator_tendsto`, `OAI.KadisonKastler.PointedMatrixSites.spatial_remote_commutator_tendsto`, `OAI_KadisonKastler_TwoRatioProductModel_tensor_typeIII1`, `OAI_KadisonKastler_antiStar_derivation_inner_of_simple`, `OAI_KadisonKastler_centralPairDecomposition_of_rankModel`, `OAI_KadisonKastler_commuting_kms_actions_eq`, `OAI.KadisonKastler.constructedCore_equiv_of_statePreserving`, `OAI.KadisonKastler.constructedFactorialCore_typeIIInfinity`, `OAI.KadisonKastler.cyclicCommonMatrixUnits_generated`, `OAI.KadisonKastler.exists_selfAdjoint_split_of_reducing_finite_corner`, `OAI.KadisonKastler.exists_strict_pinching_refinement`, `OAI.KadisonKastler.exists_uniform_pinching_gap`, `OAI.KadisonKastler.exists_uniform_projection_gap`, `OAI_KadisonKastler_exists_unitary_embedding_of_invariant_group_in_algebra`, `OAI_KadisonKastler_finite_factor_of_near_II1`, `OAI.KadisonKastler.modularCore_equiv_of_statePreserving`, `OAI.KadisonKastler.modularCore_equiv_of_two_states`, `OAI.KadisonKastler.nearly_full_corner_projection_witness`, `OAI.KadisonKastler.norm_add_positive_factor_commutant`, `OAI.KadisonKastler.positive_corner_projection_witness`, `OAI.KadisonKastler.positive_unitary_orbit_dense`, `OAI.KadisonKastler.publishedFactorialModularCore`, `OAI.KadisonKastler.scaling_vector_limit`, `OAI_KadisonKastler_simple_extension_implementer_mem_range`, `OAI.KadisonKastler.stateConjugate_vector_norm_sq_le`, `OAI.KadisonKastler.stateOrbitCore_compose_subset`, `OAI.KadisonKastler.state_bicentralizer_scalar_of_modular_coisometries`, `OAI.KadisonKastler.twoStateCorner_polar_conjugation`, `OAI.KadisonKastler.twoStateCorner_positive`, `OAI.KadisonKastler.uniform_expected_matrix_typeIII1_stability`, `OAI.KadisonKastler.uniform_expected_models_typeIII1_stability` and `OAI.KadisonKastler.uniform_properlyInfinite_strong_stability_of_product_models`.
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
import Definitions.Def_Q260K034
import Definitions.Def_Q260K035

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TomitaClosedOperator
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The closed Tomita operator in linear coordinates

The fixed antiunitary in the second coordinate turns the Tomita operator
into a complex-linear, densely defined closed operator. Its graph is the
previously constructed closed graph, not an assumed modular object.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

theorem tomitaProductGraph_no_vertical (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (x : H × H) (hx : x ∈ tomitaProductGraph M J Ω c) (hzero : x.1 = 0) :
    x.2 = 0 := by
  have h := rescaledGraph_no_vertical J Ω c hsep
    (tomitaProductCoordinates.symm x) hx hzero
  exact congrArg (fun v : TomitaGraphHilbert H => v 1) h

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TomitaGraphInvolution
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.CommonTracialPositionData.rightEquiv_transportEquiv _root_.OAI.KadisonKastler.FiniteInnerAverage.algebraApply_sub _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.StandardTracialPosition.diagonalRepresentation_vector _root_.OAI.KadisonKastler.algebraConstantField_coe _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.concreteDerivation_apply _root_.OAI.KadisonKastler.concreteDiagonalSequenceUnitary_coe _root_.OAI.KadisonKastler.concreteDiagonalSequence_apply _root_.OAI.KadisonKastler.concreteDiagonalUnitary_coe _root_.OAI.KadisonKastler.constantAlgebraUnitaryFamily_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.cyclicOrbitEquiv_val _root_.OAI.KadisonKastler.cyclicOrbitHom_apply _root_.OAI.KadisonKastler.faithfulCyclicEquiv_coe _root_.OAI.KadisonKastler.faithfulCyclicHom_apply _root_.OAI.KadisonKastler.graphCoordinateScale_one _root_.OAI.KadisonKastler.graphCoordinateScale_zero _root_.OAI.KadisonKastler.graphIsometry_one _root_.OAI.KadisonKastler.graphIsometry_zero _root_.OAI.KadisonKastler.matrixClosureVectorTrace_apply _root_.OAI.KadisonKastler.matrixLiftUnitaryAt_coe _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.minimalCyclicRetraction_compression _root_.OAI.KadisonKastler.normalCyclicEquiv_val _root_.OAI.KadisonKastler.normalCyclicHom_apply _root_.OAI.KadisonKastler.normalPairEquiv_coe _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.regularCoreDualEquiv_apply _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.spatialLeftAlgebraHom_val _root_.OAI.KadisonKastler.spatialTransportEquiv_apply _root_.OAI.KadisonKastler.spatialTransportEquiv_vector _root_.OAI.KadisonKastler.tomitaGraphFirst_adjoint_apply _root_.OAI.KadisonKastler.tomitaGraphFirst_apply _root_.OAI.KadisonKastler.tomitaLinearPolarUnitary_apply _root_.OAI.KadisonKastler.tomitaLinearPolarUnitary_symm_apply _root_.OAI.KadisonKastler.tomitaPolarCoordinates_root _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.typeICyclicHom_apply _root_.OAI.KadisonKastler.typeICyclicOperator_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonKastler.vectorStateCommutator_add _root_.OAI.KadisonKastler.vectorStateCommutator_apply _root_.OAI.KadisonKastler.vectorStateCommutator_one _root_.OAI.KadisonKastler.vectorStateCommutator_smul _root_.OAI.KadisonKastler.vectorStateCommutator_sub _root_.OAI.KadisonKastler.vectorStateCommutator_zero _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply _root_.OAI.KadisonSimilarity.predualRestriction_apply _root_.OAI.KadisonSimilarity.tracialInclusionIsometry_vector _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The involution on the closed Tomita graph

Taking adjoints on the algebraic core becomes a continuous conjugate-linear
coordinate swap. Hence its involution identity survives graph closure.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

theorem rescaledGraph_no_horizontal (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (ξ : TomitaGraphHilbert H) (hξ : ξ ∈ rescaledGraphSubspace M J Ω 1)
    (hzero : ξ 1 = 0) : ξ = 0 := by
  have hflip := rescaledGraph_no_vertical J Ω 1 hsep (tomitaGraphFlip J ξ)
    (tomitaGraphFlip_mem J Ω hξ) (by simp [hzero])
  exact (tomitaGraphFlip J).injective (hflip.trans (map_zero _).symm)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TomitaResolventEndpoints
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.canonicalInitialSpaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.centralVectorSpace_complete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.matrixCentralVectorSpace_complete _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.selfAdjointVectorSpace_complete _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Absence of endpoint eigenvectors for the Tomita resolvent -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

theorem one_sub_graphResolvent_eq_zero_iff (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω)) (x : H) :
    (1 - graphResolvent M J Ω 1) x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    let P := rescaledGraphSubspace M J Ω 1
    let v := P.starProjection (Generator.tupleSingle 0 x)
    have hfirst : v 0 = x := by
      change x - v 0 = 0 at hx
      exact (sub_eq_zero.mp hx).symm
    have hn := P.norm_starProjection_apply_le (Generator.tupleSingle 0 x)
    have hs : ‖Generator.tupleSingle (H := H) (0 : Fin 2) x‖ = ‖x‖ :=
      PiLp.norm_single 2 (fun _ : Fin 2 => H) 0 x
    rw [hs] at hn
    change ‖v‖ ≤ ‖x‖ at hn
    have hsq : ‖v 0‖ ^ 2 + ‖v 1‖ ^ 2 = ‖v‖ ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2]
      simp only [Fin.sum_univ_two]
    have hsecond : v 1 = 0 := by
      apply norm_eq_zero.mp
      rw [hfirst] at hsq
      have hn0 := norm_nonneg v
      have hn1 := norm_nonneg (v 1)
      nlinarith [sq_nonneg (‖v 1‖)]
    have hv := rescaledGraph_no_horizontal J Ω hsep v
      (P.starProjection_apply_mem _) hsecond
    have hf := congrArg (fun w : TomitaGraphHilbert H => w 0) hv
    exact hfirst.symm.trans hf
  · rintro rfl
    exact map_zero _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TomitaPolarResolventSymmetry
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.canonicalInitialSpaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.centralVectorSpace_complete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.matrixCentralVectorSpace_complete _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.selfAdjointVectorSpace_complete _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Polar conjugation interchanges the resolvent and its complement -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

theorem tomitaPolarCoordinates_first (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) (x : H) :
    (tomitaPolarCoordinates J Ω hsep hcyc x).val 0 = tomitaGraphRoot (M := M) J Ω x := by
  let U := tomitaPolarCoordinates J Ω hsep hcyc
  have hc : IsClosed {x : H | (U x).val 0 = tomitaGraphRoot (M := M) J Ω x} :=
    isClosed_eq ((PiLp.continuous_apply 2 (fun _ : Fin 2 => H) 0).comp
      (continuous_subtype_val.comp U.continuous)) (tomitaGraphRoot J Ω).continuous
  refine (tomitaGraphRoot_dense J Ω hsep hcyc).induction ?_ hc x
  rintro _ ⟨y, rfl⟩
  change (tomitaPolarCoordinates J Ω hsep hcyc (tomitaGraphRoot (M := M) J Ω y)).val 0 = _
  rw [tomitaPolarCoordinates_root, tomitaGraphFirst_adjoint_apply]
  change graphResolvent M J Ω 1 y = tomitaGraphRoot J Ω (tomitaGraphRoot J Ω y)
  exact (congrArg (fun T : H →L[ℂ] H => T y) (tomitaGraphRoot_square J Ω)).symm

theorem tomitaPolarCoordinates_conjugation (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) (x : H) :
    tomitaPolarCoordinates J Ω hsep hcyc (tomitaPolarConjugation J Ω hsep hcyc x) =
      tomitaGraphAntiunitary J Ω (tomitaPolarCoordinates J Ω hsep hcyc x) := by
  change (tomitaPolarCoordinates J Ω hsep hcyc)
    ((tomitaPolarCoordinates J Ω hsep hcyc).symm _) = _
  exact LinearIsometryEquiv.apply_symm_apply _ _

theorem tomitaPolarCoordinates_second (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) (x : H) :
    (tomitaPolarCoordinates J Ω hsep hcyc x).val 1 =
      J (tomitaGraphRoot (M := M) J Ω (tomitaPolarConjugation J Ω hsep hcyc x)) := by
  have he := congrArg (fun v : rescaledGraphSubspace M J Ω 1 => v.val 0)
    (tomitaPolarCoordinates_conjugation J Ω hsep hcyc x)
  rw [tomitaPolarCoordinates_first] at he
  change tomitaGraphRoot J Ω (tomitaPolarConjugation J Ω hsep hcyc x) =
    J.symm ((tomitaPolarCoordinates J Ω hsep hcyc x).val 1) at he
  rw [he, J.apply_symm_apply]

theorem inner_tomitaGraphRoot (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (x y : H) :
    inner ℂ (tomitaGraphRoot (M := M) J Ω x) (tomitaGraphRoot (M := M) J Ω y) =
      inner ℂ x (graphResolvent M J Ω 1 y) := by
  rw [← ContinuousLinearMap.adjoint_inner_right]
  have hs : (tomitaGraphRoot (M := M) J Ω).adjoint = tomitaGraphRoot J Ω :=
    (tomitaGraphRoot_selfAdjoint J Ω).star_eq
  rw [hs]
  exact congrArg (inner ℂ x)
    (congrArg (fun T : H →L[ℂ] H => T y) (tomitaGraphRoot_square J Ω))

theorem tomitaPolarResolvent_inner (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) (x y : H) :
    inner ℂ x y = inner ℂ x (graphResolvent M J Ω 1 y) +
      inner ℂ x (conjugationOperator (tomitaPolarConjugation J Ω hsep hcyc)
        (graphResolvent M J Ω 1) y) := by
  let U := tomitaPolarCoordinates J Ω hsep hcyc
  let C := tomitaPolarConjugation J Ω hsep hcyc
  have hprod : inner ℂ x y = inner ℂ (U x).val (U y).val := (U.inner_map_map x y).symm
  rw [PiLp.inner_apply, Fin.sum_univ_two] at hprod
  rw [tomitaPolarCoordinates_first, tomitaPolarCoordinates_first,
    tomitaPolarCoordinates_second, tomitaPolarCoordinates_second] at hprod
  rw [conjugateIsometry_inner, inner_tomitaGraphRoot, inner_tomitaGraphRoot] at hprod
  have hc := conjugateIsometry_inner C (C x) (graphResolvent M J Ω 1 (C y))
  rw [tomitaPolarConjugation_involutive J Ω hsep hcyc] at hc
  exact hprod.trans (congrArg (fun z : ℂ => inner ℂ x (graphResolvent M J Ω 1 y) + z) hc.symm)

/-- The polar conjugation exchanges the two endpoints of the graph spectrum. -/
theorem tomitaPolarConjugation_resolvent (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) :
    conjugationOperator (tomitaPolarConjugation J Ω hsep hcyc) (graphResolvent M J Ω 1) =
      1 - graphResolvent M J Ω 1 := by
  let R := graphResolvent M J Ω 1
  let C := conjugationOperator (tomitaPolarConjugation J Ω hsep hcyc) R
  have hs : R + C = 1 := by
    ext x
    apply ext_inner_left ℂ
    intro y
    change inner ℂ y (R x + C x) = inner ℂ y x
    rw [inner_add_right]
    exact (tomitaPolarResolvent_inner J Ω hsep hcyc y x).symm
  change C = 1 - R
  calc
    C = (R + C) - R := by abel
    _ = 1 - R := by rw [hs]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TomitaResolventDenseRange
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The dense range used for logarithmic approximation

The product `R(1-R)` of the graph resolvent and its complement has dense range.
This is the precise dense set on which the weighted scalar estimates apply.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

theorem graphResolvent_injective (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) :
    Function.Injective (graphResolvent M J Ω 1) := by
  intro x y he
  apply sub_eq_zero.mp
  apply (graphResolvent_eq_zero_iff J Ω 1 hsep hcyc (x - y)).mp
  rw [map_sub, he, sub_self]

theorem one_sub_graphResolvent_injective (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω)) :
    Function.Injective ((1 : H →L[ℂ] H) - graphResolvent M J Ω 1) := by
  intro x y he
  apply sub_eq_zero.mp
  apply (one_sub_graphResolvent_eq_zero_iff J Ω hsep (x - y)).mp
  rw [map_sub, he, sub_self]

theorem graphResolventCutoff_selfAdjoint (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) :
    IsSelfAdjoint (graphResolventCutoff M J Ω) := by
  have hr := (graphResolvent_positive (M := M) J Ω 1).isSelfAdjoint
  change star (graphResolvent M J Ω 1 * (1 - graphResolvent M J Ω 1)) =
    graphResolvent M J Ω 1 * (1 - graphResolvent M J Ω 1)
  rw [star_mul, star_sub, star_one, hr.star_eq]
  noncomm_ring

theorem graphResolventCutoff_dense (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) :
    DenseRange (graphResolventCutoff M J Ω) := by
  apply selfAdjoint_denseRange _ (graphResolventCutoff_selfAdjoint J Ω)
  exact (graphResolvent_injective J Ω hsep hcyc).comp
    (one_sub_graphResolvent_injective J Ω hsep)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_GraphResolventFunctionalCalculus
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Functional calculus for the bounded Tomita resolvent

The weighted scalar estimates apply to the graph resolvent because its
spectrum is contained in `[0,1]`.  All assertions here concern bounded
operators; no unbounded functional calculus is assumed.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

theorem graphResolvent_spectrum_bounds (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    {s : ℝ} (hs : s ∈ spectrum ℝ (graphResolvent M J Ω 1)) : 0 ≤ s ∧ s ≤ 1 := by
  cases subsingleton_or_nontrivial H with
  | inl h =>
    rw [spectrum.of_subsingleton] at hs
    exact False.elim hs
  | inr h =>
    have hp : 0 ≤ graphResolvent M J Ω 1 :=
      (ContinuousLinearMap.nonneg_iff_isPositive _).mpr (graphResolvent_positive J Ω 1)
    exact ⟨spectrum_nonneg_of_nonneg hp hs,
      (le_abs_self s).trans ((spectrum.norm_le_norm_of_mem hs).trans
      (graphResolvent_norm_le_one J Ω 1))⟩

theorem regularizedLogScalar_continuousOn (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    {ε : ℝ} (hε : 0 < ε) :
    ContinuousOn (regularizedLogScalar ε) (spectrum ℝ (graphResolvent M J Ω 1)) := by
  intro s hs
  have hb := graphResolvent_spectrum_bounds J Ω hs
  have hm : ContinuousAt (fun r : ℝ => 1 - r + ε) s := by fun_prop
  have hp : ContinuousAt (fun r : ℝ => r + ε) s := by fun_prop
  exact ((Real.continuousAt_log (by linarith)).comp hm).continuousWithinAt.sub
    (((Real.continuousAt_log (by linarith)).comp hp).continuousWithinAt)

theorem regularizedModularLog_eq_cfc (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    {ε : ℝ} (hε : 0 < ε) :
    (regularizedModularLog M J Ω ε).val =
      cfc (regularizedLogScalar ε) (graphResolvent M J Ω 1) := by
  let R := graphResolvent M J Ω 1
  have hR : IsSelfAdjoint R := (graphResolvent_positive J Ω 1).isSelfAdjoint
  have hp : ContinuousOn Real.log ((fun s : ℝ => s + ε) '' spectrum ℝ R) := by
    rintro _ ⟨s, hs, rfl⟩
    have hb := graphResolvent_spectrum_bounds J Ω hs
    exact (Real.continuousAt_log (by linarith)).continuousWithinAt
  have hm : ContinuousOn Real.log ((fun s : ℝ => 1 - s + ε) '' spectrum ℝ R) := by
    rintro _ ⟨s, hs, rfl⟩
    have hb := graphResolvent_spectrum_bounds J Ω hs
    exact (Real.continuousAt_log (by linarith)).continuousWithinAt
  have hap : cfc (fun s : ℝ => s + ε) R = R + algebraMap ℝ (H →L[ℂ] H) ε := by
    rw [cfc_add_const ε (fun s : ℝ => s) R (by fun_prop) hR, cfc_id' ℝ R hR]
  have ham : cfc (fun s : ℝ => 1 - s + ε) R =
      1 - R + algebraMap ℝ (H →L[ℂ] H) ε := by
    rw [cfc_add_const ε (fun s : ℝ => 1 - s) R (by fun_prop) hR,
      cfc_sub (fun _ : ℝ => 1) (fun s : ℝ => s) R (by fun_prop) (by fun_prop),
      cfc_const_one ℝ R hR, cfc_id' ℝ R hR]
  have hcp := cfc_comp Real.log (fun s : ℝ => s + ε) R hR hp (by fun_prop)
  have hcm := cfc_comp Real.log (fun s : ℝ => 1 - s + ε) R hR hm (by fun_prop)
  rw [hap] at hcp
  rw [ham] at hcm
  change CFC.log (1 - R + algebraMap ℝ (H →L[ℂ] H) ε) -
    CFC.log (R + algebraMap ℝ (H →L[ℂ] H) ε) = _
  rw [CFC.log, CFC.log, ← hcp, ← hcm]
  symm
  exact cfc_sub _ _ R (hm.comp (by fun_prop) (Set.mapsTo_image _ _))
    (hp.comp (by fun_prop) (Set.mapsTo_image _ _))

theorem graphResolventCutoff_eq_cfc (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) :
    graphResolventCutoff M J Ω =
      cfc (fun s : ℝ => s * (1 - s)) (graphResolvent M J Ω 1) := by
  have hR := (graphResolvent_positive (M := M) J Ω 1).isSelfAdjoint
  rw [cfc_mul (fun s : ℝ => s) (fun s : ℝ => 1 - s) _ (by fun_prop) (by fun_prop),
    cfc_sub (fun _ : ℝ => 1) (fun s : ℝ => s) _ (by fun_prop) (by fun_prop),
    cfc_id' ℝ _ hR, cfc_const_one ℝ _ hR]
  rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularPhaseFunctionalCalculus
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Weighted norm convergence of the modular phases

Complex continuous functional calculus turns the scalar phase bound into
an operator bound on the dense range of `R(1-R)`.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

theorem regularizedLogScalar_complex_continuousOn (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    {ε : ℝ} (hε : 0 < ε) :
    ContinuousOn (fun z : ℂ => (regularizedLogScalar ε z.re : ℂ))
      (spectrum ℂ (graphResolvent M J Ω 1)) := by
  have hR := (graphResolvent_positive (M := M) J Ω 1).isSelfAdjoint
  exact Complex.continuous_ofReal.comp_continuousOn
    ((regularizedLogScalar_continuousOn J Ω hε).comp
      Complex.continuous_re.continuousOn hR.spectrumRestricts.subset_preimage)

theorem modularPhaseScalar_continuousOn (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ContinuousOn (modularPhaseScalar t ε) (spectrum ℂ (graphResolvent M J Ω 1)) :=
  Complex.continuous_exp.comp_continuousOn
    (continuousOn_const.mul (continuousOn_const.mul
      (regularizedLogScalar_complex_continuousOn J Ω hε)))

theorem regularizedModularGroup_eq_cfc (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    (regularizedModularGroup M J Ω ε (Multiplicative.ofAdd t) : H →L[ℂ] H) =
      cfc (modularPhaseScalar t ε) (graphResolvent M J Ω 1) := by
  let R := graphResolvent M J Ω 1
  let f : ℂ → ℂ := fun z => Complex.I * ((t : ℂ) * (regularizedLogScalar ε z.re : ℂ))
  have hR : IsSelfAdjoint R := (graphResolvent_positive J Ω 1).isSelfAdjoint
  have hl := regularizedLogScalar_complex_continuousOn (M := M) J Ω hε
  have hf : ContinuousOn f (spectrum ℂ R) :=
    continuousOn_const.mul (continuousOn_const.mul hl)
  have hc : cfc f R = Complex.I • ((t : ℂ) • (regularizedModularLog M J Ω ε).val) := by
    unfold f
    rw [cfc_const_mul Complex.I (fun z : ℂ => (t : ℂ) * (regularizedLogScalar ε z.re : ℂ)) R
      (continuousOn_const.mul hl),
      cfc_const_mul (t : ℂ) (fun z : ℂ => (regularizedLogScalar ε z.re : ℂ)) R hl,
      ← cfc_real_eq_complex (regularizedLogScalar ε) hR,
      ← regularizedModularLog_eq_cfc J Ω hε]
  change NormedSpace.exp (Complex.I • ((t : ℂ) • (regularizedModularLog M J Ω ε).val)) = _
  rw [← hc, ← CFC.complex_exp_eq_normedSpace_exp (cfc_predicate f R),
    ← cfc_comp Complex.exp f R hR.isStarNormal Complex.continuous_exp.continuousOn hf]
  rfl

theorem graphResolventCutoff_eq_complex_cfc (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) :
    graphResolventCutoff M J Ω =
      cfc (fun z : ℂ => (z.re * (1 - z.re) : ℝ)) (graphResolvent M J Ω 1) := by
  rw [graphResolventCutoff_eq_cfc,
    cfc_real_eq_complex _ (graphResolvent_positive J Ω 1).isSelfAdjoint]

/-- A bound uniform in the spectral parameter, after the dense cutoff. -/
theorem regularizedModularGroup_weighted_bound (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (t : ℝ) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ‖((regularizedModularGroup M J Ω ε (Multiplicative.ofAdd t) : H →L[ℂ] H) -
      (regularizedModularGroup M J Ω δ (Multiplicative.ofAdd t) : H →L[ℂ] H)) *
      graphResolventCutoff M J Ω‖ ≤ |t| * |ε - δ| := by
  have he := modularPhaseScalar_continuousOn (M := M) J Ω t hε
  have hd := modularPhaseScalar_continuousOn (M := M) J Ω t hδ
  rw [regularizedModularGroup_eq_cfc J Ω t hε, regularizedModularGroup_eq_cfc J Ω t hδ,
    graphResolventCutoff_eq_complex_cfc, ← cfc_sub _ _ _ he hd,
    ← cfc_mul (fun z => modularPhaseScalar t ε z - modularPhaseScalar t δ z)
      (fun z : ℂ => (z.re * (1 - z.re) : ℝ)) _ (he.sub hd) (by fun_prop)]
  apply norm_cfc_le (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  intro z hz
  have hR := (graphResolvent_positive (M := M) J Ω 1).isSelfAdjoint
  have hb := graphResolvent_spectrum_bounds J Ω (hR.spectrumRestricts.subset_preimage hz)
  change 0 ≤ z.re ∧ z.re ≤ 1 at hb
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hb.1 (sub_nonneg.mpr hb.2)), mul_comm]
  simpa only [modularPhaseScalar, Complex.ofReal_mul] using
    weighted_modularPhase_difference t z.re ε δ hb.1 hb.2 hε hδ

theorem regularizedModularGroup_cutoff_apply_bound (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (t : ℝ) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (x : H) :
    ‖(regularizedModularGroup M J Ω ε (Multiplicative.ofAdd t) : H →L[ℂ] H)
        (graphResolventCutoff M J Ω x) -
      (regularizedModularGroup M J Ω δ (Multiplicative.ofAdd t) : H →L[ℂ] H)
        (graphResolventCutoff M J Ω x)‖ ≤ |t| * |ε - δ| * ‖x‖ := by
  change ‖(((regularizedModularGroup M J Ω ε (Multiplicative.ofAdd t) : H →L[ℂ] H) -
    (regularizedModularGroup M J Ω δ (Multiplicative.ofAdd t) : H →L[ℂ] H)) *
      graphResolventCutoff M J Ω) x‖ ≤ _
  exact (ContinuousLinearMap.le_opNorm _ x).trans
    (mul_le_mul_of_nonneg_right (regularizedModularGroup_weighted_bound J Ω t hε hδ)
      (norm_nonneg x))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularStrongLimit
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.normUltraproductNontrivial _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The strong limit of the regularized modular groups

The weighted estimates make the approximants Cauchy on a dense range.
Their contraction bounds extend convergence to every vector. Group laws
and inverse operators then pass to the strong limit.
-/

namespace KadisonKastler

open Filter TopologicalSpace
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

theorem modularApproximation_cutoff_cauchy (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (t : ℝ) (x : H) :
    CauchySeq (fun n => modularApproximation M J Ω n t (graphResolventCutoff M J Ω x)) := by
  apply Metric.cauchySeq_iff.mpr
  intro η hη
  let C := |t| * ‖x‖
  have hC : 0 ≤ C := mul_nonneg (abs_nonneg _) (norm_nonneg _)
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp modularRegularizationScale_tendsto.cauchySeq
    (η / (C + 1)) (by positivity)
  refine ⟨N, fun m hm n hn => ?_⟩
  have hd := hN m hm n hn
  have hb := regularizedModularGroup_cutoff_apply_bound (M := M) J Ω t
    (modularRegularizationScale_pos m) (modularRegularizationScale_pos n) x
  have hh : C * dist (modularRegularizationScale m) (modularRegularizationScale n) ≤
      (C + 1) * dist (modularRegularizationScale m) (modularRegularizationScale n) := by
    gcongr
    linarith
  have hl : (C + 1) * dist (modularRegularizationScale m) (modularRegularizationScale n) < η := by
    have := (lt_div_iff₀ (show 0 < C + 1 by positivity)).mp hd
    linarith
  rw [dist_eq_norm]
  calc
    _ ≤ C * dist (modularRegularizationScale m) (modularRegularizationScale n) := by
      simpa only [modularApproximation, C, Real.dist_eq, mul_assoc, mul_left_comm,
        mul_comm] using hb
    _ ≤ _ := hh
    _ < _ := hl

variable [SeparableSpace H]

theorem exists_modularStrongLimit (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) (t : ℝ) :
    ∃ T : H →L[ℂ] H, ‖T‖ ≤ 1 ∧
      ∀ x, Tendsto (fun n => modularApproximation M J Ω n t x) atTop (𝓝 (T x)) := by
  obtain ⟨ξ, hξ⟩ := exists_dense_seq H
  have hd := (graphResolventCutoff_dense J Ω hsep hcyc).comp hξ
    (graphResolventCutoff M J Ω).continuous
  exact exists_strong_limit_of_dense_contractions _ hd
    (fun n => modularApproximation M J Ω n t)
    (fun n => modularApproximation_contracts J Ω n t)
    (fun j => modularApproximation_cutoff_cauchy J Ω t (ξ j))

def modularStrongLimit (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) (t : ℝ) : H →L[ℂ] H :=
  (exists_modularStrongLimit J Ω hsep hcyc t).choose

theorem modularApproximation_tendsto (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) (t : ℝ) (x : H) :
    Tendsto (fun n => modularApproximation M J Ω n t x) atTop
      (𝓝 (modularStrongLimit J Ω hsep hcyc t x)) :=
  (exists_modularStrongLimit J Ω hsep hcyc t).choose_spec.2 x

theorem modularStrongLimit_zero (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) :
    modularStrongLimit J Ω hsep hcyc 0 = 1 := by
  ext x
  have ht := modularApproximation_tendsto J Ω hsep hcyc 0 x
  have he (n : ℕ) : modularApproximation M J Ω n 0 x = x := by
    change (regularizedModularGroup M J Ω (modularRegularizationScale n) 1 : H →L[ℂ] H) x = x
    rw [map_one]
    rfl
  simp only [he] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

theorem modularStrongLimit_add (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) (s t : ℝ) :
    modularStrongLimit J Ω hsep hcyc (s + t) =
      modularStrongLimit J Ω hsep hcyc s * modularStrongLimit J Ω hsep hcyc t := by
  ext x
  have ht := tendsto_mul_contractions (fun n => modularApproximation M J Ω n s)
    (fun n => modularApproximation M J Ω n t) _ _
    (fun n => modularApproximation_contracts J Ω n s)
    (modularApproximation_tendsto J Ω hsep hcyc s)
    (modularApproximation_tendsto J Ω hsep hcyc t) x
  have he (n : ℕ) : modularApproximation M J Ω n s * modularApproximation M J Ω n t =
      modularApproximation M J Ω n (s + t) := by
    exact (congrArg (fun u : unitary (H →L[ℂ] H) => u.val)
      ((regularizedModularGroup M J Ω (modularRegularizationScale n)).map_mul
        (Multiplicative.ofAdd s) (Multiplicative.ofAdd t))).symm
  simp only [he] at ht
  exact tendsto_nhds_unique (modularApproximation_tendsto J Ω hsep hcyc (s + t) x) ht

theorem modularStrongLimit_norm_map (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) (t : ℝ) (x : H) :
    ‖modularStrongLimit J Ω hsep hcyc t x‖ = ‖x‖ := by
  have ht := (modularApproximation_tendsto J Ω hsep hcyc t x).norm
  have he (n : ℕ) : ‖modularApproximation M J Ω n t x‖ = ‖x‖ :=
    Unitary.norm_map _ x
  simp only [he] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

/-- The limiting group consists of actual unitaries, with inverse at negative time. -/
def modularStrongUnitary (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) (t : ℝ) : unitary (H →L[ℂ] H) :=
  Unitary.linearIsometryEquiv.symm
    { (modularStrongLimit J Ω hsep hcyc t).toLinearMap with
      invFun := modularStrongLimit J Ω hsep hcyc (-t)
      left_inv := fun x => by
        change (modularStrongLimit J Ω hsep hcyc (-t) *
          modularStrongLimit J Ω hsep hcyc t) x = x
        rw [← modularStrongLimit_add, neg_add_cancel, modularStrongLimit_zero]
        rfl
      right_inv := fun x => by
        change (modularStrongLimit J Ω hsep hcyc t *
          modularStrongLimit J Ω hsep hcyc (-t)) x = x
        rw [← modularStrongLimit_add, add_neg_cancel, modularStrongLimit_zero]
        rfl
      norm_map' := modularStrongLimit_norm_map J Ω hsep hcyc t }

def modularStrongGroup (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) : Multiplicative ℝ →* unitary (H →L[ℂ] H) where
  toFun t := modularStrongUnitary J Ω hsep hcyc t.toAdd
  map_one' := by
    apply Subtype.ext
    exact modularStrongLimit_zero J Ω hsep hcyc
  map_mul' s t := by
    apply Subtype.ext
    exact modularStrongLimit_add J Ω hsep hcyc s.toAdd t.toAdd

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularStrongContinuity
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.normUltraproductNontrivial _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.CommonTracialPositionData.rightEquiv_transportEquiv _root_.OAI.KadisonKastler.FiniteInnerAverage.algebraApply_sub _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.StandardTracialPosition.diagonalRepresentation_vector _root_.OAI.KadisonKastler.algebraConstantField_coe _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.concreteDerivation_apply _root_.OAI.KadisonKastler.concreteDiagonalSequenceUnitary_coe _root_.OAI.KadisonKastler.concreteDiagonalSequence_apply _root_.OAI.KadisonKastler.concreteDiagonalUnitary_coe _root_.OAI.KadisonKastler.constantAlgebraUnitaryFamily_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.cyclicOrbitEquiv_val _root_.OAI.KadisonKastler.cyclicOrbitHom_apply _root_.OAI.KadisonKastler.faithfulCyclicEquiv_coe _root_.OAI.KadisonKastler.faithfulCyclicHom_apply _root_.OAI.KadisonKastler.matrixClosureVectorTrace_apply _root_.OAI.KadisonKastler.matrixLiftUnitaryAt_coe _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.minimalCyclicRetraction_compression _root_.OAI.KadisonKastler.normalCyclicEquiv_val _root_.OAI.KadisonKastler.normalCyclicHom_apply _root_.OAI.KadisonKastler.normalPairEquiv_coe _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.regularCoreDualEquiv_apply _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.spatialLeftAlgebraHom_val _root_.OAI.KadisonKastler.spatialTransportEquiv_apply _root_.OAI.KadisonKastler.spatialTransportEquiv_vector _root_.OAI.KadisonKastler.tomitaLinearPolarUnitary_apply _root_.OAI.KadisonKastler.tomitaLinearPolarUnitary_symm_apply _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.typeICyclicHom_apply _root_.OAI.KadisonKastler.typeICyclicOperator_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonKastler.vectorStateCommutator_add _root_.OAI.KadisonKastler.vectorStateCommutator_apply _root_.OAI.KadisonKastler.vectorStateCommutator_one _root_.OAI.KadisonKastler.vectorStateCommutator_smul _root_.OAI.KadisonKastler.vectorStateCommutator_sub _root_.OAI.KadisonKastler.vectorStateCommutator_zero _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply _root_.OAI.KadisonSimilarity.predualRestriction_apply _root_.OAI.KadisonSimilarity.tracialInclusionIsometry_vector _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Strong continuity of the limiting modular group

The cutoff error is bounded by `|t| ε ‖x‖`. At time zero this proves
continuity on the dense cutoff range using just one bounded approximation.
Contraction bounds and the group law give continuity on the whole space.
-/

namespace KadisonKastler

open Filter TopologicalSpace
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [SeparableSpace H] {M : VonNeumannAlgebra H}

theorem modularApproximation_limit_cutoff_bound (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) (n : ℕ) (t : ℝ) (x : H) :
    ‖modularApproximation M J Ω n t (graphResolventCutoff M J Ω x) -
      modularStrongLimit J Ω hsep hcyc t (graphResolventCutoff M J Ω x)‖ ≤
        |t| * modularRegularizationScale n * ‖x‖ := by
  have hc : Tendsto (fun _ : ℕ => modularApproximation M J Ω n t
      (graphResolventCutoff M J Ω x)) atTop
      (𝓝 (modularApproximation M J Ω n t (graphResolventCutoff M J Ω x))) := tendsto_const_nhds
  have hl := (hc.sub
    (modularApproximation_tendsto J Ω hsep hcyc t (graphResolventCutoff M J Ω x))).norm
  have hr : Tendsto (fun m => |t| * |modularRegularizationScale n -
      modularRegularizationScale m| * ‖x‖) atTop
      (𝓝 (|t| * modularRegularizationScale n * ‖x‖)) := by
    have hc : Tendsto (fun _ : ℕ => modularRegularizationScale n) atTop
        (𝓝 (modularRegularizationScale n)) := tendsto_const_nhds
    simpa only [sub_zero, abs_of_pos (modularRegularizationScale_pos n)] using
      ((hc.sub modularRegularizationScale_tendsto).abs.const_mul |t|).mul_const ‖x‖
  exact le_of_tendsto_of_tendsto hl hr (Eventually.of_forall fun m =>
    regularizedModularGroup_cutoff_apply_bound J Ω t (modularRegularizationScale_pos n)
      (modularRegularizationScale_pos m) x)

theorem modularStrongLimit_cutoff_tendsto_zero (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) (x : H) :
    Tendsto (fun t : ℝ => modularStrongLimit J Ω hsep hcyc t
      (graphResolventCutoff M J Ω x)) (𝓝 0) (𝓝 (graphResolventCutoff M J Ω x)) := by
  let y := graphResolventCutoff M J Ω x
  have happ : Tendsto (fun t : ℝ => modularApproximation M J Ω 0 t y) (𝓝 0) (𝓝 y) := by
    have ht := (regularizedModularGroup_stronglyContinuous M J Ω
      (modularRegularizationScale 0) y).tendsto 0
    have he : regularizedModularGroup M J Ω (modularRegularizationScale 0)
        (Multiplicative.ofAdd 0) = 1 := map_one _
    rw [he] at ht
    exact ht
  have herr : Tendsto (fun t : ℝ => |t| * modularRegularizationScale 0 * ‖x‖)
      (𝓝 0) (𝓝 0) := by
    simpa using (((continuous_id : Continuous (fun t : ℝ => t)).abs.tendsto 0).mul_const
      (modularRegularizationScale 0)).mul_const ‖x‖
  have hz : Tendsto (fun t : ℝ => modularStrongLimit J Ω hsep hcyc t y - y)
      (𝓝 0) (𝓝 0) := by
    apply squeeze_zero_norm (fun t => ?_) (by
      simpa only [zero_add, sub_self, norm_zero] using herr.add (happ.sub_const y).norm)
    calc
      _ ≤ ‖modularStrongLimit J Ω hsep hcyc t y - modularApproximation M J Ω 0 t y‖ +
          ‖modularApproximation M J Ω 0 t y - y‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ |t| * modularRegularizationScale 0 * ‖x‖ +
          ‖modularApproximation M J Ω 0 t y - y‖ := by
        rw [norm_sub_rev (modularStrongLimit J Ω hsep hcyc t y)]
        exact add_le_add (modularApproximation_limit_cutoff_bound J Ω hsep hcyc 0 t x) le_rfl
  simpa only [sub_add_cancel, zero_add] using hz.add_const y

theorem modularStrongLimit_tendsto_zero (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) (x : H) :
    Tendsto (fun t : ℝ => modularStrongLimit J Ω hsep hcyc t x) (𝓝 0) (𝓝 x) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨y, hy⟩ := (graphResolventCutoff_dense J Ω hsep hcyc).exists_dist_lt x
    (by positivity : 0 < ε / 4)
  filter_upwards [(Metric.tendsto_nhds.mp
    (modularStrongLimit_cutoff_tendsto_zero J Ω hsep hcyc y)) (ε / 2) (by positivity)] with t ht
  have hc : dist (modularStrongLimit J Ω hsep hcyc t x)
      (modularStrongLimit J Ω hsep hcyc t (graphResolventCutoff M J Ω y)) ≤
      dist x (graphResolventCutoff M J Ω y) := by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    rw [modularStrongLimit_norm_map]
  have hb := (dist_triangle (modularStrongLimit J Ω hsep hcyc t x)
    (modularStrongLimit J Ω hsep hcyc t (graphResolventCutoff M J Ω y)) x).trans
      (add_le_add le_rfl (dist_triangle
        (modularStrongLimit J Ω hsep hcyc t (graphResolventCutoff M J Ω y))
          (graphResolventCutoff M J Ω y) x))
  rw [dist_comm (graphResolventCutoff M J Ω y) x] at hb
  linarith

theorem modularStrongLimit_continuous (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) (x : H) :
    Continuous (fun t : ℝ => modularStrongLimit J Ω hsep hcyc t x) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hsub : Tendsto (fun s : ℝ => s - t) (𝓝 t) (𝓝 0) := by
    have hc : Continuous (fun s : ℝ => s - t) := by fun_prop
    simpa only [sub_self] using hc.tendsto t
  have hz := (modularStrongLimit_tendsto_zero J Ω hsep hcyc x).comp hsub
  have ht := (modularStrongLimit J Ω hsep hcyc t).continuous.continuousAt.tendsto.comp hz
  change Tendsto (fun s : ℝ => modularStrongLimit J Ω hsep hcyc s x)
    (𝓝 t) (𝓝 (modularStrongLimit J Ω hsep hcyc t x))
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  funext s
  change modularStrongLimit J Ω hsep hcyc s x =
    (modularStrongLimit J Ω hsep hcyc t * modularStrongLimit J Ω hsep hcyc (s - t)) x
  rw [← modularStrongLimit_add, show t + (s - t) = s by ring]

theorem modularStrongGroup_continuous (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) (x : H) :
    Continuous (fun t : ℝ =>
      (modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H) x) :=
  modularStrongLimit_continuous J Ω hsep hcyc x

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularRootCommutation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The modular group commutes with the graph square root -/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem modularApproximation_commute_resolvent (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (n : ℕ) (t : ℝ) :
    Commute (modularApproximation M J Ω n t) (graphResolvent M J Ω 1) := by
  change Commute (regularizedModularGroup M J Ω (modularRegularizationScale n)
    (Multiplicative.ofAdd t) : H →L[ℂ] H) _
  rw [regularizedModularGroup_eq_cfc J Ω t (modularRegularizationScale_pos n)]
  exact (graphResolvent_positive J Ω 1).isSelfAdjoint.commute_cfc
    (Commute.refl _) (modularPhaseScalar t (modularRegularizationScale n))

variable [TopologicalSpace.SeparableSpace H]

theorem modularStrongGroup_commute_resolvent (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) (t : ℝ) :
    Commute (modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H)
      (graphResolvent M J Ω 1) := by
  apply ContinuousLinearMap.ext
  intro x
  change modularStrongLimit J Ω hsep hcyc t (graphResolvent M J Ω 1 x) =
    graphResolvent M J Ω 1 (modularStrongLimit J Ω hsep hcyc t x)
  have hu := modularApproximation_tendsto J Ω hsep hcyc t (graphResolvent M J Ω 1 x)
  have hv := (graphResolvent M J Ω 1).continuous.continuousAt.tendsto.comp
    (modularApproximation_tendsto J Ω hsep hcyc t x)
  apply tendsto_nhds_unique hu
  convert hv using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  exact congrArg (fun T : H →L[ℂ] H => T x)
    (modularApproximation_commute_resolvent J Ω n t).eq

theorem modularStrongGroup_commute_root (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) (t : ℝ) :
    Commute (modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H)
      (tomitaGraphRoot (M := M) J Ω) := by
  rw [tomitaGraphRoot, CFC.sqrt_eq_cfc]
  exact ((modularStrongGroup_commute_resolvent J Ω hsep hcyc t).symm.cfc_nnreal NNReal.sqrt).symm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TomitaCoreCoordinates
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Bounded graph coordinates for algebraic Tomita vectors

Every algebra vector is the image of a concrete vector under the square
root of the graph resolvent. Its adjoint vector uses the polar conjugate
of the same coordinate. These are the two boundary data for the KMS strip.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

def tomitaCoreCoordinate (a : Algebra M) : H :=
  (tomitaPolarCoordinates J Ω hsep hcyc).symm
    ⟨rescaledGraphVector J Ω 1 a.val, rescaledGraphVector_mem M J Ω 1 a⟩

theorem tomitaCoreCoordinate_graph (a : Algebra M) :
    (tomitaPolarCoordinates J Ω hsep hcyc (tomitaCoreCoordinate J Ω hsep hcyc a)).val =
      rescaledGraphVector J Ω 1 a.val := by
  exact congrArg (fun v : rescaledGraphSubspace M J Ω 1 => v.val)
    ((tomitaPolarCoordinates J Ω hsep hcyc).apply_symm_apply _)

theorem tomitaCoreCoordinate_first (a : Algebra M) :
    tomitaGraphRoot (M := M) J Ω (tomitaCoreCoordinate J Ω hsep hcyc a) = a.val Ω := by
  have h := congrArg (fun v : TomitaGraphHilbert H => v 0)
    (tomitaCoreCoordinate_graph J Ω hsep hcyc a)
  rw [tomitaPolarCoordinates_first] at h
  exact h

theorem tomitaCoreCoordinate_adjoint (a : Algebra M) :
    tomitaGraphRoot (M := M) J Ω
      (tomitaPolarConjugation J Ω hsep hcyc (tomitaCoreCoordinate J Ω hsep hcyc a)) =
        star a.val Ω := by
  have h := congrArg (fun v : TomitaGraphHilbert H => v 1)
    (tomitaCoreCoordinate_graph J Ω hsep hcyc a)
  rw [tomitaPolarCoordinates_second] at h
  apply J.injective
  simpa only [rescaledGraphVector_one, one_smul] using h

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TomitaComplementaryRoot
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.normUltraproductNontrivial _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The complementary graph square root

Polar conjugation interchanges both bounded positive square roots. This
expresses the full Tomita graph using its two positive coordinates.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {M : VonNeumannAlgebra H} (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

def tomitaGraphComplementRoot : H →L[ℂ] H :=
  CFC.sqrt (1 - graphResolvent M J Ω 1)

theorem tomitaGraphRoot_conjugation :
    conjugationOperator (tomitaPolarConjugation J Ω hsep hcyc)
      (tomitaGraphRoot (M := M) J Ω) = tomitaGraphComplementRoot (M := M) J Ω := by
  apply Eq.symm
  apply CFC.sqrt_unique
  · rw [← conjugationOperator_mul _ (tomitaPolarConjugation_involutive J Ω hsep hcyc),
      tomitaGraphRoot_square, tomitaPolarConjugation_resolvent]
  · exact conjugationOperator_nonneg _ (tomitaPolarConjugation_involutive J Ω hsep hcyc)
      (CFC.sqrt_nonneg _)

theorem tomitaGraphComplementRoot_nonneg : 0 ≤ tomitaGraphComplementRoot (M := M) J Ω :=
  CFC.sqrt_nonneg _

include hsep hcyc in
theorem tomitaGraphComplementRoot_square :
    tomitaGraphComplementRoot (M := M) J Ω * tomitaGraphComplementRoot (M := M) J Ω =
      1 - graphResolvent M J Ω 1 := by
  rw [← tomitaGraphRoot_conjugation J Ω hsep hcyc,
    ← conjugationOperator_mul _ (tomitaPolarConjugation_involutive J Ω hsep hcyc),
    tomitaGraphRoot_square, tomitaPolarConjugation_resolvent]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TomitaLinearPolarCoordinates
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Linear polar coordinates for the closed Tomita graph -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

/-- Both positive coordinates are functions of the same positive contraction. -/
theorem tomitaGraphRoots_commute :
    Commute (tomitaGraphRoot (M := M) J Ω) (tomitaGraphComplementRoot (M := M) J Ω) := by
  have h : Commute (graphResolvent M J Ω 1) (1 - graphResolvent M J Ω 1) :=
    (Commute.one_right _).sub_right (Commute.refl _)
  rw [tomitaGraphRoot, tomitaGraphComplementRoot, CFC.sqrt_eq_cfc, CFC.sqrt_eq_cfc]
  exact ((h.cfc_nnreal NNReal.sqrt).symm.cfc_nnreal NNReal.sqrt).symm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TomitaMiddleCore
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The bounded middle operator on the algebra and commutant cores

The product of the complementary graph roots replaces the unbounded modular
square root in the operator identities used below.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

def tomitaMiddleOperator : H →L[ℂ] H :=
  tomitaGraphRoot (M := M) J Ω * tomitaGraphComplementRoot (M := M) J Ω

theorem tomitaMiddleOperator_selfAdjoint :
    IsSelfAdjoint (tomitaMiddleOperator (M := M) J Ω) := by
  unfold tomitaMiddleOperator
  rw [IsSelfAdjoint, star_mul, (tomitaGraphRoot_selfAdjoint J Ω).star_eq,
    (tomitaGraphComplementRoot_nonneg J Ω).isSelfAdjoint.star_eq]
  exact (tomitaGraphRoots_commute J Ω).eq.symm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularOrbit
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.CommonTracialPositionData.rightEquiv_transportEquiv _root_.OAI.KadisonKastler.FiniteInnerAverage.algebraApply_sub _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.StandardTracialPosition.diagonalRepresentation_vector _root_.OAI.KadisonKastler.algebraConstantField_coe _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.concreteDerivation_apply _root_.OAI.KadisonKastler.concreteDiagonalSequenceUnitary_coe _root_.OAI.KadisonKastler.concreteDiagonalSequence_apply _root_.OAI.KadisonKastler.concreteDiagonalUnitary_coe _root_.OAI.KadisonKastler.constantAlgebraUnitaryFamily_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.cyclicOrbitEquiv_val _root_.OAI.KadisonKastler.cyclicOrbitHom_apply _root_.OAI.KadisonKastler.faithfulCyclicEquiv_coe _root_.OAI.KadisonKastler.faithfulCyclicHom_apply _root_.OAI.KadisonKastler.matrixClosureVectorTrace_apply _root_.OAI.KadisonKastler.matrixLiftUnitaryAt_coe _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.minimalCyclicRetraction_compression _root_.OAI.KadisonKastler.normalCyclicEquiv_val _root_.OAI.KadisonKastler.normalCyclicHom_apply _root_.OAI.KadisonKastler.normalPairEquiv_coe _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.regularCoreDualEquiv_apply _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.spatialLeftAlgebraHom_val _root_.OAI.KadisonKastler.spatialTransportEquiv_apply _root_.OAI.KadisonKastler.spatialTransportEquiv_vector _root_.OAI.KadisonKastler.tomitaLinearPolarUnitary_apply _root_.OAI.KadisonKastler.tomitaLinearPolarUnitary_symm_apply _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.typeICyclicHom_apply _root_.OAI.KadisonKastler.typeICyclicOperator_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonKastler.vectorStateCommutator_add _root_.OAI.KadisonKastler.vectorStateCommutator_apply _root_.OAI.KadisonKastler.vectorStateCommutator_one _root_.OAI.KadisonKastler.vectorStateCommutator_smul _root_.OAI.KadisonKastler.vectorStateCommutator_sub _root_.OAI.KadisonKastler.vectorStateCommutator_zero _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply _root_.OAI.KadisonSimilarity.predualRestriction_apply _root_.OAI.KadisonSimilarity.tracialInclusionIsometry_vector _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Strongly continuous bounded modular orbits and their scalar averages -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}
  (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

def modularOrbit (Y : H →L[ℂ] H) (t : ℝ) : H →L[ℂ] H :=
  (modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd (-t)) : H →L[ℂ] H) * Y *
    (modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H)

theorem modularOrbit_continuous (Y : H →L[ℂ] H) (x : H) :
    Continuous (fun t => modularOrbit J Ω hsep hcyc Y t x) := by
  exact continuous_unitary_field_apply
    (fun t : ℝ => modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd (-t)))
    (fun v => (modularStrongGroup_continuous J Ω hsep hcyc v).comp continuous_neg)
    (fun t => Y ((modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
    (Y.continuous.comp (modularStrongGroup_continuous J Ω hsep hcyc x))

theorem modularOrbit_norm_le (Y : H →L[ℂ] H) (t : ℝ) :
    ‖modularOrbit J Ω hsep hcyc Y t‖ ≤ ‖Y‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg Y)
  intro x
  change ‖(modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd (-t)) : H →L[ℂ] H)
    (Y ((modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H) x))‖ ≤ _
  rw [Unitary.norm_map]
  simpa only [Unitary.norm_map] using Y.le_opNorm
    ((modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H) x)

def modularOrbitAverage (Y : H →L[ℂ] H) (φ : ℝ) (hφ : |φ| < Real.pi) : H →L[ℂ] H :=
  weightedOperatorIntegral volume (stripAverageKernel Real.pi (φ : ℂ))
    (stripAverageKernel_integrable (by simpa using hφ)) (modularOrbit J Ω hsep hcyc Y)
    (fun x => (modularOrbit_continuous J Ω hsep hcyc Y x).aestronglyMeasurable) ‖Y‖
    (Filter.Eventually.of_forall (modularOrbit_norm_le J Ω hsep hcyc Y))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_WeightedStripOperator
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The bounded holomorphic modular strip on the original space -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

def weightedStripOperator (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (z : ℂ) : H →L[ℂ] H :=
  resolventContinuousCalculus (graphResolvent M J Ω 1)
    (graphResolvent_positive J Ω 1).isSelfAdjoint
    (weightedStripContinuous (resolventRealCoordinate (graphResolvent M J Ω 1)) z)

theorem weightedStripOperator_differentiableOn (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) :
    DifferentiableOn ℂ (weightedStripOperator (M := M) J Ω) {z : ℂ | |z.re| < 1} :=
  (resolventContinuousCalculusLinear (graphResolvent M J Ω 1)
    (graphResolvent_positive J Ω 1).isSelfAdjoint).differentiable.comp_differentiableOn
      (weightedStripContinuous_differentiableOn _)

theorem weightedStripOperator_norm_le (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    {z : ℂ} (hz : |z.re| ≤ 1 / 2) : ‖weightedStripOperator (M := M) J Ω z‖ ≤ 1 := by
  apply (NonUnitalStarAlgHom.norm_apply_le _ _).trans
  exact weightedStripContinuous_norm_le _
    (fun s => graphResolvent_spectrum_bounds J Ω s.property) hz

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_WeightedStripAverage
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Applying the scalar strip formula to bounded operators

Extra resolvent powers make the spectral strip norm continuous up to both
edges. Consequently the scalar contour theorem applies to every ambient
operator, with no algebra normalization premise.
-/

namespace KadisonKastler

open Set MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

def weightedStripCoefficient (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (X : H →L[ℂ] H)
    (ξ η : H) (z : ℂ) : ℂ :=
  inner ℂ ξ ((weightedStripOperator (M := M) J Ω (-z) * X *
    weightedStripOperator (M := M) J Ω z) η)

theorem weightedStripCoefficient_differentiableOn (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (X : H →L[ℂ] H) (ξ η : H) :
    DifferentiableOn ℂ (weightedStripCoefficient (M := M) J Ω X ξ η)
      {z : ℂ | |z.re| < 1} := by
  intro z hz
  have hB := weightedStripOperator_differentiableOn (M := M) J Ω
  have hopen : IsOpen {z : ℂ | |z.re| < 1} :=
    isOpen_lt Complex.continuous_re.abs continuous_const
  have hpos := hB.differentiableAt (hopen.mem_nhds hz)
  have hneg := (hB.differentiableAt (hopen.mem_nhds (by simpa using hz))).comp z
    (differentiableAt_id.neg)
  have hm := (hneg.mul_const X).mul hpos
  exact ((innerSL ℂ ξ).differentiableAt.comp z
    (hm.clm_apply (differentiableAt_const η))).differentiableWithinAt

theorem weightedStripCoefficient_bound (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (X : H →L[ℂ] H) (ξ η : H) {z : ℂ} (hz : |z.re| ≤ 1 / 2) :
    ‖weightedStripCoefficient (M := M) J Ω X ξ η z‖ ≤ ‖ξ‖ * ‖X‖ * ‖η‖ := by
  have hp (w : ℂ) (hw : |w.re| ≤ 1 / 2) (v : H) :
      ‖weightedStripOperator (M := M) J Ω w v‖ ≤ ‖v‖ := by
    calc
      _ ≤ ‖weightedStripOperator (M := M) J Ω w‖ * ‖v‖ :=
        (weightedStripOperator (M := M) J Ω w).le_opNorm v
      _ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right
        (weightedStripOperator_norm_le J Ω hw) (norm_nonneg v)
      _ = ‖v‖ := one_mul _
  apply (norm_inner_le_norm _ _).trans
  change ‖ξ‖ * ‖weightedStripOperator (M := M) J Ω (-z)
    (X (weightedStripOperator (M := M) J Ω z η))‖ ≤ _
  calc
    _ ≤ ‖ξ‖ * ‖X (weightedStripOperator (M := M) J Ω z η)‖ :=
      mul_le_mul_of_nonneg_left (hp (-z) (by simpa using hz) _) (norm_nonneg _)
    _ ≤ ‖ξ‖ * (‖X‖ * ‖weightedStripOperator (M := M) J Ω z η‖) :=
      mul_le_mul_of_nonneg_left (X.le_opNorm _) (norm_nonneg _)
    _ ≤ ‖ξ‖ * (‖X‖ * ‖η‖) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hp z hz η) (norm_nonneg _))
        (norm_nonneg _)
    _ = _ := by ring

theorem weightedStripCoefficient_average (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (X : H →L[ℂ] H) (ξ η : H) (φ : ℝ) (hφ : |φ| < Real.pi) :
    (∫ t : ℝ, stripAverageKernel Real.pi (φ : ℂ) t *
      (Complex.exp (Complex.I * φ / 2) *
          weightedStripCoefficient (M := M) J Ω X ξ η ((1 / 2 : ℂ) + t * Complex.I) +
        Complex.exp (-(Complex.I * φ / 2)) *
          weightedStripCoefficient (M := M) J Ω X ξ η ((-1 / 2 : ℂ) + t * Complex.I))) =
      weightedStripCoefficient (M := M) J Ω X ξ η 0 := by
  have hd := weightedStripCoefficient_differentiableOn (M := M) J Ω X ξ η
  have hc := hd.continuousOn.mono (show {z : ℂ | |z.re| ≤ 1 / 2} ⊆
    {z : ℂ | |z.re| < 1} from fun z hz => (show |z.re| < 1 from lt_of_le_of_lt hz (by norm_num)))
  exact centered_strip_average φ hφ _ hc
    (hd.mono (fun z hz => (show |z.re| < 1 from lt_trans hz (by norm_num))))
    (‖ξ‖ * ‖X‖ * ‖η‖) (by positivity)
    (fun z hz => weightedStripCoefficient_bound J Ω X ξ η hz)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularCyclicPhase
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The modular group in the cyclic spectral model

The two injective graph coordinates exclude the endpoints. Dominated
convergence then identifies the strong-limit group with the logarithmic
phase multiplier on every scalar cyclic spectral space.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem graphResolventVectorMeasure_interior (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) (x : H) :
    ∀ᵐ s ∂resolventVectorMeasure (graphResolvent M J Ω 1)
      (graphResolvent_positive J Ω 1).isSelfAdjoint x, 0 < s.val ∧ s.val < 1 := by
  have h0 := measure_eq_zero_iff_ae_notMem.mp
    (resolventVectorMeasure_zero_endpoint (graphResolvent M J Ω 1)
      (graphResolvent_positive J Ω 1).isSelfAdjoint (graphResolvent_injective J Ω hsep hcyc) x)
  have h1 := measure_eq_zero_iff_ae_notMem.mp
    (resolventVectorMeasure_one_endpoint (graphResolvent M J Ω 1)
      (graphResolvent_positive J Ω 1).isSelfAdjoint (one_sub_graphResolvent_injective J Ω hsep) x)
  filter_upwards [h0, h1] with s h0 h1
  have hb := graphResolvent_spectrum_bounds J Ω s.property
  change s.val ≠ 0 at h0
  change s.val ≠ 1 at h1
  exact ⟨lt_of_le_of_ne hb.1 h0.symm, lt_of_le_of_ne hb.2 h1⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularCyclicGroup
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The scalar cyclic modular group

The phase multipliers form a strongly continuous unitary group. The
cyclic isometry intertwines this group with the constructed original
group, so its laws require no additional modular-theory input.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

def modularCyclicPhaseOperator (M : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H) (Ω x : H)
    (t : ℝ) : ModularCyclicSpace M J Ω x →L[ℂ] ModularCyclicSpace M J Ω x :=
  resolventScalarMultiplier _ _ x (fun s => modularSpectralPhase t s.val)
    ((modularSpectralPhase_measurable t).comp measurable_subtype_coe) 1
    (fun s => (modularSpectralPhase_norm t s.val).le)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_WeightedStripFactorization
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Factoring the weighted strip boundaries through the middle operator -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}
  (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

theorem modularStrongGroup_commute_complement_root (t : ℝ) :
    Commute (modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H)
      (tomitaGraphComplementRoot (M := M) J Ω) := by
  rw [tomitaGraphComplementRoot, CFC.sqrt_eq_cfc]
  exact (((Commute.one_right _).sub_right
    (modularStrongGroup_commute_resolvent J Ω hsep hcyc t)).symm.cfc_nnreal NNReal.sqrt).symm

theorem modularStrongGroup_commute_middle (t : ℝ) :
    Commute (modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H)
      (tomitaMiddleOperator (M := M) J Ω) :=
  (modularStrongGroup_commute_root J Ω hsep hcyc t).mul_right
    (modularStrongGroup_commute_complement_root J Ω hsep hcyc t)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CanonicalPositiveCone
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Positivity of the cone for the constructed modular conjugation

The positive core pairing and the constructed commutant theorem make the
generated cone acute. In particular its intersection with its negative is
zero. Self-duality and representation of all normal states are not asserted.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}
  (J : H ≃ₗᵢ⋆[ℂ] H) (ξ : H)
  (hsep : Function.Injective (algebraVectorMap M ξ))
  (hcyc : DenseRange (algebraVectorMap M ξ))

def canonicalModularPositiveCone : ConvexCone ℝ H :=
  modularPositiveCone (M := M) (tomitaPolarConjugation J ξ hsep hcyc) ξ

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CyclicGaugeKernel
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}
  (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω)) (x : H)

theorem characterField_tensor_rows {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (l : X → ℝ) (hl : Measurable l)
    (f : Lp ℂ 2 (volume : Measure ℝ)) (v : Lp ℂ 2 μ) :
    ∀ᵐ s ∂μ, ∀ᵐ t ∂(volume : Measure ℝ),
      ((characterField μ l hl : Lp (RegularCoreHilbert ℂ) 2 μ →L[ℂ]
        Lp (RegularCoreHilbert ℂ) 2 μ) (scalarLpTensor μ v f)) s t =
      regularCharacterScalar (l s) t * f t * v s := by
  filter_upwards [characterField_apply_ae μ l hl (scalarLpTensor μ v f),
    scalarLpTensor_apply_ae μ v f] with s ht hv
  have he := ht.trans (congrArg
    (regularCharacterUnitary (H := ℂ) (l s) : RegularCoreHilbert ℂ →L[ℂ] RegularCoreHilbert ℂ) hv)
  filter_upwards [regularCharacterUnitary_apply_ae (l s) (v s • f), Lp.coeFn_smul (v s) f]
    with t ht hf
  calc
    _ = ((regularCharacterUnitary (H := ℂ) (l s) : RegularCoreHilbert ℂ →L[ℂ]
        RegularCoreHilbert ℂ) (v s • f)) t :=
      congrArg (fun w : RegularCoreHilbert ℂ => w t) he
    _ = regularCharacterScalar (l s) t • (v s • f) t := ht
    _ = _ := by rw [hf]; change _ * (v s * f t) = _; ring

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_NormalRepresentationRange
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Ranges of faithful representations continuous on bounded weak nets

Kaplansky approximation and compactness of the source operator ball show
that the range is already a von Neumann algebra. The same approximation
transports a specified generating algebra into a target von Neumann algebra.
-/

namespace KadisonKastler

open UnitalTomsWinter Generator Generator.Tracial Filter
open scoped Topology

noncomputable section

universe u

variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem boundedWeakNormal_maps_generated
    (M : VonNeumannAlgebra H) (φ : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (hφ : BoundedWeakNormal M φ) (B : StarSubalgebra ℂ (H →L[ℂ] H))
    (hBM : B ≤ M.toStarSubalgebra) (hMB : M ≤ generatedVonNeumannAlgebra B)
    (N : VonNeumannAlgebra K)
    (hBN : ∀ a : B, φ ⟨a.val, hBM a.property⟩ ∈ N) :
    ∀ a : Algebra M, φ a ∈ N := by
  classical
  have hball (a : Algebra M) (ha : ‖a‖ ≤ 1) : φ a ∈ N := by
    have hb : a.val ∈ Set.centralizer (Set.centralizer (B : Set (H →L[ℂ] H))) := by
      have h := hMB a.property
      change a.val ∈ (generatedVonNeumannAlgebra B : Set (H →L[ℂ] H)) at h
      rwa [generatedVonNeumannAlgebra_coe] at h
    obtain ⟨c, hc, hlim⟩ := publishedKaplanskyDensity.exists_weak_contraction_net B a.val hb ha
    let d : Finset H × ℕ → Algebra M := fun i => ⟨(c i).val, hBM (c i).property⟩
    let e : Finset H × ℕ → Algebra N := fun i => ⟨φ (d i), hBN (c i)⟩
    exact weak_operator_limit_mem N e (φ a)
      (hφ d a 1 (Eventually.of_forall hc) hlim)
  intro a
  by_cases hz : a = 0
  · rw [hz, map_zero]; exact N.zero_mem
  have hn : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  let c : ℂ := (‖a‖ : ℂ)⁻¹
  have hc : c ≠ 0 := inv_ne_zero (by exact_mod_cast hn)
  have hsmall : ‖c • a‖ ≤ 1 := by
    simp only [c, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg a), inv_mul_cancel₀ hn, le_refl]
  have hb := hball (c • a) hsmall
  rw [show φ (c • a) = c • φ a from φ.toAlgHom.toLinearMap.map_smul _ _] at hb
  exact (N.toStarSubalgebra.toSubalgebra.toSubmodule.smul_mem_iff hc).mp hb

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PublishedModularSpectral
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The published modular spectral resolution, in bounded coordinates

Blackadar, *Operator Algebras* (2006), III.4.3.2 and III.4.4.7--9
and III.4.6.1--2 (printed pp.313, 316--317, 320), gives the modular group, centralizer characterization and the polar
decomposition of the closed Tomita operator. III.4.7.1--2 (pp.325--326)
identifies its action by the KMS strip condition. I.7.4.5--7 and I.7.4.10
(pp.34--37) give its logarithmic spectral resolution and functional calculus.

We retain only the upper cuts of `log Δ`, their Fourier gauge identity,
and the bounded functional-calculus identities at distance `1/2` from a
cut. The first entry of the graph projection is `(1 + c² Δ)⁻¹`.
The identification of the second graph coordinate may be any antiunitary.
There is no comparison between two algebras in this published input.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Tomita--Takesaki and the spectral theorem at a cyclic separating vector,
restricted to the bounded data above. -/
def PublishedModularSpectralResolution : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H],
    ∀ (M : VonNeumannAlgebra H) (Ω : H),
      DenseRange (algebraVectorMap M Ω) → Function.Injective (algebraVectorMap M Ω) →
      Nonempty (ModularConjugationData M Ω × ModularSpectralResolution M Ω)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ReducingCommutantCorner
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The commutant on a reducing subspace is the represented corner -/

namespace KadisonKastler

noncomputable section

open Generator Generator.Tracial

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (E : Submodule ℂ H) [CompleteSpace E]

/-- Full central support of the reducing projection makes restriction faithful. -/
theorem commutantReducingHom_injective (M : VonNeumannAlgebra H)
    (hE : E.starProjection ∈ M.commutant) (hE0 : E.starProjection ≠ 0)
    (hN : ScalarCenter M.commutant) :
    Function.Injective (commutantReducingHom E M hE) := by
  intro a b hab
  let x : Algebra M := a - b
  have hx : commutantReducingHom E M hE x = 0 := by
    rw [map_sub, hab, sub_self]
  have hxc : cornerCompression E x.val = 0 := hx
  have he := congrArg (cornerExtension E) hxc
  rw [cornerExtension_compression, map_zero] at he
  have hp := isStarProjection_starProjection (U := E)
  have hc : E.starProjection * x.val = x.val * E.starProjection :=
    (VonNeumannAlgebra.mem_commutant_iff.mp hE x.val x.property).symm
  have hxp : x.val * E.starProjection = 0 := by
    rw [hc, mul_assoc, hp.isIdempotentElem.eq] at he
    exact he
  let p : AlgebraProjection M.commutant :=
    ⟨⟨E.starProjection, hE⟩,
      ⟨Subtype.ext hp.isIdempotentElem.eq, Subtype.ext hp.isSelfAdjoint.star_eq⟩⟩
  have hp0 : p.val ≠ 0 := fun h => hE0 (congrArg Subtype.val h)
  have hxN : x.val ∈ M.commutant.commutant := by
    rw [VonNeumannAlgebra.commutant_commutant]
    change x.val ∈ M.toSubalgebra
    exact x.property
  have hz := commutant_eq_zero_of_mul_factor_projection M.commutant hN p hp0
    x.val hxN hxp
  exact sub_eq_zero.mp (Subtype.ext hz)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PointedMatrixSum
attribute [-instance] _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.spatialHilbert_separable _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
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

theorem sumSite_generates (S : PointedMatrixSites M Ω ν)
    (T : PointedMatrixSites N ξ η) :
    spatialProductAlgebra M N = generatedVonNeumannAlgebra (⨆ i, (S.sumSite T i).algebra) := by
  let Q := generatedVonNeumannAlgebra (⨆ i, (S.sumSite T i).algebra)
  have hentry (i : I ⊕ J) (a b : Fin 2) : (S.sumSite T i).entry a b ∈ Q :=
    subset_generatedVonNeumannAlgebra _
      ((le_iSup (fun i => (S.sumSite T i).algebra) i) ((S.sumSite T i).entry_mem a b))
  have hleft : ∀ x ∈ M, spatialLeft (K := K) x ∈ Q := by
    intro x hx
    rw [S.generates] at hx
    apply spatialLeft_mem_of_generated publishedKaplanskyDensity _ Q _ hx
    have hle : (⨆ i, (S.site i).algebra) ≤ Q.toStarSubalgebra.comap (spatialLeft (K := K)) := by
      apply iSup_le
      intro i
      apply ((S.site i).algebra_le_iff _).mpr
      intro a b
      exact hentry (.inl i) a b
    exact fun _ h => hle h
  have hright : ∀ x ∈ N, spatialRight (H := H) x ∈ Q := by
    intro x hx
    rw [T.generates] at hx
    apply spatialRight_mem_of_generated publishedKaplanskyDensity _ Q _ hx
    have hle : (⨆ i, (T.site i).algebra) ≤ Q.toStarSubalgebra.comap (spatialRight (H := H)) := by
      apply iSup_le
      intro i
      apply ((T.site i).algebra_le_iff _).mpr
      intro a b
      exact hentry (.inr i) a b
    exact fun _ h => hle h
  apply le_antisymm
  · apply generatedVonNeumannAlgebra_le_of_le
    apply sup_le
    · rintro x ⟨a, ha, rfl⟩
      exact hleft a ha
    · rintro x ⟨a, ha, rfl⟩
      exact hright a ha
  · apply generatedVonNeumannAlgebra_le_of_le
    apply iSup_le
    intro i
    apply ((S.sumSite T i).algebra_le_iff _).mpr
    intro a b
    cases i with
    | inl i => exact spatialLeft_mem_product M N (S.site_mem i a b)
    | inr j => exact spatialRight_mem_product M N (T.site_mem j a b)

/-- Tensoring two pointed systems constructs their sum-indexed system. -/
def sum (S : PointedMatrixSites M Ω ν) (T : PointedMatrixSites N ξ η) :
    PointedMatrixSites (spatialProductAlgebra M N) (tensorVector ξ Ω) (Sum.elim ν η) where
  valid i := by cases i with | inl i => exact S.valid i | inr j => exact T.valid j
  site := S.sumSite T
  commuting i j hij a b c d := by
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        change spatialLeft (K := K) ((S.site i).entry a b) * spatialLeft ((S.site j).entry c d) =
          spatialLeft ((S.site j).entry c d) * spatialLeft ((S.site i).entry a b)
        rw [← map_mul, ← map_mul, (S.commuting i j (fun h => hij (congrArg Sum.inl h)) a b c d).eq]
      | inr j =>
        change spatialTensorOp ((S.site i).entry a b) 1 * spatialTensorOp 1 ((T.site j).entry c d) =
          spatialTensorOp 1 ((T.site j).entry c d) * spatialTensorOp ((S.site i).entry a b) 1
        rw [← spatialTensorOp_mul, ← spatialTensorOp_mul]
        simp only [mul_one, one_mul]
    | inr i =>
      cases j with
      | inl j =>
        change spatialTensorOp 1 ((T.site i).entry a b) * spatialTensorOp ((S.site j).entry c d) 1 =
          spatialTensorOp ((S.site j).entry c d) 1 * spatialTensorOp 1 ((T.site i).entry a b)
        rw [← spatialTensorOp_mul, ← spatialTensorOp_mul]
        simp only [mul_one, one_mul]
      | inr j =>
        change spatialRight (H := H) ((T.site i).entry a b) * spatialRight ((T.site j).entry c d) =
          spatialRight ((T.site j).entry c d) * spatialRight ((T.site i).entry a b)
        rw [← map_mul, ← map_mul, (T.commuting i j (fun h => hij (congrArg Sum.inr h)) a b c d).eq]
  generates := S.sumSite_generates T
  unit_vector := by rw [norm_tensorVector_apply, S.unit_vector, T.unit_vector, one_mul]
  cyclic := denseRange_spatialProduct_vector M N Ω ξ S.cyclic T.cyclic
  separating := separating_spatialProduct_vector_of_separating M N Ω ξ S.separating T.separating
  moments := S.sumSite_moments T

end PointedMatrixSites

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PointedPowerProduct
attribute [-instance] _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductNontrivial _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.spatialHilbert_separable _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Concrete Powers product and the pointed-product input

The countable configuration Hilbert space carries the faithful product
of the two-dimensional diagonal state. Its commuting right action gives
a separating vacuum; finite configuration vectors give cyclicity.
-/

namespace KadisonKastler

open UnitalTomsWinter

noncomputable section

universe u

/-- A constant two-dimensional product with its actual matrix-state moments. -/
def constantPointedMatrixProduct {ν : ℝ} (hν : 0 < ν) (hν1 : ν < 1) :
    PointedMatrixProduct.{0} (fun _ : ℕ => ν) := by
  let d : PointedLocalMatrixData ν := Classical.choice (exists_pointedLocalMatrixData hν)
  exact {
    K := PointedPowerHilbert
    algebra := pointedPowerAlgebra d.left
    vector := pointedPowerVacuum
    coordinates := {
      valid := fun _ => ⟨hν,hν1⟩
      site := pointedPowerSite d.left
      commuting := pointedPowerSite_commuting d.left
      generates := rfl
      unit_vector := norm_pointedPowerVacuum
      cyclic := pointedPowerAlgebra_cyclic d.left d.left_spans
      separating := pointedPowerAlgebra_separating d
      moments := pointedPower_moments d } }

/-- The fixed lambda product required by the absorption argument. -/
def fixedPowersProduct : PointedMatrixProduct.{u} (fun _ : ℕ => fixedProductLambda) :=
  (constantPointedMatrixProduct fixedProductLambda_pos fixedProductLambda_lt_one).universeLift

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TwoRatioPointedConstruction
attribute [-instance] _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductNontrivial _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The concrete pointed product for the two fixed ratios

The constant matrix-state products are placed in the
two spatial tensor legs. Their finite moments, cyclicity and separation
give the exact two-family coordinate system used by the application.
Its finite stages include remote copies and finite complements.
-/

namespace KadisonKastler

open UnitalTomsWinter

noncomputable section

universe u

/-- The two prescribed site families with their actual product-state representation. -/
def twoRatioPointedProduct : PointedMatrixProduct.{u} twoRatioSiteParameter := by
  let P := fixedPowersProduct.{u}
  let Q : PointedMatrixProduct.{u} (fun _ : ℕ => fixedProductMu) :=
    (constantPointedMatrixProduct fixedProductMu_pos fixedProductMu_lt_one).universeLift
  exact {
    K := SpatialHilbert P.K Q.K
    algebra := spatialProductAlgebra P.algebra Q.algebra
    vector := tensorVector Q.vector P.vector
    coordinates := P.coordinates.sum Q.coordinates }

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_StateCommutatorAlgebra
attribute [-instance] _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 0

namespace OAI

/-! # Algebraic estimates for state centralizer sequences

The state commutator is linear, respects adjoints in norm, and satisfies
an explicit product estimate. These facts support the passage from
unitary tests to all bounded sequences.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem vectorFunctional_star (ξ : H) (a : Algebra M) :
    vectorFunctional ξ (star a)=star (vectorFunctional ξ a) := by
  change inner ℂ ξ (a.val.adjoint ξ)=star (inner ℂ ξ (a.val ξ))
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact (inner_conj_symm (𝕜 := ℂ) (a.val ξ) ξ).symm

theorem vectorStateCommutator_star_apply (ξ : H) (a b : Algebra M) :
    vectorStateCommutator ξ (star a) b = -star (vectorStateCommutator ξ a (star b)) := by
  rw [vectorStateCommutator_apply,vectorStateCommutator_apply,← vectorFunctional_star]
  simp only [star_sub,star_mul,star_star,map_sub]
  abel

theorem vectorStateCommutator_star_norm (ξ : H) (a : Algebra M) :
    ‖vectorStateCommutator ξ (star a)‖=‖vectorStateCommutator ξ a‖ := by
  have h (a : Algebra M) : ‖vectorStateCommutator ξ (star a)‖ ≤
      ‖vectorStateCommutator ξ a‖ := by
    apply (vectorStateCommutator ξ (star a)).opNorm_le_bound (norm_nonneg _)
    intro b
    rw [vectorStateCommutator_star_apply,norm_neg,norm_star]
    simpa only [norm_star] using (vectorStateCommutator ξ a).le_opNorm (star b)
  exact le_antisymm (h a) (by simpa only [star_star] using h (star a))

theorem vectorStateCommutator_mul_apply (ξ : H) (a b x : Algebra M) :
    vectorStateCommutator ξ (a*b) x =
      vectorStateCommutator ξ a (b*x)+vectorStateCommutator ξ b (x*a) := by
  simp only [vectorStateCommutator_apply,map_sub,mul_assoc]
  ring

theorem vectorStateCommutator_mul_norm_le (ξ : H) (a b : Algebra M) :
    ‖vectorStateCommutator ξ (a*b)‖ ≤
      ‖vectorStateCommutator ξ a‖*‖b‖+‖a‖*‖vectorStateCommutator ξ b‖ := by
  apply (vectorStateCommutator ξ (a*b)).opNorm_le_bound (by positivity)
  intro x
  rw [vectorStateCommutator_mul_apply]
  calc
    _ ≤ ‖vectorStateCommutator ξ a (b*x)‖+‖vectorStateCommutator ξ b (x*a)‖ := norm_add_le _ _
    _ ≤ ‖vectorStateCommutator ξ a‖*‖b*x‖+‖vectorStateCommutator ξ b‖*‖x*a‖ :=
      add_le_add ((vectorStateCommutator ξ a).le_opNorm _) ((vectorStateCommutator ξ b).le_opNorm _)
    _ ≤ ‖vectorStateCommutator ξ a‖*(‖b‖*‖x‖)+‖vectorStateCommutator ξ b‖*(‖x‖*‖a‖) := by
      gcongr <;> exact norm_mul_le _ _
    _ = _ := by ring

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_StateCentralSequenceAlgebra
attribute [-instance] _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 0

namespace OAI

/-! # The C-star algebra of state-central bounded sequences

State commutator estimates provide addition, multiplication, adjoints and
norm closure directly, independently of the vector centrality criterion.
-/

namespace KadisonKastler

open Generator.Tracial Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem StateAsymptoticallyCentral.add {ξ : H} {x y : BoundedSequence (Algebra M)}
    (hx : StateAsymptoticallyCentral ξ x) (hy : StateAsymptoticallyCentral ξ y) :
    StateAsymptoticallyCentral ξ (x+y) := by
  change Tendsto (fun n => ‖vectorStateCommutator ξ (x n+y n)‖) atTop (𝓝 0)
  simp only [vectorStateCommutator_add]
  apply squeeze_zero (fun _ => norm_nonneg _) (fun _ => norm_add_le _ _)
  simpa only [add_zero] using Filter.Tendsto.add hx hy

theorem StateAsymptoticallyCentral.smul {ξ : H} {x : BoundedSequence (Algebra M)}
    (hx : StateAsymptoticallyCentral ξ x) (c : ℂ) : StateAsymptoticallyCentral ξ (c • x) := by
  change Tendsto (fun n => ‖vectorStateCommutator ξ (c • x n)‖) atTop (𝓝 0)
  simp only [vectorStateCommutator_smul,norm_smul]
  simpa only [mul_zero] using hx.const_mul ‖c‖

theorem StateAsymptoticallyCentral.star {ξ : H} {x : BoundedSequence (Algebra M)}
    (hx : StateAsymptoticallyCentral ξ x) : StateAsymptoticallyCentral ξ (star x) := by
  simpa only [StateAsymptoticallyCentral,BoundedContinuousFunction.star_apply,
    vectorStateCommutator_star_norm] using hx

theorem StateAsymptoticallyCentral.mul {ξ : H} {x y : BoundedSequence (Algebra M)}
    (hx : StateAsymptoticallyCentral ξ x) (hy : StateAsymptoticallyCentral ξ y) :
    StateAsymptoticallyCentral ξ (x*y) := by
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun n => (vectorStateCommutator_mul_norm_le ξ (x n) (y n)).trans
      (add_le_add
        (mul_le_mul_of_nonneg_left (y.norm_coe_le_norm n) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (x.norm_coe_le_norm n) (norm_nonneg _))))
  simpa only [zero_mul,mul_zero,add_zero] using (hx.mul_const ‖y‖).add (hy.const_mul ‖x‖)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RemoteProductCopy
attribute [-instance] _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.spatialHilbert_separable _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A state-preserving copy beyond each finite product stage -/

namespace KadisonKastler

open Generator UnitalTomsWinter

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {Ω : H}

namespace PointedMatrixSites

variable (S : PointedMatrixSites M Ω twoRatioSiteParameter)

def remoteDoubleUnitary (n : ℕ) : SpatialHilbert H H ≃ₗᵢ[ℂ] H :=
  (S.sum S).reindexEquivalence S (remoteTwoRatioDoubling n)
    (remoteTwoRatioDoubling_parameter n)

theorem remoteDoubleUnitary_algebra (n : ℕ) :
    spatialTransportAlgebra (S.remoteDoubleUnitary n) (spatialProductAlgebra M M)=M :=
  (S.sum S).reindexEquivalence_algebra S _ _

def remoteCopy (n : ℕ) : Algebra M →⋆ₐ[ℂ] Algebra M :=
  (((S.remoteDoubleUnitary n).conjStarAlgEquiv.toStarAlgHom.comp
    (spatialLeft (K := H))).comp M.toStarSubalgebra.subtype).codRestrict M.toStarSubalgebra
      (by
        intro a
        have hm : (S.remoteDoubleUnitary n).conjStarAlgEquiv (spatialLeft a.val) ∈
            spatialTransportAlgebra (S.remoteDoubleUnitary n) (spatialProductAlgebra M M) := by
          apply (mem_spatialTransportAlgebra _ _ _).mpr
          rw [StarAlgEquiv.symm_apply_apply]
          exact spatialLeft_mem_product M M a.property
        rwa [S.remoteDoubleUnitary_algebra n] at hm)

end PointedMatrixSites

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PositiveReferenceHaagerup
attribute [-instance] _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Haagerup witnesses at positive references

The spatial coisometries scale on every vector. Positivity identifies the
new reference's polar conjugation with the old one, so the constructed
modular-product-state argument applies again at the new reference.
-/

namespace KadisonKastler

open Generator Generator.Tracial UnitalTomsWinter Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

/-- A concrete all-vector coisometry property; the spatial product below
supplies it by the already constructed remote matrix sequences. -/
def UniversalModularCoisometries (M : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H) : Prop :=
  ∀ t : ℝ, 0 < t → t < 1 → ∃ w : ℕ → Algebra M,
    (∀ n, w n*star (w n)=1) ∧
    (∀ η : H, Tendsto (fun n => (w n).val η-
      (t : ℂ) • conjugationOperator J (star (w n).val) η) atTop (𝓝 0)) ∧
    ∀ (a : Algebra M) (η : H),
      Tendsto (fun n => (w n*a*star (w n)).val η) atTop (𝓝 (a.val η))

universe u

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TwoRatioProductConstruction
attribute [-instance] _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The two-ratio product

The finite and remote matrix stages are concrete products. The two
off-diagonal modular eigenvalues follow from their finite product moments
and the KMS characterization of the supplied modular resolution.
-/

namespace KadisonKastler

noncomputable section

universe u

def concreteTwoRatioProductModel : TwoRatioProductModel.{u} :=
  twoRatioPointedProduct.toTwoRatioProductModel

end

end KadisonKastler

end OAI
end


