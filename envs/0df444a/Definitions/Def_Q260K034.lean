-- Prove2me | Definitions.Def_Q260K034
-- name    : Q260K034
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T07:55:25.244193+00:00
-- url     : https://prove2.me/theorems/09eaea32-6918-49e4-8eaa-8f056c32b5f7
-- title:
--   Definitions bundle Q260K034 of the split of OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 48 declarations of OpenAI's Lean: 17 definitions, 4 inductive types or structures and 27 theorems. The definitions and types are `OAI.KadisonKastler.AdmissibleOrthogonalFamily`, `OAI.KadisonKastler.FaithfulVectorBicentralizersScalar`, `OAI.KadisonKastler.FiniteFactorPublishedInputs`, `OAI.KadisonKastler.HaagerupCommutatorWitnesses`, `OAI.KadisonKastler.ModularCorePublishedInputs`, `OAI.KadisonKastler.ModularCyclicSpace`, `OAI.KadisonKastler.ModularSpectralResolution`, `OAI.KadisonKastler.ModularSpectralResolution.fourierPacket`, `OAI.KadisonKastler.PointedMatrixProduct.toTwoRatioProductModel`, `OAI.KadisonKastler.PointedMatrixSites.blockScalingPartialIsometry`, `OAI.KadisonKastler.PointedMatrixSites.centralizerBlockZero`, `OAI.KadisonKastler.ProjectionFamilyAdmissible`, `OAI.KadisonKastler.PublishedFieldTomiyamaFamily`, `OAI.KadisonKastler.StateAsymptoticallyCentral`, `OAI.KadisonKastler.TwoRatioProductModel`, `OAI.KadisonKastler.abelianDescentFactorOrder`, `OAI.KadisonKastler.projectionFamilyRemainder`, `OAI.KadisonKastler.spatialLeftAlgebraHom`, `OAI.KadisonKastler.stateBicentralizerMember`, `OAI.KadisonKastler.stateCentralizerAlgebra`, `OAI.KadisonKastler.stateCentralizerVonNeumann`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `KadisonKastler_AbelianActionStability`, `KadisonKastler_FiniteFactorApplication`, `KadisonKastler_ModularCoreStability`, `KadisonKastler_ModularCyclicGroup`, `KadisonKastler_ModularHaagerupWitnesses`, `KadisonKastler_ModularLocalizedPackets`, `KadisonKastler_ModularSiteEigen`, `KadisonKastler_PointedMatrixSum`, `KadisonKastler_ProductCentralizerSmallProjections`, `KadisonKastler_ProductScalingWords`, `KadisonKastler_ProjectionFamilyAdmissible`, `KadisonKastler_ProjectionFamilyMaximal`, `KadisonKastler_ProjectionFamilySpaces`, `KadisonKastler_PublishedModularSpectral`, `KadisonKastler_PublishedStandardIsomorphism`, `KadisonKastler_PublishedTwoRatioProduct`, `KadisonKastler_RemoteSiteDoubling`, `KadisonKastler_SpatialAssociatorAlgebra`, `KadisonKastler_SpatialBicentralizer`, `KadisonKastler_SpatialMatrixDensity`, `KadisonKastler_SpatialStateCentrality`, `KadisonKastler_StateBicentralizerTests`, `KadisonKastler_StateCentralSequenceAlgebra`, `KadisonKastler_StateCentralizerVonNeumann`, `KadisonKastler_StateCommutatorAlgebra`, `KadisonKastler_TomitaCentralizerGraph`, `KadisonKastler_TomitaLinearPolarCoordinates`, `KadisonKastler_TomitaVectorProjection`, `KadisonKastler_TwoRatioProductConstruction`.
--
--   **Imports.** It imports the published bundle `Def_StrongKadisonKastler`; the bundles `OAIQ075A028`, `Q260K032` and `Q260K071` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q260K037`, `Q260K038`, `Q260K039`, `Q260K040`, `Q260K041` and `Q260K072`; the statements `OAI_KadisonKastler_CommonTracialPositionData_exists_finiteFactor_isomorphism`, `OAI.KadisonKastler.FaithfulVectorStateHomogeneity.scalar_bicentralizers_of_one`, `OAI.KadisonKastler.FullMatrixCorner.spatial_of_common_entries`, `OAI.KadisonKastler.FullMatrixCorner.spatial_of_injective_matrix_subalgebra`, `OAI.KadisonKastler.ModularConjugationData.dominated_symmetric_projection_witness`, `OAI_KadisonKastler_ModularConjugationData_noncollinear_projection_witness`, `OAI.KadisonKastler.ModularConjugationData.symmetric_projection_witness`, `OAI.KadisonKastler.PointedMatrixSites.exists_represented_scalar_bicentralizer`, `OAI.KadisonKastler.PointedMatrixSites.spatial_state_bicentralizer_scalar`, `OAI.KadisonKastler.PointedMatrixSites.twoRatio_centralizer_diffuse`, `OAI.KadisonKastler.TypeIII1Factor.of_faithfulTensorRepresentation`, `OAI.KadisonKastler.TypeIIIFactor.exists_relative_projection_insertion`, `OAI.KadisonKastler.constructedStabilityCoreInputs`, `OAI.KadisonKastler.constructed_common_matrix_subfactor_spatial_stability`, `OAI_KadisonKastler_constructed_finiteFactor_spatial_of_matrixStages_and_boundary`, `OAI.KadisonKastler.exists_algebraic_modular_test_values`, `OAI.KadisonKastler.exists_bicentralizer_state_conjugate_limit`, `OAI.KadisonKastler.exists_modular_product_state_of_simple`, `OAI.KadisonKastler.exists_relative_projection_residual_gap`, `OAI.KadisonKastler.exists_relative_unitary_residual_gap`, `OAI.KadisonKastler.exists_standard_finiteFactor_isomorphism_of_published`, `OAI.KadisonKastler.exists_state_scaling_coisometry`, `OAI.KadisonKastler.expectedMatrixSubfactorModel_of_one_bicentralizer`, `OAI.KadisonKastler.expectedMatrixSubfactorModel_of_relative_bicentralizers`, `OAI.KadisonKastler.finiteFactor_spatial_of_published`, `OAI.KadisonKastler.haagerupCommutatorWitnesses_of_modular_product`, `OAI_KadisonKastler_kkDistance_reducing_commutants_after_alignment`, `OAI.KadisonKastler.modularCore_equiv_of_normal`, `OAI_KadisonKastler_nearInclusion_reducing_commutants_after_alignment`, `OAI.KadisonKastler.scalar_stateBicentralizer_of_isometric`, `OAI.KadisonKastler.stateBicentralizerMember_congr_vectorFunctional`, `OAI.KadisonKastler.stateBicentralizerMember_of_state_conjugate_limit`, `OAI.KadisonKastler.stateBicentralizerMember_of_unitary_reference_tests`, `OAI.KadisonKastler.stateBicentralizerMember.spatial_pullback`, `OAI.KadisonKastler.uniformFactorStability_of_properlyInfinite`, `OAI.KadisonKastler.uniform_II1_strong_stability`, `OAI.KadisonKastler.uniform_common_action_of_rescaled_graphs`, `OAI.KadisonKastler.uniform_modular_matrix_graph_strong_stability` and `OAI.KadisonKastler.uniform_prepared_matrix_strong_stability`; the proofs of `OAI_KadisonKastler_CommonTracialPositionData_exists_finiteFactor_isomorphism`, `OAI.KadisonKastler.FaithfulVectorStateHomogeneity.scalar_bicentralizers_of_one`, `OAI.KadisonKastler.FaithfulVectorStateHomogeneity.spatial_transport`, `OAI.KadisonKastler.FullMatrixCorner.spatial_of_common_entries`, `OAI.KadisonKastler.FullMatrixCorner.spatial_of_injective_matrix_subalgebra`, `OAI.KadisonKastler.ModularConjugationData.dominated_symmetric_projection_witness`, `OAI_KadisonKastler_ModularConjugationData_noncollinear_projection_witness`, `OAI.KadisonKastler.ModularConjugationData.symmetric_projection_witness`, `OAI.KadisonKastler.PointedMatrixSites.exists_scaling_coisometry_near`, `OAI.KadisonKastler.StateScales.spatialRight`, `OAI.KadisonKastler.TypeIIIFactor.exists_countable_amplification_unitary`, `OAI.KadisonKastler.TypeIIIFactor.exists_cyclic_separating_unit_vector`, `OAI.KadisonKastler.TypeIIIFactor.exists_cyclic_vector_same_state`, `OAI.KadisonKastler.TypeIIIFactor.exists_relative_matrix_state_of_projection_gap`, `OAI.KadisonKastler.TypeIIIFactor.exists_relative_positive_matrix_state_near_weight`, `OAI.KadisonKastler.TypeIIIFactor.exists_relative_projection_insertion`, `OAI.KadisonKastler.coisometry_conjugation_error_le`, `OAI.KadisonKastler.conjugates_vector_difference_sq_le`, `OAI.KadisonKastler.constructedStabilityCoreInputs`, `OAI.KadisonKastler.constructed_common_matrix_subfactor_spatial_stability`, `OAI_KadisonKastler_constructed_finiteFactor_spatial_of_matrixStages_and_boundary`, `OAI.KadisonKastler.exists_algebraic_modular_test_values`, `OAI.KadisonKastler.exists_corner_tracial_vector`, `OAI.KadisonKastler.exists_matrixClosure_state_retraction`, `OAI.KadisonKastler.exists_modular_product_state_of_simple`, `OAI.KadisonKastler.exists_positive_matrix_central_unit_vector`, `OAI.KadisonKastler.exists_properInfinite_matrix_preparation_of_embedding`, `OAI.KadisonKastler.exists_relative_positive_decomposition`, `OAI.KadisonKastler.exists_relative_projection_residual_gap`, `OAI.KadisonKastler.exists_selfAdjoint_two_vector_gap`, `OAI.KadisonKastler.exists_standard_finiteFactor_isomorphism_of_published`, `OAI.KadisonKastler.exists_tracial_vector_of_II1_cyclic`, `OAI.KadisonKastler.exists_tracial_vector_of_II1_separating`, `OAI.KadisonKastler.expectedMatrixSubfactorModel_of_one_bicentralizer`, `OAI.KadisonKastler.expectedMatrixSubfactorModel_of_projection_cuts_with_gap`, `OAI.KadisonKastler.expectedMatrixSubfactorModel_of_relative_bicentralizers`, `OAI.KadisonKastler.finiteFactor_spatial_of_published`, `OAI.KadisonKastler.functional_norm_eq_of_starEquiv`, `OAI.KadisonKastler.isometric_vector_separating`, `OAI_KadisonKastler_kkDistance_reducing_commutants_after_alignment`, `OAI.KadisonKastler.matrixCentralProjection_separating`, `OAI.KadisonKastler.matrixCentralVector_projection_state`, `OAI_KadisonKastler_nearInclusion_reducing_commutants_after_alignment`, `OAI.KadisonKastler.positiveCone_parts_mem_centralVectorSpace`, `OAI.KadisonKastler.positiveCone_separating_add`, `OAI.KadisonKastler.positiveVectorPinch_separating`, `OAI.KadisonKastler.positive_isometry_pullback_normalized`, `OAI.KadisonKastler.regularCore_not_factor_of_centralizing_vector_representation`, `OAI.KadisonKastler.relative_modularQuadratic_mem_central`, `OAI.KadisonKastler.relative_positiveCone_norm_sq_le_state_norm`, `OAI.KadisonKastler.stateBicentralizerMember_congr_vectorFunctional`, `OAI.KadisonKastler.typeIII_of_factorialCore`, `OAI.KadisonKastler.uniformFactorStability_of_properlyInfinite`, `OAI.KadisonKastler.uniform_II1_strong_stability`, `OAI.KadisonKastler.uniform_common_action_of_rescaled_graphs`, `OAI.KadisonKastler.uniform_prepared_matrix_strong_stability`, `OAI.KadisonKastler.unitary_comparison_centrality` and `OAI.KadisonKastler.unitary_state_transition_defect`.
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
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
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
import Mathlib.Data.Finset.Sort
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
import Mathlib.Topology.Instances.Real.Lemmas
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
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_StrongKadisonKastler
import Definitions.Def_OAIQ075A028
import Definitions.Def_Q260K032
import Definitions.Def_Q260K071

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PublishedStandardIsomorphism
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Common-position isomorphism from the published scalar inputs

The countable group is constructed from trace-dense unitaries. The
boundary, both scalar means, and double ergodicity are then supplied by
`PublishedBoundary`. The only additional input is the family of constant-
field specializations of Tomiyama's Theorem 1(2), Proceedings of the Japan
Academy 33 (1957), 608--612, pp. 608--609.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

universe u

variable (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]

/-- Tomiyama's same published theorem, specialized to every scalar field
base and group used on the fixed represented Hilbert space. -/
def PublishedFieldTomiyamaFamily : Prop :=
  ∀ (G D : Type u) [Group G] [TopologicalSpace G] [DiscreteTopology G]
    [MeasurableSpace D] (μ : Measure D) [IsFiniteMeasure μ],
    PublishedFieldTomiyama (G := G) (H := H) (μ := μ)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TomitaVectorProjection
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The state vector in the Tomita graph

Projection of `(Ω,0)` onto the unscaled graph is exactly half of `(Ω,JΩ)`.
This elementary identity identifies the state vector for the polar construction.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

theorem tomita_state_coefficient (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (a : Algebra M) :
    inner ℂ (J Ω) (J (star a.val Ω)) = inner ℂ Ω (a.val Ω) := by
  rw [conjugateIsometry_inner]
  change (starRingEnd ℂ) (inner ℂ Ω (star a.val Ω)) = _
  rw [inner_conj_symm, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_left]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TomitaCentralizerGraph
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

theorem vectorState_centralizer_star (Ω : H) (r : Algebra M)
    (hr : ∀ a : Algebra M,
      inner ℂ Ω ((r.val * a.val) Ω) = inner ℂ Ω ((a.val * r.val) Ω)) :
    ∀ a : Algebra M,
      inner ℂ Ω ((star r.val * a.val) Ω) = inner ℂ Ω ((a.val * star r.val) Ω) := by
  intro a
  have h := congrArg star (hr (star a))
  change star (inner ℂ Ω ((r.val * star a.val) Ω)) =
    star (inner ℂ Ω ((star a.val * r.val) Ω)) at h
  rw [vectorState_star, vectorState_star, star_mul, star_mul, star_star] at h
  exact h.symm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularCyclicGroup
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

abbrev ModularCyclicSpace (M : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H) (Ω x : H) :=
  ResolventCyclicL2 (graphResolvent M J Ω 1) (graphResolvent_positive J Ω 1).isSelfAdjoint x

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PublishedModularSpectral
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

/-- The part of modular spectral theory used by the application. All
operators retained here are bounded, including the restricted inverse. -/
structure ModularSpectralResolution (M : VonNeumannAlgebra H) (Ω : H) where
  group : Multiplicative ℝ →* unitary (H →L[ℂ] H)
  continuous : ∀ x, Continuous (fun t : ℝ => (group (Multiplicative.ofAdd t) : H →L[ℂ] H) x)
  normalizes : ∀ t, Conjugates (group t) M M
  isModular : IsModularStateGroup M Ω group
  centralizer_fixed : ∀ x ∈ M, ProductStateCentralizes M Ω x →
    ∀ t, unitaryConj (group t) x = x
  upperCut : ℝ → H →L[ℂ] H
  projection : ∀ a, IsStarProjection (upperCut a)
  upper_contracts : ∀ a, ‖upperCut a‖ ≤ 1
  lower_contracts : ∀ a, ‖1 - upperCut a‖ ≤ 1
  measurable : ∀ a x, AEStronglyMeasurable (fun ξ : ℝ => upperCut (a - 2 * Real.pi * ξ) x) volume
  gauge_identity : ∀ a,
    (star (regularGauge group continuous) : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) *
        regularFrequencyProjection a *
        (regularGauge group continuous : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) =
      (Lp.fourierTransformₗᵢ ℝ H).symm.conjStarAlgEquiv
        (regularFieldOperator volume (fun ξ => upperCut (a - 2 * Real.pi * ξ))
          (measurable a) 1 (Filter.Eventually.of_forall fun _ξ => upper_contracts _))
  high_inverse : ∀ (J : H ≃ₗᵢ⋆[ℂ] H) a, ∃ R : H →L[ℂ] H,
    ‖R‖ ≤ 1 + Real.exp (-(1 / 2 : ℝ)) ∧
    (1 - graphResolvent M J Ω (Real.exp (-a / 2))) * R = upperCut (a + 1 / 2) ∧
    upperCut (a + 1 / 2) * R = R
  low_bound : ∀ (J : H ≃ₗᵢ⋆[ℂ] H) a,
    ‖(1 - upperCut (a - 1 / 2)) * (1 - graphResolvent M J Ω (Real.exp (-a / 2)))‖ ≤
      Real.exp (-(1 / 2 : ℝ)) / (1 + Real.exp (-(1 / 2 : ℝ)))
  low_support : ∀ (J : H ≃ₗᵢ⋆[ℂ] H) a,
    (1 - upperCut (a - 1 / 2)) * (1 - graphResolvent M J Ω (Real.exp (-a / 2))) *
        (1 - upperCut (a - 1 / 2)) =
      (1 - upperCut (a - 1 / 2)) * (1 - graphResolvent M J Ω (Real.exp (-a / 2)))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TomitaLinearPolarCoordinates
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.CommonTracialPositionData.rightEquiv_transportEquiv _root_.OAI.KadisonKastler.FiniteInnerAverage.algebraApply_sub _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.StandardTracialPosition.diagonalRepresentation_vector _root_.OAI.KadisonKastler.algebraConstantField_coe _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.concreteDerivation_apply _root_.OAI.KadisonKastler.concreteDiagonalSequenceUnitary_coe _root_.OAI.KadisonKastler.concreteDiagonalSequence_apply _root_.OAI.KadisonKastler.concreteDiagonalUnitary_coe _root_.OAI.KadisonKastler.constantAlgebraUnitaryFamily_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.cyclicOrbitEquiv_val _root_.OAI.KadisonKastler.cyclicOrbitHom_apply _root_.OAI.KadisonKastler.faithfulCyclicEquiv_coe _root_.OAI.KadisonKastler.faithfulCyclicHom_apply _root_.OAI.KadisonKastler.matrixClosureVectorTrace_apply _root_.OAI.KadisonKastler.matrixLiftUnitaryAt_coe _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.minimalCyclicRetraction_compression _root_.OAI.KadisonKastler.normalCyclicEquiv_val _root_.OAI.KadisonKastler.normalCyclicHom_apply _root_.OAI.KadisonKastler.normalPairEquiv_coe _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.spatialTransportEquiv_apply _root_.OAI.KadisonKastler.spatialTransportEquiv_vector _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.typeICyclicHom_apply _root_.OAI.KadisonKastler.typeICyclicOperator_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply _root_.OAI.KadisonSimilarity.predualRestriction_apply _root_.OAI.KadisonSimilarity.tracialInclusionIsometry_vector _root_.OAI.NaimarkZFC.gns_apply_coe
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

@[simp] theorem tomitaLinearPolarUnitary_symm_apply (a : H) :
    (tomitaLinearPolarUnitary J Ω hsep hcyc).symm a =
      tomitaPolarConjugation J Ω hsep hcyc (J.symm a) := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteFactorApplication
attribute [-instance] _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Uniform strong stability of separably acting II₁ factors

Boundary means, field projections and finite type stability combine
with a common tracial position and uniform amplification to give a
small spatial implementation.
-/

namespace KadisonKastler

noncomputable section

universe u

local instance applicationFactorOrder_rc10b75_1 {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] (P : VonNeumannAlgebra K) :
    PartialOrder (Algebra P) := CStarAlgebra.spectralOrder _
local instance applicationFactorStarOrder_rc10b75_1 {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] (P : VonNeumannAlgebra K) :
    StarOrderedRing (Algebra P) := CStarAlgebra.spectralOrderedRing _
/-- The published specializations used for the finite-factor application.
Each field refers to a separately documented published input. -/
structure FiniteFactorPublishedInputs : Prop where
  boundary : PublishedBoundary.{u}
  tomiyama : ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H], PublishedFieldTomiyamaFamily H
  finiteType : ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H], PublishedFiniteType (H := H)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_AbelianActionStability
attribute [-instance] _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Abelian action correction and descent

Finite-Cesaro means give the scalar averaging used in the action and
fixed-point arguments. These results apply to the additive real modular
group and its character group, viewed as discrete abelian groups.
-/

namespace KadisonKastler

noncomputable section

universe u v w s

section CharacterDescent

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {G : Type w} [Group G] {L : Type s} [CommGroup L]
  [TopologicalSpace L] [DiscreteTopology L]
  {M N : VonNeumannAlgebra H}

local instance abelianDescentFactorOrder (P : VonNeumannAlgebra H) :
    PartialOrder (Algebra P) := CStarAlgebra.spectralOrder _
local instance abelianDescentFactorStarOrder (P : VonNeumannAlgebra H) :
    StarOrderedRing (Algebra P) := CStarAlgebra.spectralOrderedRing _

end CharacterDescent

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularCoreStability
attribute [-instance] _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 0

namespace OAI

/-! # Completing modular graph stability by descent through the regular core

The source core belongs to the neighboring modular group.
The tensor gap is proved from the same complete maps used for graph
comparison and is propagated through the small action alignment.
-/

namespace KadisonKastler

noncomputable section

universe u

local instance modularCoreOrder_rc10b75_1 {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (P : VonNeumannAlgebra H) :
    PartialOrder (Algebra P) := CStarAlgebra.spectralOrder _
local instance modularCoreStarOrder_rc10b75_1 {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (P : VonNeumannAlgebra H) :
    StarOrderedRing (Algebra P) := CStarAlgebra.spectralOrderedRing _
/-- The modular representation and source-core type are explicit hypotheses
for descent through the regular core. -/
structure ModularCorePublishedInputs : Prop where
  finite : FiniteFactorPublishedInputs.{u}
  coreCommutant : PublishedRegularCommutant.{u}
  realSpectral : PublishedRealSpectralCommutant.{u}
  diagonal : PublishedRealDiagonalDecomposition.{u}
  copies : PublishedProperInfiniteProjectionCopies.{u}
  spectral : PublishedVonNeumannSpectralCut.{u}
  comparison : PublishedTypeIIIProjectionComparison.{u}
  sakai : PublishedSimpleDerivationInner.{u}
  hardy : PublishedHardyMultiplierEvaluation.{u}
  correction : ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (M : VonNeumannAlgebra H), PublishedMultiplicationCorrection M

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularLocalizedPackets
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Fourier packets localized by the modular spectral cuts

The already constructed Fourier gauge identity transports bounded scalar
frequency windows to short modular spectral intervals, fiber by fiber.
The norm identity gives the total weight of the resulting vector states.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {Ω : H}

namespace ModularSpectralResolution

variable (S : ModularSpectralResolution M Ω)

def fourierPacket (φ : Lp ℂ 2 (volume : Measure ℝ)) (ξ : H) : RegularCoreHilbert H :=
  (Lp.fourierTransformₗᵢ ℝ H) (regularGaugedPacket S.group S.continuous φ ξ)

end ModularSpectralResolution

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularHaagerupWitnesses
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The quantitative Haagerup premise from constructed modular data

The uniform constant is six. This is the sufficient condition appearing
in AHHM, arXiv:1804.05706v2, Theorem 7.2, specialized to a fixed faithful
cyclic vector. The implication to scalar bicentralizers is not assumed here.
-/

namespace KadisonKastler

open MeasureTheory NaimarkZFC Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {Ω : H}

def HaagerupCommutatorWitnesses (d : ModularConjugationData M Ω) : Prop :=
  ∀ a : Algebra M, a.val Ω=d.rightAction (star a) Ω →
    productVectorState Ω a.val=0 → ‖a.val Ω‖=1 →
    ∀ δ : ℝ, 0 < δ → ∃ b : Algebra M,
      ‖b.val Ω‖+‖(b*a).val Ω‖ < 6*‖(a*b-b*a).val Ω‖ ∧
      ‖b.val Ω-d.rightAction b Ω‖ < δ*‖(a*b-b*a).val Ω‖

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularSiteEigen
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSignedGroup_finite _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.Generator.MatrixUnitSystem.adaptedBasis_apply _root_.OAI.Generator.MatrixUnitSystem.initialColumn_apply _root_.OAI.Generator.orthonormalMatrixUnits_entry_apply _root_.OAI.KadisonKastler.CommonTracialPositionData.rightEquiv_transportEquiv _root_.OAI.KadisonKastler.FiniteInnerAverage.algebraApply_sub _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.PointedMatrixSites.reindexEquivalence_word _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.ScalarInvariantMean.stateOrbitScalar_apply _root_.OAI.KadisonKastler.StandardTracialPosition.diagonalRepresentation_vector _root_.OAI.KadisonKastler.algebraConstantField_coe _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.concreteDerivation_apply _root_.OAI.KadisonKastler.concreteDiagonalSequenceUnitary_coe _root_.OAI.KadisonKastler.concreteDiagonalSequence_apply _root_.OAI.KadisonKastler.concreteDiagonalUnitary_coe _root_.OAI.KadisonKastler.conjugateMatrixUnits_entry _root_.OAI.KadisonKastler.conjugatedMatrixUnits_entry _root_.OAI.KadisonKastler.constantAlgebraUnitaryFamily_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.cyclicOrbitEquiv_val _root_.OAI.KadisonKastler.cyclicOrbitHom_apply _root_.OAI.KadisonKastler.faithfulCyclicEquiv_coe _root_.OAI.KadisonKastler.faithfulCyclicHom_apply _root_.OAI.KadisonKastler.matrixClosureVectorTrace_apply _root_.OAI.KadisonKastler.matrixLiftUnitaryAt_coe _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.mem_twoRatioComplementSites _root_.OAI.KadisonKastler.minimalCyclicRetraction_compression _root_.OAI.KadisonKastler.normalCyclicEquiv_val _root_.OAI.KadisonKastler.normalCyclicHom_apply _root_.OAI.KadisonKastler.normalPairEquiv_coe _root_.OAI.KadisonKastler.pointedRawVacuum_apply _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.spatialMatrixUnits_entry _root_.OAI.KadisonKastler.spatialTransportEquiv_vector _root_.OAI.KadisonKastler.tomitaLinearPolarUnitary_apply _root_.OAI.KadisonKastler.tomitaLinearPolarUnitary_symm_apply _root_.OAI.KadisonKastler.tomitaPolarCoordinates_root _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.typeICyclicHom_apply _root_.OAI.KadisonKastler.typeICyclicOperator_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply _root_.OAI.KadisonSimilarity.predualRestriction_apply _root_.OAI.KadisonSimilarity.tracialInclusionIsometry_vector _root_.OAI.NaimarkZFC.gns_apply_coe
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

/-- The KMS condition turns a weighted trace identity into an operator eigenvalue. -/
theorem modular_eigen_of_state_balance
    (m : ModularSpectralResolution M Ω)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (x : H →L[ℂ] H) (hx : x ∈ M) (L : ℝ) (hL : 0 ≤ L)
    (hbal : ∀ y ∈ M, productVectorState Ω (y * x) =
      (Real.exp (-L) : ℂ) * productVectorState Ω (x * y)) (t : ℝ) :
    unitaryConj (m.group (Multiplicative.ofAdd t)) x =
      Complex.exp (Complex.I * (L : ℂ) * t) • x := by
  let v := m.group (Multiplicative.ofAdd t)
  let c := Complex.exp (Complex.I * (L : ℂ) * t)
  have hcoeff (y : H →L[ℂ] H) (hy : y ∈ M) :
      productVectorState Ω (unitaryConj v x * y) = c * productVectorState Ω (x * y) := by
    obtain ⟨f, hfc, hfd, hfb, hf₀, hf₁⟩ := m.isModular.kms x hx y hy
    have he (s : ℝ) : f ((s : ℂ) + Complex.I) = (Real.exp (-L) : ℂ) * f s := by
      rw [hf₁, hf₀]
      exact state_balance_unitary _ (m.normalizes _) (m.isModular.fixes_vector _) x _ hbal y hy
    have h := kms_strip_exponential hL hfc hfd hfb he t
    have hfzero : f 0 = productVectorState Ω (x * y) := by
      simpa using hf₀ (0 : ℝ)
    rw [hf₀ t, hfzero] at h
    exact h
  let d : H →L[ℂ] H := unitaryConj v x - c • x
  have hdx : d ∈ M := by
    apply M.sub_mem
    · have hmem : unitaryConj v x ∈ unitaryConj v '' (M : Set (H →L[ℂ] H)) :=
        Set.mem_image_of_mem _ hx
      rwa [m.normalizes (Multiplicative.ofAdd t)] at hmem
    · exact M.smul_mem hx c
  have hstar : star d ∈ M := M.toStarSubalgebra.star_mem' hdx
  have hz : productVectorState Ω (d * star d) = 0 := by
    have h := hcoeff (star d) hstar
    change productVectorState Ω
      ((unitaryConj v x - c • x) * star d) = 0
    simpa only [sub_mul, smul_mul_assoc, productVectorState, sub_apply, smul_apply,
      inner_sub_right, inner_smul_right, sub_eq_zero] using h
  have hinner : inner ℂ ((star d) Ω) ((star d) Ω) = 0 := by
    calc
      _ = productVectorState Ω (d * star d) := by
        change inner ℂ ((star d) Ω) ((star d) Ω) = inner ℂ Ω (d ((star d) Ω))
        exact ContinuousLinearMap.adjoint_inner_left d ((star d) Ω) Ω
      _ = 0 := hz
  have hvz : (star d) Ω = 0 := inner_self_eq_zero.mp hinner
  have hzalg : (⟨star d, hstar⟩ : M.toStarSubalgebra) = 0 := hsep (by
    change (star d) Ω = (0 : H →L[ℂ] H) Ω
    simpa using hvz)
  have hs : star d = 0 := congrArg Subtype.val hzalg
  have hd : d = 0 := by simpa only [star_star, star_zero] using congrArg star hs
  exact sub_eq_zero.mp hd

namespace PointedMatrixSites

/-- The off-diagonal matrix unit at every site has its prescribed modular frequency. -/
theorem twoRatio_site_modular_eigen
    (S : PointedMatrixSites M Ω twoRatioSiteParameter)
    (m : ModularSpectralResolution M Ω) (i : TwoRatioSite) (t : ℝ) :
    unitaryConj (m.group (Multiplicative.ofAdd t)) ((S.site i).entry 0 1) =
      Complex.exp (Complex.I * ((-Real.log (twoRatioSiteParameter i) : ℝ) : ℂ) * t) •
        (S.site i).entry 0 1 := by
  have hν := S.valid i
  have hx : (S.site i).entry 0 1 ∈ M := by
    have hmem : (S.site i).entry 0 1 ∈ ⨆ j, (S.site j).algebra :=
      (le_iSup (fun j => (S.site j).algebra) i) ((S.site i).entry_mem 0 1)
    exact Eq.mpr (congrArg (fun N : VonNeumannAlgebra H => (S.site i).entry 0 1 ∈ N)
      S.generates) (subset_generatedVonNeumannAlgebra _ hmem)
  apply modular_eigen_of_state_balance m S.separating _ hx _
    (neg_nonneg.mpr (Real.log_nonpos hν.1.le hν.2.le))
  intro y hy
  have h := S.twoRatio_site_balance i 0 1 y hy
  have hw : (twoSiteWeight (twoRatioSiteParameter i) 0 : ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    simp only [twoSiteWeight, ite_true, if_true, ne_eq, inv_eq_zero]
    linarith [hν.1]
  have hw₁ : (twoSiteWeight (twoRatioSiteParameter i) 1 : ℂ) =
      (twoRatioSiteParameter i : ℂ) * (twoSiteWeight (twoRatioSiteParameter i) 0 : ℂ) := by
    simp [twoSiteWeight, div_eq_mul_inv]
  rw [hw₁] at h
  rw [neg_neg, Real.exp_log hν.1]
  apply mul_left_cancel₀ hw
  calc
    _ = ((twoRatioSiteParameter i : ℂ) * (twoSiteWeight (twoRatioSiteParameter i) 0 : ℂ)) *
        productVectorState Ω ((S.site i).entry 0 1 * y) := h.symm
    _ = _ := by ring

theorem twoRatio_site_modular_star_eigen
    (S : PointedMatrixSites M Ω twoRatioSiteParameter)
    (m : ModularSpectralResolution M Ω) (i : TwoRatioSite) (t : ℝ) :
    unitaryConj (star (m.group (Multiplicative.ofAdd t))) ((S.site i).entry 0 1) =
      regularCharacterScalar (Real.log (twoRatioSiteParameter i)) t •
        (S.site i).entry 0 1 := by
  rw [regularGroup_star_eq]
  have h := S.twoRatio_site_modular_eigen m i (-t)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 2
  rw [regularCharacterScalar, Circle.coe_exp]
  congr 1
  push_cast
  ring

end PointedMatrixSites

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SpatialMatrixDensity
attribute [-instance] _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.spatialHilbert_separable _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Increasing finite spatial matrix images are weakly dense -/

namespace KadisonKastler

open UnitalTomsWinter Generator Filter
open scoped Topology

noncomputable section

universe u

variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem spatialRight_mem_generated_contraction
    (hK : PublishedKaplanskyDensity.{u})
    (B : StarSubalgebra ℂ (K →L[ℂ] K))
    (A : StarSubalgebra ℂ (SpatialHilbert H K →L[ℂ] SpatialHilbert H K))
    (hBA : ∀ b ∈ B, spatialRight (H := H) b ∈ A)
    (b : K →L[ℂ] K) (hb : b ∈ generatedVonNeumannAlgebra B) (hn : ‖b‖ ≤ 1) :
    spatialRight (H := H) b ∈ generatedVonNeumannAlgebra A := by
  classical
  have hb' : b ∈ Set.centralizer (Set.centralizer (B : Set (K →L[ℂ] K))) := by
    change b ∈ (generatedVonNeumannAlgebra B : Set (K →L[ℂ] K)) at hb
    rwa [generatedVonNeumannAlgebra_coe] at hb
  obtain ⟨a, ha, hlim⟩ := hK.exists_strong_contraction_net B b hb' hn
  let c : Finset K × ℕ → Algebra (generatedVonNeumannAlgebra A) := fun d =>
    ⟨spatialRight (H := H) (a d),
      subset_generatedVonNeumannAlgebra A (hBA _ (a d).property)⟩
  apply Generator.Tracial.weak_operator_limit_mem (l := (atTop : Filter (Finset K × ℕ)))
    (generatedVonNeumannAlgebra A) c
  intro x y
  exact (continuous_const.inner continuous_id).continuousAt.tendsto.comp
    (spatialRight_tendsto_strong (fun d => (a d : K →L[ℂ] K)) b ha hlim x)

/-- The right spatial representation carries the generated von Neumann
algebra into the von Neumann algebra generated by its images. -/
theorem spatialRight_mem_generated
    (hK : PublishedKaplanskyDensity.{u})
    (B : StarSubalgebra ℂ (K →L[ℂ] K))
    (A : StarSubalgebra ℂ (SpatialHilbert H K →L[ℂ] SpatialHilbert H K))
    (hBA : ∀ b ∈ B, spatialRight (H := H) b ∈ A)
    (b : K →L[ℂ] K) (hb : b ∈ generatedVonNeumannAlgebra B) :
    spatialRight (H := H) b ∈ generatedVonNeumannAlgebra A := by
  by_cases hzero : b = 0
  · rw [hzero, map_zero]
    exact (generatedVonNeumannAlgebra A).zero_mem
  have hp : 0 < ‖b‖ := norm_pos_iff.mpr hzero
  have hc : (‖b‖ : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hbn : ‖(‖b‖ : ℂ)⁻¹ • b‖ ≤ 1 := by
    simp only [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hp, inv_mul_cancel₀ hp.ne']
    exact le_rfl
  have hs := spatialRight_mem_generated_contraction hK B A hBA
    ((‖b‖ : ℂ)⁻¹ • b) ((generatedVonNeumannAlgebra B).smul_mem hb _) hbn
  have hr := (generatedVonNeumannAlgebra A).smul_mem hs (‖b‖ : ℂ)
  rwa [← map_smul, smul_smul, mul_inv_cancel₀ hc, one_smul] at hr

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SpatialAssociatorAlgebra
attribute [-instance] _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.spatialHilbert_separable _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
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

theorem spatialLeft_mem_generated_contraction
    (hK : PublishedKaplanskyDensity.{u})
    (B : StarSubalgebra ℂ (H →L[ℂ] H))
    (A : StarSubalgebra ℂ (SpatialHilbert H K →L[ℂ] SpatialHilbert H K))
    (hBA : ∀ b ∈ B, spatialLeft (K := K) b ∈ A)
    (b : H →L[ℂ] H) (hb : b ∈ generatedVonNeumannAlgebra B) (hn : ‖b‖ ≤ 1) :
    spatialLeft (K := K) b ∈ generatedVonNeumannAlgebra A := by
  classical
  have hb' : b ∈ Set.centralizer (Set.centralizer (B : Set (H →L[ℂ] H))) := by
    change b ∈ (generatedVonNeumannAlgebra B : Set (H →L[ℂ] H)) at hb
    rwa [generatedVonNeumannAlgebra_coe] at hb
  obtain ⟨a, ha, hlim⟩ := hK.exists_strong_contraction_net B b hb' hn
  let c : Finset H × ℕ → Algebra (generatedVonNeumannAlgebra A) := fun d =>
    ⟨spatialLeft (K := K) (a d),
      subset_generatedVonNeumannAlgebra A (hBA _ (a d).property)⟩
  apply Generator.Tracial.weak_operator_limit_mem (l := (atTop : Filter (Finset H × ℕ)))
    (generatedVonNeumannAlgebra A) c
  intro x y
  exact (continuous_const.inner continuous_id).continuousAt.tendsto.comp
    (spatialLeft_tendsto_strong (fun d => (a d : H →L[ℂ] H)) b ha hlim x)

/-- The first-leg representation preserves membership in generated von Neumann algebras. -/
theorem spatialLeft_mem_generated
    (hK : PublishedKaplanskyDensity.{u})
    (B : StarSubalgebra ℂ (H →L[ℂ] H))
    (A : StarSubalgebra ℂ (SpatialHilbert H K →L[ℂ] SpatialHilbert H K))
    (hBA : ∀ b ∈ B, spatialLeft (K := K) b ∈ A)
    (b : H →L[ℂ] H) (hb : b ∈ generatedVonNeumannAlgebra B) :
    spatialLeft (K := K) b ∈ generatedVonNeumannAlgebra A := by
  by_cases hzero : b = 0
  · rw [hzero, map_zero]
    exact (generatedVonNeumannAlgebra A).zero_mem
  have hp : 0 < ‖b‖ := norm_pos_iff.mpr hzero
  have hc : (‖b‖ : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hbn : ‖(‖b‖ : ℂ)⁻¹ • b‖ ≤ 1 := by
    simp only [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hp, inv_mul_cancel₀ hp.ne']
    exact le_rfl
  have hs := spatialLeft_mem_generated_contraction hK B A hBA
    ((‖b‖ : ℂ)⁻¹ • b) ((generatedVonNeumannAlgebra B).smul_mem hb _) hbn
  have hr := (generatedVonNeumannAlgebra A).smul_mem hs (‖b‖ : ℂ)
  rwa [← map_smul, smul_smul, mul_inv_cancel₀ hc, one_smul] at hr

theorem spatialLeft_mem_of_generated
    (hK : PublishedKaplanskyDensity.{u}) (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (Q : VonNeumannAlgebra (SpatialHilbert H K))
    (hS : ∀ x ∈ S, spatialLeft (K := K) x ∈ Q)
    {x : H →L[ℂ] H} (hx : x ∈ generatedVonNeumannAlgebra S) :
    spatialLeft (K := K) x ∈ Q := by
  have h := spatialLeft_mem_generated hK S Q.toStarSubalgebra hS x hx
  rwa [generated_of_vonNeumann] at h

theorem spatialRight_mem_of_generated
    (hK : PublishedKaplanskyDensity.{u}) (S : StarSubalgebra ℂ (K →L[ℂ] K))
    (Q : VonNeumannAlgebra (SpatialHilbert H K))
    (hS : ∀ x ∈ S, spatialRight (H := H) x ∈ Q)
    {x : K →L[ℂ] K} (hx : x ∈ generatedVonNeumannAlgebra S) :
    spatialRight (H := H) x ∈ Q := by
  have h := spatialRight_mem_generated hK S Q.toStarSubalgebra hS x hx
  rwa [generated_of_vonNeumann] at h

end Generated

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PointedMatrixSum
attribute [-instance] _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.spatialHilbert_separable _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
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

/-- Separation in each tensor leg implies separation of the product
vector, without requiring supplied modular conjugations. -/
theorem separating_spatialProduct_vector_of_separating
    (M : VonNeumannAlgebra H) (N : VonNeumannAlgebra K) (Ω : H) (ξ : K)
    (hM : Function.Injective (algebraVectorMap M Ω))
    (hN : Function.Injective (algebraVectorMap N ξ)) :
    Function.Injective (algebraVectorMap (spatialProductAlgebra M N) (tensorVector ξ Ω)) := by
  have hcM : DenseRange (algebraVectorMap M.commutant Ω) := by
    apply Generator.commutant_orbit_dense M Ω
    intro a ha
    apply hM
    change a.val Ω = (0 : H →L[ℂ] H) Ω
    simpa only [zero_apply] using ha
  have hcN : DenseRange (algebraVectorMap N.commutant ξ) := by
    apply Generator.commutant_orbit_dense N ξ
    intro a ha
    apply hN
    change a.val ξ = (0 : K →L[ℂ] K) ξ
    simpa only [zero_apply] using ha
  have hsmall := denseRange_spatialProduct_vector M.commutant N.commutant Ω ξ hcM hcN
  have hlarge : DenseRange (algebraVectorMap (spatialProductAlgebra M N).commutant
      (tensorVector ξ Ω)) := by
    apply Dense.mono _ hsmall
    rintro _ ⟨a, rfl⟩
    exact ⟨⟨a.val, spatialProduct_commutants_le M N a.property⟩, rfl⟩
  intro a b hab
  apply Subtype.ext
  apply operator_eq_of_mem_commutant_of_eq_on_cyclicVector
    (spatialProductAlgebra M N).commutant (tensorVector ξ Ω) hlarge a.val b.val
  · rw [VonNeumannAlgebra.commutant_commutant]
    exact a.property
  · rw [VonNeumannAlgebra.commutant_commutant]
    exact b.property
  · exact hab

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_StateCentralizerVonNeumann
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.CommonTracialPositionData.rightEquiv_transportEquiv _root_.OAI.KadisonKastler.FiniteInnerAverage.algebraApply_sub _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.StandardTracialPosition.diagonalRepresentation_vector _root_.OAI.KadisonKastler.algebraConstantField_coe _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.concreteDerivation_apply _root_.OAI.KadisonKastler.concreteDiagonalSequenceUnitary_coe _root_.OAI.KadisonKastler.concreteDiagonalSequence_apply _root_.OAI.KadisonKastler.concreteDiagonalUnitary_coe _root_.OAI.KadisonKastler.constantAlgebraUnitaryFamily_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.cyclicOrbitEquiv_val _root_.OAI.KadisonKastler.cyclicOrbitHom_apply _root_.OAI.KadisonKastler.faithfulCyclicEquiv_coe _root_.OAI.KadisonKastler.faithfulCyclicHom_apply _root_.OAI.KadisonKastler.matrixClosureVectorTrace_apply _root_.OAI.KadisonKastler.matrixLiftUnitaryAt_coe _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.minimalCyclicRetraction_compression _root_.OAI.KadisonKastler.normalCyclicEquiv_val _root_.OAI.KadisonKastler.normalCyclicHom_apply _root_.OAI.KadisonKastler.normalPairEquiv_coe _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.spatialTransportEquiv_vector _root_.OAI.KadisonKastler.tomitaLinearPolarUnitary_apply _root_.OAI.KadisonKastler.tomitaLinearPolarUnitary_symm_apply _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.typeICyclicHom_apply _root_.OAI.KadisonKastler.typeICyclicOperator_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 0

namespace OAI

/-! # The exact vector-state centralizer as a von Neumann algebra

Strong approximation preserves its defining matrix-coefficient identities.
The reference vector restricts to a faithful trace. For the fixed product
construction, finite-site swaps make this centralizer a factor.
-/

namespace KadisonKastler

open Generator Generator.Tracial UltrapowerBridge Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

def stateCentralizerAlgebra (ξ : H) : StarSubalgebra ℂ (H →L[ℂ] H) where
  carrier := {a | a ∈ M ∧ ProductStateCentralizes M ξ a}
  zero_mem' := ⟨M.zero_mem,by intro b hb; simp [productVectorState]⟩
  one_mem' := ⟨M.one_mem,by intro b hb; simp only [one_mul,mul_one]⟩
  add_mem' := by
    rintro a b ⟨ha,hac⟩ ⟨hb,hbc⟩
    refine ⟨M.add_mem ha hb,?_⟩
    intro c hc
    simpa only [add_mul,mul_add,productVectorState,add_apply,inner_add_right] using
      congrArg₂ (·+·) (hac c hc) (hbc c hc)
  mul_mem' := by
    rintro a b ⟨ha,hac⟩ ⟨hb,hbc⟩
    refine ⟨M.mul_mem ha hb,?_⟩
    intro c hc
    calc
      _ = productVectorState ξ (a*(b*c)) := by rw [mul_assoc]
      _ = productVectorState ξ ((b*c)*a) := hac _ (M.mul_mem hb hc)
      _ = productVectorState ξ (b*(c*a)) := by rw [mul_assoc]
      _ = productVectorState ξ ((c*a)*b) := hbc _ (M.mul_mem hc ha)
      _ = _ := by rw [mul_assoc]
  algebraMap_mem' z := by
    refine ⟨M.algebraMap_mem z,?_⟩
    intro a ha
    simp only [Algebra.algebraMap_eq_smul_one,smul_mul_assoc,mul_smul_comm,one_mul,mul_one]
  star_mem' := by
    rintro a ⟨ha,hac⟩
    refine ⟨M.toStarSubalgebra.star_mem' ha,?_⟩
    intro b hb
    exact vectorState_centralizer_star ξ (⟨a,ha⟩ : Algebra M)
      (fun c => hac c.val c.property) (⟨b,hb⟩ : Algebra M)

theorem stateCentralizerAlgebra_bicommutant (ξ : H) :
    Set.centralizer (Set.centralizer (stateCentralizerAlgebra (M := M) ξ :
      Set (H →L[ℂ] H)))=stateCentralizerAlgebra (M := M) ξ := by
  classical
  apply Set.Subset.antisymm
  · intro T hT
    have hTM : T ∈ M := by
      rw [← SetLike.mem_coe,← M.centralizer_centralizer]
      intro R hR
      exact hT R (fun a ha => hR a ha.1)
    refine ⟨hTM,?_⟩
    intro b hb
    obtain ⟨a,ha⟩ := bicommutant_exists_strong_net (stateCentralizerAlgebra (M := M) ξ) T hT
    have hl : Tendsto (fun i => inner ℂ ξ ((a i).val (b ξ))) atTop
        (𝓝 (inner ℂ ξ (T (b ξ)))) := tendsto_const_nhds.inner (ha (b ξ))
    have hr : Tendsto (fun i => inner ℂ ξ (b ((a i).val ξ))) atTop
        (𝓝 (inner ℂ ξ (b (T ξ)))) :=
      tendsto_const_nhds.inner ((b.continuous.tendsto (T ξ)).comp (ha ξ))
    apply tendsto_nhds_unique hl
    exact hr.congr' (Eventually.of_forall (fun i => ((a i).property.2 b hb).symm))
  · intro T hT R hR
    exact (hR T hT).symm

def stateCentralizerVonNeumann (ξ : H) : VonNeumannAlgebra H where
  toStarSubalgebra := stateCentralizerAlgebra (M := M) ξ
  centralizer_centralizer' := stateCentralizerAlgebra_bicommutant ξ

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PublishedTwoRatioProduct
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSignedGroup_finite _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The pointed infinite-product construction used by the application

Blackadar, *Operator Algebras*, III.3.1.1--3 (pp.293--295), constructs
the countable pointed tensor product from the finite-site algebras and
product states. For faithful matrix states the local left and right
orbits are dense. Disjoint finite blocks have product matrix moments;
an unused block with the same site types gives `RemoteProductBlock`.

The site modular action is conjugation by the diagonal density matrix,
and the modular operator of the product is the tensor product of the
site operators: III.4.4.7--9 and III.4.5.8 (pp.316--319). Only the two
off-diagonal eigenoperators are retained below. No centralizer or core
factoriality, type classification, absorption, or stability is assumed.
-/

namespace KadisonKastler

noncomputable section

universe u

/-- Concrete construction data for countably many sites of each of the
two fixed matrix-state types. Finite complement moments, rather than
irreducibility, are the retained input. -/
structure TwoRatioProductModel where
  K : Type u
  [normedK : NormedAddCommGroup K]
  [innerK : InnerProductSpace ℂ K]
  [completeK : CompleteSpace K]
  [nontrivialK : Nontrivial K]
  [separableK : TopologicalSpace.SeparableSpace K]
  stages : ProductMatrixStages (H := K)
  coordinates : PointedMatrixSites stages.algebra stages.vector twoRatioSiteParameter
  lambdaSite : Generator.MatrixUnitSystem (Fin 2) (K →L[ℂ] K)
  muSite : Generator.MatrixUnitSystem (Fin 2) (K →L[ℂ] K)
  lambda_mem : lambdaSite.algebra ≤ stages.algebra.toStarSubalgebra
  mu_mem : muSite.algebra ≤ stages.algebra.toStarSubalgebra
  lambda_eigen : ∀ (m : ModularSpectralResolution stages.algebra stages.vector) (t : ℝ),
    unitaryConj (star (m.group (Multiplicative.ofAdd t))) (lambdaSite.entry 0 1) =
      regularCharacterScalar (Real.log fixedProductLambda) t • lambdaSite.entry 0 1
  mu_eigen : ∀ (m : ModularSpectralResolution stages.algebra stages.vector) (t : ℝ),
    unitaryConj (star (m.group (Multiplicative.ofAdd t))) (muSite.entry 0 1) =
      regularCharacterScalar (Real.log fixedProductMu) t • muSite.entry 0 1

attribute [instance] TwoRatioProductModel.normedK TwoRatioProductModel.innerK
  TwoRatioProductModel.completeK TwoRatioProductModel.nontrivialK TwoRatioProductModel.separableK

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProductCentralizerSmallProjections
attribute [-instance] _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.normUltraproductNontrivial _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Small projections in the fixed product-state centralizer

The all-zero diagonal in a finite block of lambda sites is in the exact
state centralizer. Its trace is `(1 + lambda)⁻ⁿ`, hence tends to zero.
-/

namespace KadisonKastler

open Generator Generator.Tracial UltrapowerBridge Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {Ω : H}

namespace PointedMatrixSites

variable (S : PointedMatrixSites M Ω twoRatioSiteParameter)

theorem twoRatio_site_diagonal_mem_centralizer (i : TwoRatioSite) (a : Fin 2) :
    (S.site i).entry a a ∈ stateCentralizerVonNeumann (M := M) Ω := by
  refine ⟨?_,?_⟩
  · have hm := subset_generatedVonNeumannAlgebra _
      ((le_iSup (fun j => (S.site j).algebra) i) ((S.site i).entry_mem a a))
    exact Eq.mpr (congrArg (fun N : VonNeumannAlgebra H =>
      (S.site i).entry a a ∈ N) S.generates) hm
  · intro b hb
    apply mul_left_cancel₀ (a := (twoSiteWeight (twoRatioSiteParameter i) a : ℂ))
    · have hp : 0 < twoRatioSiteParameter i := by
        rcases i with n | n
        · exact fixedProductLambda_pos
        · exact fixedProductMu_pos
      have hw : 0 < twoSiteWeight (twoRatioSiteParameter i) a := by
        unfold twoSiteWeight
        split_ifs <;> positivity
      exact_mod_cast ne_of_gt hw
    · exact S.twoRatio_site_balance i a a b hb

theorem twoRatio_block_zero_mem_centralizer (l : List TwoRatioSite) :
    S.blockEntry l (matrixSiteBlockZero l) (matrixSiteBlockZero l) ∈
      stateCentralizerVonNeumann (M := M) Ω := by
  induction l with
  | nil => exact (stateCentralizerVonNeumann (M := M) Ω).one_mem
  | cons i l ih =>
    exact (stateCentralizerVonNeumann (M := M) Ω).mul_mem
      (S.twoRatio_site_diagonal_mem_centralizer i 0) ih

def centralizerBlockZero (l : List TwoRatioSite) (hl : l.Nodup) :
    AlgebraProjection (stateCentralizerVonNeumann (M := M) Ω) := by
  let E := S.finiteBlock l hl
  let z := matrixSiteBlockZero l
  refine ⟨⟨E.entry z z,S.twoRatio_block_zero_mem_centralizer l⟩,?_,?_⟩
  · exact Subtype.ext (E.diagonal_projection z).isIdempotentElem.eq
  · exact Subtype.ext (E.diagonal_projection z).isSelfAdjoint.star_eq

end PointedMatrixSites

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProductScalingWords
attribute [-instance] _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Finite product words as state-scaling partial isometries

All scale ratios here come from the actual two fixed site families.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {Ω : H}

namespace PointedMatrixSites

variable (S : PointedMatrixSites M Ω twoRatioSiteParameter)

include S

def blockScalingPartialIsometry (l : List TwoRatioSite) (hl : l.Nodup)
    (a b : MatrixSiteBlockIndex l) : PartialIsometry M := by
  let E := S.finiteBlock l hl
  let e (r c : MatrixSiteBlockIndex l) : Algebra M :=
    ⟨E.entry r c,S.finiteBlock_le l hl (E.entry_mem r c)⟩
  refine ⟨⟨e b b,?_,?_⟩,e a b,?_⟩
  · exact Subtype.ext (E.diagonal_projection b).isIdempotentElem.eq
  · exact Subtype.ext (E.diagonal_projection b).isSelfAdjoint.star_eq
  · apply Subtype.ext
    change star (E.entry a b)*E.entry a b=E.entry b b
    simp only [E.star_entry,E.mul_entry,↓reduceIte]

end PointedMatrixSites

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_StateCommutatorAlgebra
attribute [-instance] _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.CommonTracialPositionData.rightEquiv_transportEquiv _root_.OAI.KadisonKastler.StandardTracialPosition.diagonalRepresentation_vector _root_.OAI.KadisonKastler.algebraConstantField_coe _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.constantAlgebraUnitaryFamily_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.matrixClosureVectorTrace_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.minimalCyclicRetraction_compression _root_.OAI.KadisonKastler.normalCyclicEquiv_val _root_.OAI.KadisonKastler.normalCyclicHom_apply _root_.OAI.KadisonKastler.normalPairEquiv_coe _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.spatialTransportEquiv_vector _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply _root_.OAI.KadisonSimilarity.predualRestriction_apply _root_.OAI.KadisonSimilarity.tracialInclusionIsometry_vector _root_.OAI.NaimarkZFC.gns_apply_coe
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

@[simp] theorem vectorStateCommutator_apply (ξ : H) (a b : Algebra M) :
    vectorStateCommutator ξ a b=vectorFunctional ξ (a*b-b*a) := rfl

@[simp] theorem vectorStateCommutator_add (ξ : H) (a b : Algebra M) :
    vectorStateCommutator ξ (a+b)=vectorStateCommutator ξ a+vectorStateCommutator ξ b := by
  ext c
  simp only [vectorStateCommutator_apply,add_apply,add_mul,mul_add,
    map_sub,map_add]
  ring

@[simp] theorem vectorStateCommutator_smul (ξ : H) (c : ℂ) (a : Algebra M) :
    vectorStateCommutator ξ (c • a)=c • vectorStateCommutator ξ a := by
  ext b
  simp only [vectorStateCommutator_apply,smul_apply,smul_mul_assoc,mul_smul_comm,
    ← smul_sub,map_smul,smul_eq_mul]

@[simp] theorem vectorStateCommutator_zero (ξ : H) :
    vectorStateCommutator (M := M) ξ 0=0 := by
  ext a
  simp only [vectorStateCommutator_apply,zero_mul,mul_zero,sub_self,map_zero,zero_apply]

@[simp] theorem vectorStateCommutator_one (ξ : H) :
    vectorStateCommutator (M := M) ξ 1=0 := by
  ext a
  simp only [vectorStateCommutator_apply,one_mul,mul_one,sub_self,map_zero,zero_apply]

@[simp] theorem vectorStateCommutator_sub (ξ : H) (a b : Algebra M) :
    vectorStateCommutator ξ (a-b)=vectorStateCommutator ξ a-vectorStateCommutator ξ b := by
  ext c
  simp only [vectorStateCommutator_apply,sub_apply,sub_mul,mul_sub,map_sub]
  ring

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_StateCentralSequenceAlgebra
attribute [-instance] _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

def StateAsymptoticallyCentral (ξ : H) (x : BoundedSequence (Algebra M)) : Prop :=
  Tendsto (fun n => ‖vectorStateCommutator ξ (x n)‖) atTop (𝓝 0)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_StateBicentralizerTests
attribute [-instance] _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # State-sequence bicentralizers and their unitary tests

This formulation applies to a separating vector even when its algebra
orbit is a proper subspace of the represented Hilbert space.
-/

namespace KadisonKastler

open Filter
open scoped Topology BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

def stateBicentralizerMember (ξ : H) (a : Algebra M) : Prop :=
  ∀ x : BoundedSequence (Algebra M), StateAsymptoticallyCentral ξ x →
    ∀ η : H, Tendsto (fun n => (a*(x n)-(x n)*a).val η) atTop (𝓝 0)

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

theorem remoteTwoRatioDoubling_parameter (n : ℕ) (i : TwoRatioSite ⊕ TwoRatioSite) :
    twoRatioSiteParameter (remoteTwoRatioDoubling n i)=
      Sum.elim twoRatioSiteParameter twoRatioSiteParameter i := by
  rcases i with ((i | i) | (i | i)) <;> rfl

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SpatialStateCentrality
attribute [-instance] _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.spatialHilbert_separable _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
attribute [-simp] _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.matrixClosureVectorTrace_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.spatialTransportEquiv_vector _root_.OAI.KadisonKastler.tensorVectorSliceCP_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # State-central sequences in the first tensor leg

The product-state commutator is bounded by the original state commutator.
Thus bicentralizer membership of a first-leg operator implies membership
in the original algebra. Together with the independent-swap argument,
this is the needed product-leg specialization of AHHM, Proposition7.1.
-/

namespace KadisonKastler

open UnitalTomsWinter Generator Generator.Tracial Filter
open scoped Topology

noncomputable section

universe u

variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def spatialLeftAlgebraHom (M : VonNeumannAlgebra H) (D : VonNeumannAlgebra K) :
    Algebra M →⋆ₐ[ℂ] Algebra (spatialProductAlgebra M D) :=
  (spatialLeft.comp M.toStarSubalgebra.subtype).codRestrict _
    (fun a => spatialLeft_mem_product M D a.property)

@[simp] theorem spatialLeftAlgebraHom_val (M : VonNeumannAlgebra H)
    (D : VonNeumannAlgebra K) (a : Algebra M) :
    (spatialLeftAlgebraHom M D a).val=spatialLeft (K := K) a.val := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProjectionFamilySpaces
attribute [-instance] _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
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

theorem projectionFamilyRemainderSpace_invariant (S : Set (AlgebraProjection M))
    (a : Algebra M.commutant) {x : H} (hx : x ∈ projectionFamilyRemainderSpace S) :
    a.val x ∈ projectionFamilyRemainderSpace S := by
  rw [mem_projectionFamilyRemainderSpace] at hx ⊢
  intro p hp
  have hc := congrArg (fun T : H →L[ℂ] H => T x)
    (VonNeumannAlgebra.mem_commutant_iff.mp a.property p.val.val p.val.property)
  change p.val.val (a.val x)=a.val (p.val.val x) at hc
  rw [hc,hx p hp,map_zero]

theorem projectionFamilyRemainderProjection_mem (S : Set (AlgebraProjection M)) :
    (projectionFamilyRemainderSpace S).toSubmodule.starProjection ∈ M := by
  have h : (projectionFamilyRemainderSpace S).toSubmodule.starProjection ∈ M.commutant.commutant := by
    apply VonNeumannAlgebra.mem_commutant_iff.mpr
    intro a ha
    exact (starProjection_commutes_of_invariant (projectionFamilyRemainderSpace S).toSubmodule
      a (fun _ hx => projectionFamilyRemainderSpace_invariant S ⟨a,ha⟩ hx)
        (fun _ hx => projectionFamilyRemainderSpace_invariant S (star ⟨a,ha⟩) hx)).symm
  simpa only [M.commutant_commutant] using h

def projectionFamilyRemainder (S : Set (AlgebraProjection M)) : AlgebraProjection M :=
  ⟨⟨(projectionFamilyRemainderSpace S).toSubmodule.starProjection,
      projectionFamilyRemainderProjection_mem S⟩,
    ⟨Subtype.ext (Submodule.isIdempotentElem_starProjection _).eq,
      Subtype.ext (isSelfAdjoint_starProjection _).star_eq⟩⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProjectionFamilyAdmissible
attribute [-instance] _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Closed quantitative constraints on projection families -/

namespace KadisonKastler

open Generator.Tracial Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

def ProjectionFamilyAdmissible (J : H ≃ₗᵢ⋆[ℂ] H) (ξ η : H) (δ : ℝ)
    (S : Set (AlgebraProjection M)) : Prop :=
  (‖(1-modularQuadratic J (projectionFamilyRemainder S).val) ξ‖^2+
      ‖(1-modularQuadratic J (projectionFamilyRemainder S).val) η‖^2 ≤
    131072*‖(1-projectionFamilyPinching J S) η‖^2) ∧
  (‖(1-projectionFamilyPinching J S) ξ‖^2 ≤ δ*‖(1-projectionFamilyPinching J S) η‖^2)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProjectionFamilyMaximal
attribute [-instance] _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Maximal admissible orthogonal projection families

Chain unions retain the two quantitative inequalities by strong convergence
of the constructed kernel projections.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

def AdmissibleOrthogonalFamily (J : H ≃ₗᵢ⋆[ℂ] H) (ξ η : H) (δ : ℝ)
    (S : Set (AlgebraProjection M)) : Prop :=
  (∀ p ∈ S, p.val≠0) ∧ S.Pairwise (fun p q => p.val*q.val=0) ∧
    ProjectionFamilyAdmissible J ξ η δ S

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SpatialBicentralizer
attribute [-instance] _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Spatial transfer of faithful vector-state bicentralizers -/

namespace KadisonKastler

open Generator.Tracial Filter
open scoped Topology

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}

def FaithfulVectorBicentralizersScalar (M : VonNeumannAlgebra H) : Prop :=
  ∀ ξ : H, ‖ξ‖=1 → Function.Injective (algebraVectorMap M ξ) →
    ∀ a : Algebra M, stateBicentralizerMember ξ a → ∃ z : ℂ, a=z • 1

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TwoRatioProductConstruction
attribute [-instance] _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductNontrivial _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
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

def PointedMatrixProduct.toTwoRatioProductModel
    (P : PointedMatrixProduct.{u} twoRatioSiteParameter) : TwoRatioProductModel.{u} where
  K := P.K
  normedK := P.normedK
  innerK := P.innerK
  completeK := P.completeK
  nontrivialK := P.nontrivialK
  separableK := P.separableK
  stages := P.coordinates.twoRatioStages
  coordinates := P.coordinates.twoRatioStages_coordinates
  lambdaSite := P.coordinates.twoRatioStages_coordinates.site (Sum.inl 0)
  muSite := P.coordinates.twoRatioStages_coordinates.site (Sum.inr 0)
  lambda_mem := P.coordinates.twoRatioStages_coordinates.twoRatio_site_algebra_le _
  mu_mem := P.coordinates.twoRatioStages_coordinates.twoRatio_site_algebra_le _
  lambda_eigen := fun m t =>
    P.coordinates.twoRatioStages_coordinates.twoRatio_site_modular_star_eigen m (Sum.inl 0) t
  mu_eigen := fun m t =>
    P.coordinates.twoRatioStages_coordinates.twoRatio_site_modular_star_eigen m (Sum.inr 0) t

end

end KadisonKastler

end OAI
end


