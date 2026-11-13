-- Prove2me | Definitions.Def_Q260K007
-- name    : Q260K007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T04:34:34.628435+00:00
-- url     : https://prove2.me/theorems/8fa1903f-4dbf-48f4-b469-82495dd616d6
-- title:
--   Definitions bundle Q260K007 of the split of OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 414 declarations of OpenAI's Lean: 219 definitions, 10 instances and 185 theorems. The definitions and types are `OAI.KadisonKastler.conjugationFixedCone`, `OAI.KadisonKastler.constructedNormalizerAverageFamilyCStar`, `OAI.KadisonKastler.constructedNormalizerCorrectionCStar`, `OAI.KadisonKastler.constructedPairedAmplificationOperatorOrder`, `OAI.KadisonKastler.constructedPairedAmplificationSourceOrder`, `OAI.KadisonKastler.coreTraceReciprocal`, `OAI.KadisonKastler.coreTraceSymmetrySpace`, `OAI.KadisonKastler.cornerCompressionLinear`, `OAI.KadisonKastler.cornerFunctional`, `OAI.KadisonKastler.correctionProducts`, `OAI.KadisonKastler.cuntzCommutatorOperatorOrder`, `OAI.KadisonKastler.derivationExtensionFactorInstance1`, `OAI.KadisonKastler.descentOperatorOrder`, `OAI.KadisonKastler.descentValue`, `OAI.KadisonKastler.expectedBicentralizerRealInner`, `OAI.KadisonKastler.expectedOneBicentralizerRealInner`, `OAI.KadisonKastler.expectedRelativeRealInner`, `OAI.KadisonKastler.exponentialRemainder`, `OAI.KadisonKastler.finiteAlgebraOrbit`, `OAI.KadisonKastler.finiteBilinearProduct`, `OAI.KadisonKastler.finiteChainMeanValue`, `OAI.KadisonKastler.finiteChainUltrafilter`, `OAI.KadisonKastler.finiteCoordinateL2`, `OAI.KadisonKastler.finiteGroupAverage`, `OAI.KadisonKastler.finiteMatrixDifferential`, `OAI.KadisonKastler.finiteOperatorCoefficient`, `OAI.KadisonKastler.finiteOutwardProjection`, `OAI.KadisonKastler.finitePhaseSum`, `OAI.KadisonKastler.finitePinchingRealInner`, `OAI.KadisonKastler.finiteRMS`, `OAI.KadisonKastler.finiteReducingSpace`, `OAI.KadisonKastler.finiteSign`, `OAI.KadisonKastler.finiteSignLeftCovariance`, `OAI.KadisonKastler.finiteSignRightCovariance`, `OAI.KadisonKastler.finiteSignSum`, `OAI.KadisonKastler.finiteSubgroupFunctional`, `OAI.KadisonKastler.finiteThresholdProjection`, `OAI.KadisonKastler.firstCoordinateIsometry`, `OAI.KadisonKastler.flattenedGraphOrder`, `OAI.KadisonKastler.flattenedRowOrder` and 179 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `KadisonKastler_BalancedOrbitFamilies`, `KadisonKastler_BicentralizerScalarHulls`, `KadisonKastler_BoundaryErgodicReduction`, `KadisonKastler_ClosedExponentialGenerator`, `KadisonKastler_CommonRankFactorFibers`, `KadisonKastler_CommonRankOperatorFields`, `KadisonKastler_CompleteConjugation`, `KadisonKastler_CompleteCorrectionProducts`, `KadisonKastler_CompleteLinearOperations`, `KadisonKastler_CompletelyBounded`, `KadisonKastler_CompletelyPositive`, `KadisonKastler_ConcreteUCP`, `KadisonKastler_ConjugationComparison`, `KadisonKastler_ConstructedNormalizerAveraging`, `KadisonKastler_ConstructedNormalizerCorrection`, `KadisonKastler_ConstructedPairedAmplification`, `KadisonKastler_ContinuousPolarPath`, `KadisonKastler_CoreFrequencyUnitWindow`, `KadisonKastler_CoreHalfFrequencyWindow`, `KadisonKastler_CoreTraceMonomialReduction`, `KadisonKastler_CoreTraceReciprocal`, `KadisonKastler_CoreTraceSymmetry`, `KadisonKastler_CountableUnitaryAssembly`, `KadisonKastler_CuntzCommutator`, `KadisonKastler_CyclicStateCompression`, `KadisonKastler_DerivationExtensionFactor`, `KadisonKastler_DerivationStarReduction`, `KadisonKastler_ExpectedFromBicentralizer`, `KadisonKastler_ExpectedFromOneBicentralizer`, `KadisonKastler_ExpectedFromRelativeBicentralizers`, `KadisonKastler_ExponentialRemainder`, `KadisonKastler_FactorAnticommuting`, `KadisonKastler_FaithfulRepresentation`, `KadisonKastler_FiniteCochainDifferential`, `KadisonKastler_FiniteCoefficientFactorization`, `KadisonKastler_FiniteCoordinateL2`, `KadisonKastler_FiniteGroupAverage`, `KadisonKastler_FiniteHaagerupBounds`, `KadisonKastler_FiniteOperatorDuality`, `KadisonKastler_FinitePhases`, `KadisonKastler_FinitePinchingApproximation`, `KadisonKastler_FiniteSignFourthMoment`, `KadisonKastler_FiniteThresholdProjection`, `KadisonKastler_FlattenedGraphRow`, `KadisonKastler_FlattenedGraphVector`, `KadisonKastler_FourierIntegralL2`, `KadisonKastler_FrequencyActionAlignment`, `KadisonKastler_GaussianStateBounds`, `KadisonKastler_GaussianStateDerivative`, `KadisonKastler_GaussianStateKernel`, `KadisonKastler_GeneratedDerivationExtension`, `KadisonKastler_GraphClipping`, `KadisonKastler_GraphMomentBounds`, `KadisonKastler_HaagerupWeakLimits`, `KadisonKastler_HardyCauchyBoundary`, `KadisonKastler_HardyCauchyKernel`, `KadisonKastler_HardyCompression`, `KadisonKastler_HermitianAnnihilatorBall`, `KadisonKastler_HilbertBlockCompletion`, `KadisonKastler_HilbertColumns`, `KadisonKastler_HilbertContractionFactor`, `KadisonKastler_HilbertDefect`, `KadisonKastler_HilbertMatrixGeneration`, `KadisonKastler_HilbertRows`, `KadisonKastler_HilbertSignMoments`, `KadisonKastler_HilbertSumCorners`, `KadisonKastler_HilbertSumOperators`, `KadisonKastler_IncreasingFiniteMean`, `KadisonKastler_IncreasingMatrixPreparation`, `KadisonKastler_InfinitesimalExponentiation`, `KadisonKastler_IsometricCornerAlgebra`, `KadisonKastler_IsometricRestriction`, `KadisonKastler_IsometryComplement`, `KadisonKastler_MatrixActionCocycle`, `KadisonKastler_MatrixCommutantDistance`, `KadisonKastler_MatrixCornerAutomorphism`, `KadisonKastler_MatrixFixedCorners`, `KadisonKastler_MatrixNearCommutant`, `KadisonKastler_MatrixOrbitPairings`, `KadisonKastler_MatrixStagesInClosure`, `KadisonKastler_MatrixStateMoments`, `KadisonKastler_MatrixStrictContraction`, `KadisonKastler_MaximalClosedStarIdeal`, `KadisonKastler_ModularFixedVectors`, `KadisonKastler_ModularPositiveReal`, `KadisonKastler_NearlyFullCornerWitness`, `KadisonKastler_NormalizedMatrixAveraging`, `KadisonKastler_NormalizedPolarPath`, `KadisonKastler_NormalizedPositivePinching`, `KadisonKastler_NormalizedStageReference`, `KadisonKastler_NormalizerLogarithm`, `KadisonKastler_NormalizingRepresentations`, `KadisonKastler_OutwardSpectralCuts`, `KadisonKastler_PairedMatrixColumn`, `KadisonKastler_PairedMatrixProjection`, `KadisonKastler_PartialIsometryCorner`, `KadisonKastler_PartialSupportSpan`, `KadisonKastler_PartitionProjectionGap`, `KadisonKastler_PartitionSignAverage`, `KadisonKastler_PoissonCharacter`, `KadisonKastler_Polar`, `KadisonKastler_PositiveConeDualProjection`, `KadisonKastler_PositiveConeFaithfulApproximation`, `KadisonKastler_PositiveConeOrthogonality`, `KadisonKastler_PositiveConePowersStormer`, `KadisonKastler_PositiveConeProjectionSupport`, `KadisonKastler_PositiveConeQuadraticSupport`, `KadisonKastler_PositiveConeSelfDual`, `KadisonKastler_PositiveConeStateEstimate`, `KadisonKastler_PositiveCornerWitness`, `KadisonKastler_PositiveIsometryPullback`, `KadisonKastler_PositiveMatrixAveraging`, `KadisonKastler_PositiveOrbitContraction`, `KadisonKastler_PositiveOrbitDensity`, `KadisonKastler_PositiveReferenceCone`, `KadisonKastler_PositiveReferenceHaagerup`, `KadisonKastler_PositiveReferenceModular`, `KadisonKastler_PositiveVectorPinching`, `KadisonKastler_ProbabilityMatrixDistance`, `KadisonKastler_ProbabilityOperatorAlgebra`, `KadisonKastler_ProjectionCentralScalar`, `KadisonKastler_ProjectionCommutatorEnergy`, `KadisonKastler_ProjectionJordanMap`, `KadisonKastler_ProjectionMatrices`, `KadisonKastler_ProjectionPinchedState`, `KadisonKastler_ProjectionReflectionOrbit`, `KadisonKastler_QuotientUnitBall`, `KadisonKastler_RandomWalkShiftLaw`, `KadisonKastler_RandomizedPairing`, `KadisonKastler_RecoveryJointLaw`, `KadisonKastler_RectangularHilbert`, `KadisonKastler_RectangularOperator`, `KadisonKastler_RectangularWeakCompact`, `KadisonKastler_RegularCoreDensePeriods`, `KadisonKastler_RegularTensorGap`, `KadisonKastler_RelativeBicentralizerGap`, `KadisonKastler_RelativeMatrixExtension`, `KadisonKastler_RelativeMatrixPreparation`, `KadisonKastler_RelativeMatrixStateHomogeneity`, `KadisonKastler_RelativePositiveDecomposition`, `KadisonKastler_RelativePositivePinching`, `KadisonKastler_RelativePowersStormer`, `KadisonKastler_RelativeProjectionInsertion`, `KadisonKastler_RelativeRankMatrixState`, `KadisonKastler_RelativeUnitaryStateDefect`, `KadisonKastler_RowOperatorFactorization`, `KadisonKastler_RowRepresentationContraction`, `KadisonKastler_ScalarPacketMeasure`, `KadisonKastler_SelfAdjointApproximation`, `KadisonKastler_SeparableAlgebraPair`, `KadisonKastler_SeparableReducingSpace`, `KadisonKastler_ShortFrequencyScalar`, `KadisonKastler_SignedFunctionalCompression`, `KadisonKastler_SignedSquareThreshold`, `KadisonKastler_SmoothingHeightSequence`, `KadisonKastler_SpatialCompleteGap`, `KadisonKastler_SpatialMatrix`, `KadisonKastler_SpatialMatrixAmplification`, `KadisonKastler_SpatialMatrixImage`, `KadisonKastler_SpatialTensorDescent`, `KadisonKastler_SpatialTensorModulus`, `KadisonKastler_SpectralClipping`, `KadisonKastler_StrictPinchingRefinement`, `KadisonKastler_StrongCommutantTests`, `KadisonKastler_ThresholdCutIntegral`, `KadisonKastler_TomiyamaNormGeometry`, `KadisonKastler_TomiyamaPositive`, `KadisonKastler_TomiyamaProjection`, `KadisonKastler_TracialConjugationBound`, `KadisonKastler_TwoCornerStateNorm`, `KadisonKastler_TwoRatioScalingWords`, `KadisonKastler_TwoStateCornerEmbedding`, `KadisonKastler_TypeIIIConstantNorm`, `KadisonKastler_UCPDescent`, `KadisonKastler_UniformPinchingGap`, `KadisonKastler_UniformProjectionGap`, `KadisonKastler_UnitBallClosure`, `KadisonKastler_UnitaryBounds`, `KadisonKastler_UnitaryResidualGap`, `KadisonKastler_VaryingQuotient`, `KadisonKastler_VectorStateFourthMoment`, `KadisonKastler_WOTDistanceSeparation`, `KadisonKastler_WeakMatrixLimits`, `Naimark_Basic`, `TracialSplitting_Model`, `TracialSplitting_NuclearTransfer`, `TracialSplitting_SimpleIdeals`.
--
--   **Imports.** It imports the bundles `OAIQ075A017` and `OAIQ075A022` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q260K014`, `Q260K015` and `Q260K018`; the statements `OAI.KadisonKastler.FrequencySmoothing.norm_product_sub_one_le`, `OAI.KadisonKastler.constructed_complete_closeness_of_paired_factor`, `OAI.KadisonKastler.exists_finite_bimodular_covariance_families`, `OAI.KadisonKastler.exists_finite_polar_coefficients`, `OAI.KadisonKastler.exists_simple_spatial_derivation`, `OAI.KadisonKastler.factor_of_extreme_signed_derivation_extension`, `OAI.KadisonKastler.finiteOutwardProjection_gap_integrable`, `OAI.KadisonKastler.finiteOutwardProjection_integral_lower`, `OAI.KadisonKastler.finiteOutwardProjection_integral_mass`, `OAI.KadisonKastler.finiteOutwardProjection_integral_upper_sq`, `OAI.KadisonKastler.finiteOutwardProjection_mass_integrable`, `OAI.KadisonKastler.opNorm_le_of_finite_covariance_families` and `OAI.KadisonKastler.pure_restriction_commuting_factorization`; the proofs of `OAI.KadisonKastler.PreservesJordan.multiplicative_of_close_of_II1`, `OAI.KadisonKastler.commutator_mem_of_small_expUnitary_normalizes`, `OAI.KadisonKastler.exists_near_algebra_of_finite_orbit_bound`, `OAI.KadisonKastler.exists_simple_spatial_derivation`, `OAI.KadisonKastler.exists_unitary_boundary_intertwiner`, `OAI.KadisonKastler.finiteOutwardProjection_gap_integrable`, `OAI.KadisonKastler.finiteOutwardProjection_integral_lower`, `OAI.KadisonKastler.finiteOutwardProjection_integral_mass`, `OAI.KadisonKastler.finiteOutwardProjection_integral_upper_sq`, `OAI.KadisonKastler.finiteOutwardProjection_mass_integrable`, `OAI.KadisonKastler.map_star_square_of_map_unitary`, `OAI.KadisonKastler.pure_restriction_commuting_factorization`, `OAI.KadisonKastler.tomiyama_corner_supported` and `OAI.KadisonKastler.tomiyama_map_projection_mul`.
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
import Mathlib.Analysis.CStarAlgebra.SpecialFunctions.PosPart
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.CStarAlgebra.Unitization
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
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
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
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
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
import Mathlib.Topology.Instances.ENNReal.Lemmas
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
import Definitions.Def_OAIQ075A017
import Definitions.Def_OAIQ075A022

section
-- module Solutions.OAIQ075_KS.Compat
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
section OAIVecLookup
variable {α : Type _}
@[simp] theorem vecCons3_one (a b c : α) : (![a, b, c] : Fin 3 → α) 1 = b := rfl
@[simp] theorem vecCons3_two (a b c : α) : (![a, b, c] : Fin 3 → α) 2 = c := rfl
@[simp] theorem vecCons4_one (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 1 = b := rfl
@[simp] theorem vecCons4_two (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 2 = c := rfl
@[simp] theorem vecCons4_three (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 3 = d := rfl
end OAIVecLookup
section OAIVecTail
variable {α : Type _}
@[simp] theorem vecConsTail1_1 (x : α) (f : Fin 1 → α) : (Matrix.vecCons x f : Fin 2 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_1 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_2 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_1 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail3_2 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_3 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_1 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail4_2 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail4_3 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_4 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 4 = f 3 := rfl
end OAIVecTail
@[simp] theorem fin3_mk_0 (h : 0 < 3) : (⟨0, h⟩ : Fin 3) = 0 := rfl
@[simp] theorem fin3_mk_1 (h : 1 < 3) : (⟨1, h⟩ : Fin 3) = 1 := rfl
@[simp] theorem fin3_mk_2 (h : 2 < 3) : (⟨2, h⟩ : Fin 3) = 2 := rfl
@[simp] theorem fin4_mk_0 (h : 0 < 4) : (⟨0, h⟩ : Fin 4) = 0 := rfl
@[simp] theorem fin4_mk_1 (h : 1 < 4) : (⟨1, h⟩ : Fin 4) = 1 := rfl
@[simp] theorem fin4_mk_2 (h : 2 < 4) : (⟨2, h⟩ : Fin 4) = 2 := rfl
@[simp] theorem fin4_mk_3 (h : 3 < 4) : (⟨3, h⟩ : Fin 4) = 3 := rfl
@[simp] theorem fin5_mk_0 (h : 0 < 5) : (⟨0, h⟩ : Fin 5) = 0 := rfl
@[simp] theorem fin5_mk_1 (h : 1 < 5) : (⟨1, h⟩ : Fin 5) = 1 := rfl
@[simp] theorem fin5_mk_2 (h : 2 < 5) : (⟨2, h⟩ : Fin 5) = 2 := rfl
@[simp] theorem fin5_mk_3 (h : 3 < 5) : (⟨3, h⟩ : Fin 5) = 3 := rfl
@[simp] theorem fin5_mk_4 (h : 4 < 5) : (⟨4, h⟩ : Fin 5) = 4 := rfl
/-- `norm_num` cannot decide equalities of `Fin` literals here (oaiq-091). -/
@[simp] theorem fin3_lit_0_1 : ((0 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin3_lit_0_2 : ((0 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_1_0 : ((1 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_1_2 : ((1 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_2_0 : ((2 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_2_1 : ((2 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_0_1 : ((0 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_0_2 : ((0 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_0_3 : ((0 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_1_0 : ((1 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_1_2 : ((1 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_1_3 : ((1 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_2_0 : ((2 : Fin 4) = 0) ↔ False := by decide
/-- Mathlib d13f23b's `MeasurableSpace Circle` (Mathlib.MeasureTheory.Group.Circle): the subtype structure. A def,
turned on as a local instance in the modules that use the characters `𝐞`/`fourierChar`/`probChar` (q141). -/
@[reducible] def circleMeasurableSpace : MeasurableSpace Circle :=
  inferInstanceAs <| MeasurableSpace <| Subtype (· ∈ Submonoid.unitSphere ℂ)
/-- d13f23b's `BorelSpace Circle`, for `circleMeasurableSpace`. -/
theorem circleBorelSpace : @BorelSpace Circle _ circleMeasurableSpace :=
  inferInstanceAs <| BorelSpace <| Subtype (· ∈ Metric.sphere (0 : ℂ) 1)
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CompletelyBounded
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
/-- Entrywise application of a linear equivalence is an equivalence at
every rectangular matrix size. -/
def matrixLinearEquiv (F : A ≃ₗ[ℂ] B) (p q : ℕ) :
    CStarMatrix (Fin p) (Fin q) A ≃ₗ[ℂ] CStarMatrix (Fin p) (Fin q) B where
  toFun := CStarMatrix.mapₗ F.toLinearMap
  invFun := CStarMatrix.mapₗ F.symm.toLinearMap
  left_inv X := by ext i j; exact F.symm_apply_apply (X i j)
  right_inv X := by ext i j; exact F.apply_symm_apply (X i j)
  map_add' := map_add _
  map_smul' := map_smul _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FaithfulRepresentation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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

/-- A star homomorphism, viewed as a continuous linear map. -/
def starAlgHomToContinuousLinearMap (φ : A →⋆ₐ[ℂ] B) : A →L[ℂ] B :=
  φ.toAlgHom.toLinearMap.mkContinuous 1 (fun a => by
    change ‖φ a‖ ≤ 1 * ‖a‖
    simpa only [one_mul] using NonUnitalStarAlgHom.norm_apply_le φ a)

@[simp]
theorem starAlgHomToContinuousLinearMap_apply (φ : A →⋆ₐ[ℂ] B) (a : A) :
    starAlgHomToContinuousLinearMap φ a = φ a := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CompletelyPositive
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

/-- Every diagonal entry of a positive C⋆-matrix is positive. -/
theorem cstarMatrix_diagonal_nonneg {n : Type*} [Fintype n] [DecidableEq n]
    (M : CStarMatrix n n A) (hM : 0 ≤ M) (i : n) : 0 ≤ M i i := by
  rw [StarOrderedRing.nonneg_iff] at hM
  refine AddSubmonoid.closure_induction (fun X hX => ?_) (by simp)
    (fun X Y _ _ hX hY => ?_) hM
  · obtain ⟨X, rfl⟩ := hX
    simp only [CStarMatrix.mul_apply, CStarMatrix.star_eq_conjTranspose,
      CStarMatrix.conjTranspose_apply]
    exact Finset.sum_nonneg fun j _ => star_mul_self_nonneg _
  · exact add_nonneg hX hY

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_Polar
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# Polar unitaries close to the identity

We construct the polar factor of an invertible element using the positive
square root supplied by continuous functional calculus.
-/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

variable {A : Type*} [CStarAlgebra A]

section Ordered

variable [PartialOrder A] [StarOrderedRing A]

/-- The absolute value of an invertible element is invertible. -/
theorem isUnit_abs (t : Aˣ) : IsUnit (CFC.abs (t : A)) := by
  apply (CFC.isUnit_sqrt_iff _).mpr
  exact t.isUnit.star.mul t.isUnit

/-- Polar decomposition of an invertible element, with unitary polar factor. -/
theorem exists_unitary_mul_abs (t : Aˣ) :
    ∃ u : unitary A, (u : A) * CFC.abs (t : A) = (t : A) := by
  let s : Aˣ := (isUnit_abs t).unit
  have hs : (s : A) = CFC.abs (t : A) := (isUnit_abs t).unit_spec
  have hsstar : star s = s := Units.ext (by
    change star (s : A) = (s : A)
    rw [hs]
    exact (CFC.abs_nonneg _).star_eq)
  have hsinvstar : star ((s⁻¹ : Aˣ) : A) = ((s⁻¹ : Aˣ) : A) := by
    rw [← Units.coe_star, star_inv, hsstar]
  have hss : (s : A) * (s : A) = star (t : A) * (t : A) := by
    rw [hs, CFC.abs_mul_abs]
  let v : Aˣ := t * s⁻¹
  have hunit : (v : A) ∈ unitary A := by
    apply v.isUnit.mem_unitary_of_star_mul_self
    change star ((t : A) * (s⁻¹ : Aˣ)) * ((t : A) * (s⁻¹ : Aˣ)) = 1
    rw [star_mul, hsinvstar]
    calc
      ((s⁻¹ : Aˣ) : A) * star (t : A) * ((t : A) * (s⁻¹ : Aˣ)) =
          ((s⁻¹ : Aˣ) : A) * (star (t : A) * (t : A)) * (s⁻¹ : Aˣ) := by simp only [mul_assoc]
      _ = ((s⁻¹ : Aˣ) : A) * ((s : A) * (s : A)) * (s⁻¹ : Aˣ) := by rw [hss]
      _ = 1 := by simp only [← mul_assoc, Units.inv_mul, one_mul, Units.mul_inv]
  refine ⟨⟨v, hunit⟩, ?_⟩
  change (t : A) * (s⁻¹ : Aˣ) * CFC.abs (t : A) = (t : A)
  rw [← hs, mul_assoc, Units.inv_mul, mul_one]

end Ordered

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RectangularHilbert
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

local instance rectangularHilbertOperatorOrder : PartialOrder (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrder _
local instance rectangularHilbertOperatorStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FinitePhases
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# Finite phase randomization

Orthogonal scalar phases turn a coefficient column into a random vector
with exactly the same mean square. This is the finite Parseval identity
used for the randomized commutator coefficients in §3.
-/

namespace KadisonKastler

open Finset
open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {Ω W : Type*} [Fintype Ω] [Fintype W] [DecidableEq W]

def finitePhaseSum (χ : W → Ω → ℂ) (v : W → H) (t : Ω) : H :=
  ∑ w, χ w t • v w

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RectangularOperator
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Adjoint and product formulas for rectangular operator matrices -/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {l m n : Type*} [Fintype l] [Fintype m] [Fintype n]

local instance rectangularOperatorOrder : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
local instance rectangularOperatorStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProjectionMatrices
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# Matrices of orthogonal projections

The preservation-cut estimate uses an operator matrix whose nonzero
entries are projections, orthogonal within each row and each column.
Such a rectangular matrix is a contraction.
-/

namespace KadisonKastler

open Finset

noncomputable section

theorem isStarProjection_sum_orthogonal {A ι : Type*} [NonUnitalRing A] [StarRing A]
    (s : Finset ι) (P : ι → A) (hP : ∀ i ∈ s, IsStarProjection (P i))
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → P i * P j = 0) :
    IsStarProjection (∑ i ∈ s, P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [sum_insert hi]
    apply (hP i (by simp)).add
      (ih (by intro j hj; exact hP j (by simp [hj]))
        (by intro j hj k hk hjk; exact horth j (by simp [hj]) k (by simp [hk]) hjk))
    rw [mul_sum]
    apply sum_eq_zero
    intro j hj
    exact horth i (by simp) j (by simp [hj]) (by aesop)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_HilbertRows
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

local instance hilbertRowOrder : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
local instance hilbertRowStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_HilbertColumns
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Annihilation columns and their products -/

namespace KadisonKastler

open Finset

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {I J : Type*} [Fintype I] [Fintype J]

local instance hilbertColumnOrder : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
local instance hilbertColumnStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _

def operatorColumn (C : I → H →L[ℂ] H) : CStarMatrix I Unit (H →L[ℂ] H) :=
  CStarMatrix.ofMatrix (fun i _ => C i)

omit [CompleteSpace H] [Fintype I] in
@[simp]
theorem operatorColumn_apply (C : I → H →L[ℂ] H) (i : I) (u : Unit) :
    operatorColumn C i u = C i := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SpectralClipping
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# Norm clipping with preserved support and quotient image

The cutoff multiplies an element on the right by a continuous function of
its absolute value. Both the clipped part and the discarded part have
star squares bounded by the original star square.
-/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A scalar functional-calculus identity for any continuous right multiplier. -/
theorem star_mul_cfc_abs (x : A) (f : ℝ → ℝ) (hf : Continuous f) :
    star (x * cfc f (CFC.abs x)) * (x * cfc f (CFC.abs x)) =
      cfc (fun t => (t * f t) ^ 2) (CFC.abs x) := by
  have ha : IsSelfAdjoint (CFC.abs x) := (CFC.abs_nonneg x).isSelfAdjoint
  have hfstar : star (cfc f (CFC.abs x)) = cfc f (CFC.abs x) :=
    (cfc_predicate f (CFC.abs x)).star_eq
  calc
    _ = cfc f (CFC.abs x) * (star x * x) * cfc f (CFC.abs x) := by
      rw [star_mul, hfstar]
      simp only [mul_assoc]
    _ = cfc f (CFC.abs x) * cfc (fun t : ℝ => t ^ 2) (CFC.abs x) *
        cfc f (CFC.abs x) := by
      rw [cfc_pow_id (R := ℝ) _ 2 ha, pow_two, CFC.abs_mul_abs]
    _ = cfc (fun t => f t * t ^ 2 * f t) (CFC.abs x) := by
      rw [← cfc_mul f (fun t : ℝ => t ^ 2) _ hf.continuousOn (by fun_prop),
        ← cfc_mul (fun t => f t * t ^ 2) f _ (by fun_prop) hf.continuousOn]
    _ = _ := by congr 1; funext t; ring

section Hom

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

theorem starAlgHom_map_abs (π : A →⋆ₐ[ℂ] B) (x : A) :
    π (CFC.abs x) = CFC.abs (π x) := by
  simp only [CFC.abs]
  rw [CFC.sqrt_eq_real_sqrt _ (star_mul_self_nonneg x),
    CFC.sqrt_eq_real_sqrt _ (star_mul_self_nonneg (π x)), cfcₙ_eq_cfc, cfcₙ_eq_cfc]
  rw [π.map_cfc Real.sqrt (star x * x) (by fun_prop) (by fun_prop)
    (star_mul_self_nonneg x).isSelfAdjoint (by
      simp only [map_mul, map_star]
      exact (star_mul_self_nonneg (π x)).isSelfAdjoint)]
  simp only [map_mul, map_star]

end Hom

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteSignFourthMoment
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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

/-- The coordinate signs on the uniform finite Boolean probability space. -/
def finiteSign (ε : ι → Bool) (i : ι) : ℝ := if ε i then -1 else 1

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem finiteSign_sq (ε : ι → Bool) (i : ι) : finiteSign ε i ^ 2 = 1 := by
  cases h : ε i <;> simp [finiteSign, h]

variable {B : Type*} [CStarAlgebra B]

/-- The unnormalized random sum; normalization is introduced after expansion. -/
def finiteSignSum (a : ι → B) (ε : ι → Bool) : B := ∑ i, finiteSign ε i • a i

/-- The usual variance-one normalization of the finite sign sum. -/
def normalizedFiniteSignSum (a : ι → B) (ε : ι → Bool) : B :=
  (Real.sqrt (Fintype.card ι : ℝ))⁻¹ • finiteSignSum a ε

/-- Right covariance of the coefficients. -/
def finiteSignRightCovariance (a : ι → B) : B :=
  (Fintype.card ι : ℝ)⁻¹ • ∑ i, star (a i) * a i

/-- Left covariance of the coefficients. -/
def finiteSignLeftCovariance (a : ι → B) : B :=
  (Fintype.card ι : ℝ)⁻¹ • ∑ i, a i * star (a i)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BalancedOrbitFamilies
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Balanced two-sided unitary orbit families

Independent equal-weight left and right conjugation averages control the
respective covariances of the Cartesian-product orbit family. Its common
pairing is unchanged by an operator commuting with both unitary actions.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {A I J : Type*} [CStarAlgebra A]
  [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]

/-- The finite two-sided orbit, indexed by independent choices. -/
def twoSidedOrbit (d : I → unitary A) (e : J → unitary A) (a : A) (ij : I × J) : A :=
  (d ij.1 : A) * a * (e ij.2 : A)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RandomizedPairing
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# Extracting the scalar commutator from randomized rows

Finite Cauchy–Schwarz bounds the two row errors without a factor for the
number of random choices. Together with the scalar commutator estimate
this gives the constant 141 in the amplification argument.
-/

namespace KadisonKastler

open Finset
open scoped BigOperators Topology

noncomputable section

variable {Ω H : Type*} [Fintype Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def finiteRMS (v : Ω → H) : ℝ := Real.sqrt (𝔼 w, ‖v w‖ ^ 2)

def meanPairing (x : Ω → H →L[ℂ] H) (v w : Ω → H) : ℂ :=
  𝔼 i, inner ℂ (x i (v i)) (w i)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_VaryingQuotient
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Trace-preserving embeddings of varying tracial products

Coordinate embeddings descend to the represented tracial quotients.
Faithfulness and the trace ultralimit formula supply the kernel inclusion;
no additional ultraproduct embedding principle is assumed.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

section Descent

variable {A B C : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]
variable (f : A →⋆ₐ[ℂ] B) (hf : Function.Surjective f) (g : A →⋆ₐ[ℂ] C)
variable (hker : ∀ x, f x = 0 → g x = 0)

include hker

theorem descent_eq {x y : A} (hxy : f x = f y) : g x = g y := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply hker
  rw [map_sub, hxy, sub_self]

def descentValue (x : B) : C := g (Classical.choose (hf x))

theorem descentValue_map (x : A) : descentValue f hf g (f x) = g x := by
  apply descent_eq f g hker
  exact Classical.choose_spec (hf (f x))

/-- Descent through a surjective star homomorphism with smaller kernel. -/
def starAlgHomDescend : B →⋆ₐ[ℂ] C where
  toFun := descentValue f hf g
  map_one' := by
    rw [← map_one f, descentValue_map f hf g hker, map_one]
  map_mul' x y := by
    obtain ⟨a, rfl⟩ := hf x
    obtain ⟨b, rfl⟩ := hf y
    rw [← map_mul, descentValue_map f hf g hker, map_mul,
      descentValue_map f hf g hker, descentValue_map f hf g hker]
  map_zero' := by
    rw [← map_zero f, descentValue_map f hf g hker, map_zero]
  map_add' x y := by
    obtain ⟨a, rfl⟩ := hf x
    obtain ⟨b, rfl⟩ := hf y
    rw [← map_add, descentValue_map f hf g hker, map_add,
      descentValue_map f hf g hker, descentValue_map f hf g hker]
  commutes' z := by
    calc
      descentValue f hf g (algebraMap ℂ B z) =
          descentValue f hf g (f (algebraMap ℂ A z)) :=
        congrArg (descentValue f hf g) (f.commutes z).symm
      _ = g (algebraMap ℂ A z) := descentValue_map f hf g hker _
      _ = algebraMap ℂ C z := g.commutes z
  map_star' x := by
    obtain ⟨a, rfl⟩ := hf x
    rw [← map_star, descentValue_map f hf g hker, map_star,
      descentValue_map f hf g hker]

@[simp]
theorem starAlgHomDescend_apply_map (x : A) :
    starAlgHomDescend f hf g hker (f x) = g x := descentValue_map f hf g hker x

end Descent

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_UnitaryBounds
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# Extending estimates from unitaries

The final step of the uniform amplification argument bounds a linear
commutator map on every contraction from its bound on unitaries.  This
uses the four-unitary decomposition already proved in Mathlib.
-/

namespace KadisonKastler

variable {A B : Type*} [CStarAlgebra A] [NormedAddCommGroup B] [NormedSpace ℂ B]

/-- A uniform estimate on unitaries extends to the whole algebra with a
factor of two. Continuity need not be assumed for this pointwise statement. -/
theorem norm_le_twice_unitary_bound (T : A →ₗ[ℂ] B) {C : ℝ}
    (hT : ∀ u : unitary A, ‖T (u : A)‖ ≤ C) (x : A) :
    ‖T x‖ ≤ 2 * C * ‖x‖ := by
  obtain ⟨u, c, hx, hc⟩ := CStarAlgebra.exists_sum_four_unitary x
  calc
    ‖T x‖ = ‖∑ i : Fin 4, c i • T (u i : A)‖ := by rw [hx, map_sum]; simp only [map_smul]
    _ ≤ ∑ i : Fin 4, ‖c i • T (u i : A)‖ :=
      norm_sum_le _ _
    _ = ∑ i : Fin 4, ‖c i‖ * ‖T (u i : A)‖ := by simp only [norm_smul]
    _ ≤ ∑ _i : Fin 4, (‖x‖ / 2) * C := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul (hc i) (hT (u i)) (norm_nonneg _) (by positivity)
    _ = 2 * C * ‖x‖ := by simp <;> ring

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TracialConjugationBound
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Comparing tracial conjugations in common position

The two conjugations are supplied as actual conjugate-linear isometries.
Common right-action commutation remains an explicit structural premise;
the distance estimate itself follows from unit-ball approximation and
the proved finite bimodular test.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The complex-linear comparison operator of two conjugations. -/
def tracialConjugationDefect (J₁ J₂ : H ≃ₗᵢ⋆[ℂ] H) : H →L[ℂ] H :=
  (J₂ : H →L⋆[ℂ] H).comp (J₁ : H →L⋆[ℂ] H) - 1

omit [CompleteSpace H] in
@[simp]
theorem tracialConjugationDefect_apply (J₁ J₂ : H ≃ₗᵢ⋆[ℂ] H) (ξ : H) :
    tracialConjugationDefect J₁ J₂ ξ = J₂ (J₁ ξ) - ξ := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_HilbertSignMoments
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Hilbert-space second and fourth moments of independent signs

The fourth-moment constant is three. Real Hilbert spaces suffice for the
proof and complex Hilbert spaces are covered by restriction of scalars.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {ι V : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The Hilbert-space sum of independent signs. -/
def hilbertSignSum (a : ι → V) (ε : ι → Bool) : V :=
  ∑ i, finiteSign ε i • a i

/-- The variance-one normalized Hilbert-space sign sum. -/
def normalizedHilbertSignSum (a : ι → V) (ε : ι → Bool) : V :=
  (Real.sqrt (Fintype.card ι : ℝ))⁻¹ • hilbertSignSum a ε

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixStateMoments
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Mixed vector-state moments of finite matrix orbits

These are the two independent-copy pairings used in graph flattening.
The finite signed-permutation averages are actual matrix averages, and
only the common vector-state centralizer identity is used. In particular
none of the state calculations presupposes a tracial ambient state.
-/

namespace KadisonKastler

open Filter
open scoped Topology BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The ambient vector functional, without an algebra-membership wrapper. -/
def operatorVectorState (Ω : H) : (H →L[ℂ] H) →ₗ[ℂ] ℂ where
  toFun x := inner ℂ Ω (x Ω)
  map_add' _ _ := inner_add_right _ _ _
  map_smul' _ _ := inner_smul_right _ _ _

omit [CompleteSpace H] in
@[simp] theorem operatorVectorState_apply (Ω : H) (x : H →L[ℂ] H) :
    operatorVectorState Ω x = inner ℂ Ω (x Ω) := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_VectorStateFourthMoment
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Nontracial fourth moments of independent signs

The three-pairing sign identity holds for the actual vector functional.
The crossed pairing is bounded after summing the two orders of its
indices. This avoids applying a tracial fourth-moment theorem to the
nontracial vector state in the modular graph argument.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Real part of the ambient vector state, as a real-linear functional. -/
def realVectorState (Ω : H) : (H →L[ℂ] H) →ₗ[ℝ] ℝ :=
  Complex.reLm.comp ((operatorVectorState Ω).restrictScalars ℝ)

omit [CompleteSpace H] [Fintype ι] [DecidableEq ι] in
@[simp] theorem realVectorState_apply (Ω : H) (x : H →L[ℂ] H) :
    realVectorState Ω x = (inner ℂ Ω (x Ω)).re := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixOrbitPairings
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Fourth-moment pairings of actual two-sided matrix orbits

The sampled elements are `u*x*v*`. Their first and third sign-pairing
terms reduce exactly to the independent matrix averages in
`MatrixStateMoments`; the reductions use the vector-state centralizer,
not a trace identity for arbitrary elements.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- One actual sample of the two-sided unitary orbit. -/
def unitaryDoubleOrbit (x : H →L[ℂ] H)
    (u v : unitary (H →L[ℂ] H)) : H →L[ℂ] H :=
  (u : H →L[ℂ] H) * x * star (v : H →L[ℂ] H)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_GraphMomentBounds
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Expected costs before graph clipping

The cost uses the actual vector state and the two fourth powers. The
finite-sample estimate retains the diagonal correction, so increasing
the number of samples removes the diagonal cost. The final scalar lemma
chooses a stage and a sample size from convergence of the mixed moments.
-/

namespace KadisonKastler

open Filter
open scoped Topology BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

local instance graphMomentRealInner : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

/-- The nonnegative cost appearing before graph-vector clipping. -/
def graphMomentCost (Ω : H) (k : ℝ) (x : H →L[ℂ] H) : ℝ :=
  realVectorState Ω (star x * x) + k * realVectorState Ω (x * star x) +
    realVectorState Ω ((star x * x) ^ 2) + k * realVectorState Ω ((x * star x) ^ 2)

variable {I G : Type*} [Fintype I] [DecidableEq I] [Fintype G] [Nonempty G]

/-- The four scalar statistics needed for the expected graph cost. -/
def orbitSecondMoment (Ω : H) (k : ℝ) (a : G → H →L[ℂ] H) : ℝ :=
  (𝔼 g, realVectorState Ω (star (a g) * a g)) +
    k * (𝔼 g, realVectorState Ω (a g * star (a g)))

def orbitDiagonalMoment (Ω : H) (a : G → H →L[ℂ] H) : ℝ :=
  𝔼 g, realVectorState Ω ((star (a g) * a g) ^ 2)

def orbitFirstPairMoment (Ω : H) (a : G → H →L[ℂ] H) : ℝ :=
  𝔼 g, 𝔼 h, realVectorState Ω ((star (a g) * a g) * (star (a h) * a h))

def orbitThirdPairMoment (Ω : H) (a : G → H →L[ℂ] H) : ℝ :=
  𝔼 g, 𝔼 h, realVectorState Ω ((star (a g) * a h) * (star (a h) * a g))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BoundaryErgodicReduction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Removing the boundary variables by double ergodicity

The diagonal comparison gives the vector field `L* a Ω`.  Its covariance
is derived from the product intertwiner and the tracial right action.
Double ergodicity is used only for this actual bounded measurable field.
-/

namespace KadisonKastler

universe uG uD uH

open MeasureTheory Filter

noncomputable section

section Operators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The scalar phase supplied by the invariant vector defines a unitary
scalar operator. -/
def scalarUnitaryOfNormOne (z : ℂ) (hz : ‖z‖ = 1) : unitary (H →L[ℂ] H) :=
  ⟨z • 1, by
    have hzz : star z * z = 1 := by
      rw [Complex.star_def, Complex.conj_mul', hz]
      norm_num
    have hzz' : z * star z = 1 := by rw [mul_comm, hzz]
    constructor <;> simp only [star_smul, star_one, smul_mul_assoc, mul_smul_comm,
      one_mul, smul_smul, hzz, hzz', one_smul]⟩

end Operators

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FactorAnticommuting
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.MatrixUnitSystem.concrete_finiteDimensional _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Anticommuting unitaries in finite factors

The two Pauli matrices in a unital system of two-by-two matrix units give
selfadjoint anticommuting unitaries. Every II₁ factor contains such a system,
so the quantitative Jordan orientation test applies without an additional
assumption on the source factor.
-/

namespace KadisonKastler

noncomputable section

section MatrixUnits

variable {A : Type*} [Ring A] [StarRing A] [_root_.Algebra ℂ A]
  (E : Generator.MatrixUnitSystem (Fin 2) A)

/-- The diagonal Pauli matrix in the given matrix units. -/
def matrixUnitsPauliZ : A := E.entry 0 0 - E.entry 1 1

/-- The off-diagonal Pauli matrix in the given matrix units. -/
def matrixUnitsPauliX : A := E.entry 0 1 + E.entry 1 0

theorem matrixUnitsPauliZ_star : star (matrixUnitsPauliZ E) = matrixUnitsPauliZ E := by
  simp only [matrixUnitsPauliZ, star_sub, E.star_entry]

theorem matrixUnitsPauliX_star : star (matrixUnitsPauliX E) = matrixUnitsPauliX E := by
  simp only [matrixUnitsPauliX, star_add, E.star_entry, add_comm]

theorem matrixUnitsPauliZ_sq : matrixUnitsPauliZ E * matrixUnitsPauliZ E = 1 := by
  have ht : E.entry 0 0 + E.entry 1 1 = 1 := by
    simpa only [Fin.sum_univ_two] using E.total
  simpa [matrixUnitsPauliZ, sub_mul, mul_sub, E.mul_entry] using ht

theorem matrixUnitsPauliX_sq : matrixUnitsPauliX E * matrixUnitsPauliX E = 1 := by
  have ht : E.entry 0 0 + E.entry 1 1 = 1 := by
    simpa only [Fin.sum_univ_two] using E.total
  simpa [matrixUnitsPauliX, add_mul, mul_add, E.mul_entry, add_comm] using ht

/-- The diagonal Pauli unitary. -/
def matrixUnitsPauliZUnitary : unitary A :=
  ⟨matrixUnitsPauliZ E, by
    constructor <;> rw [matrixUnitsPauliZ_star, matrixUnitsPauliZ_sq]⟩

/-- The off-diagonal Pauli unitary. -/
def matrixUnitsPauliXUnitary : unitary A :=
  ⟨matrixUnitsPauliX E, by
    constructor <;> rw [matrixUnitsPauliX_star, matrixUnitsPauliX_sq]⟩

end MatrixUnits

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProjectionJordanMap
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Projection preservation from unitary preservation

Two scalar phases on a projection determine both its adjoint and its
square. Thus a unital complex-linear map preserving unitaries preserves
projections and orthogonal projection products, without an analytic
expansion of the exponential.
-/

namespace KadisonKastler

noncomputable section

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

/-- Put one unit-modulus scalar on a projection and one on its complement. -/
def projectionPhaseUnitary (p : A) (hp : IsStarProjection p)
    (z : ℂ) (hz : star z * z = 1) : unitary A :=
  ⟨1 - p + z • p, by
    have hz' : z * star z = 1 := by rwa [mul_comm]
    constructor
    · simp only [star_add, star_sub, star_one, star_smul, hp.isSelfAdjoint.star_eq,
        add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul,
        hp.one_sub.isIdempotentElem.eq, hp.mul_one_sub_self,
        hp.one_sub_mul_self, hp.isIdempotentElem.eq, hz', smul_zero,
        one_smul, add_zero, zero_add, sub_add_cancel]
    · simp only [star_add, star_sub, star_one, star_smul, hp.isSelfAdjoint.star_eq,
        add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul,
        hp.one_sub.isIdempotentElem.eq, hp.mul_one_sub_self,
        hp.one_sub_mul_self, hp.isIdempotentElem.eq, hz, smul_zero,
        one_smul, add_zero, zero_add, sub_add_cancel]⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RecoveryJointLaw
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Equality of the actual recovery expression for free pairs

Continuous clipping stays in the closed algebra generated by the
projection and the Haar unitary. The finite normal-word trace law therefore
applies to the concrete recovery contraction, without a spectral premise.
-/

namespace KadisonKastler

noncomputable section

universe u v

variable {B : Type u} [CStarAlgebra B]

local instance recoveryJointLawOrder : PartialOrder B := CStarAlgebra.spectralOrder B
local instance recoveryJointLawStarOrder : StarOrderedRing B :=
  CStarAlgebra.spectralOrderedRing B

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_GraphClipping
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Spectral clipping of a rescaled graph vector

The positive vector state can be applied to the two C*-order tail
bounds. Adjoint compatibility gives the same cutoff on both graph
coordinates. No traciality of the vector state is used.
-/

namespace KadisonKastler

noncomputable section

open scoped CStarAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

local instance graphClippingOrder : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
local instance graphClippingStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FlattenedGraphVector
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A bounded operator retaining the rescaled graph defect

The defining graph vector is normalized, averaged over the actual
finite matrix orbits, sampled with independent signs, and spectrally
clipped. All bounds concern the same resulting algebra element.
-/

namespace KadisonKastler

open scoped BigOperators CStarAlgebra

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

local instance flattenedGraphOrder : PartialOrder (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrder _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FlattenedGraphRow
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A bounded replicated row retaining the graph signal

A single cutoff of the row square preserves algebra membership and loses
at most one thirty-second of the graph signal in normalized mean square.
The cutoff and the row norm are independent of the row length.
-/

namespace KadisonKastler

open scoped BigOperators CStarAlgebra

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

local instance flattenedRowOrder : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CountableUnitaryAssembly
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Assembling the dimension strata by a Hilbert direct sum -/

namespace KadisonKastler

noncomputable section

variable {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)]
  [∀ n, InnerProductSpace ℂ (E n)] [∀ n, CompleteSpace (E n)]

def l2FiberUnitaryApply (U : ∀ n, unitary (E n →L[ℂ] E n)) (f : lp E 2) : lp E 2 :=
  ⟨fun n => (U n : E n →L[ℂ] E n) (f n),
    (lp.memℓp f).mono' (fun n => (Unitary.norm_map (U n) (f n)).le)⟩

@[simp] theorem l2FiberUnitaryApply_apply (U : ∀ n, unitary (E n →L[ℂ] E n))
    (f : lp E 2) (n : ℕ) :
    l2FiberUnitaryApply U f n = (U n : E n →L[ℂ] E n) (f n) := rfl

theorem norm_l2FiberUnitaryApply (U : ∀ n, unitary (E n →L[ℂ] E n)) (f : lp E 2) :
    ‖l2FiberUnitaryApply U f‖ = ‖f‖ := by
  apply le_antisymm
  · exact lp.norm_mono (by norm_num) fun n => (Unitary.norm_map (U n) (f n)).le
  · exact lp.norm_mono (by norm_num) fun n => (Unitary.norm_map (U n) (f n)).ge

def l2FiberUnitaryEquiv (U : ∀ n, unitary (E n →L[ℂ] E n)) : lp E 2 ≃ₗᵢ[ℂ] lp E 2 where
  toFun := l2FiberUnitaryApply U
  invFun := l2FiberUnitaryApply (fun n => star (U n))
  map_add' f g := by
    apply lp.ext
    funext n
    simp only [l2FiberUnitaryApply_apply, lp.coeFn_add, Pi.add_apply, map_add]
  map_smul' c f := by
    apply lp.ext
    funext n
    simp only [l2FiberUnitaryApply_apply, lp.coeFn_smul, Pi.smul_apply, map_smul,
      RingHom.id_apply]
  norm_map' := norm_l2FiberUnitaryApply U
  left_inv f := by
    apply lp.ext
    funext n
    exact congrArg (fun T : E n →L[ℂ] E n => T (f n)) (U n).property.1
  right_inv f := by
    apply lp.ext
    funext n
    exact congrArg (fun T : E n →L[ℂ] E n => T (f n)) (U n).property.2

def l2FiberUnitary (U : ∀ n, unitary (E n →L[ℂ] E n)) : unitary (lp E 2 →L[ℂ] lp E 2) :=
  Unitary.linearIsometryEquiv.symm (l2FiberUnitaryEquiv U)

@[simp] theorem l2FiberUnitary_apply (U : ∀ n, unitary (E n →L[ℂ] E n))
    (f : lp E 2) (n : ℕ) :
    ((l2FiberUnitary U : lp E 2 →L[ℂ] lp E 2) f) n = (U n : E n →L[ℂ] E n) (f n) := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_StrongCommutantTests
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Countable strong-operator tests for commutation

On a uniformly bounded set of operators, convergence on a countable dense
set of vectors implies convergence on every vector. A countable dense set
of coordinate sequences therefore supplies all commutant tests.
-/

namespace KadisonKastler

open Filter TopologicalSpace
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- Uniform contraction bounds extend pointwise convergence from a dense
sequence to every vector. -/
theorem tendsto_apply_of_dense_contractions (v : ℕ → H) (hv : DenseRange v)
    (A : ℕ → H →L[ℂ] H) (B : H →L[ℂ] H)
    (hA : ∀ n, ‖A n‖ ≤ 1) (hB : ‖B‖ ≤ 1)
    (h : ∀ j, Tendsto (fun n => A n (v j)) atTop (𝓝 (B (v j)))) (x : H) :
    Tendsto (fun n => A n x) atTop (𝓝 (B x)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨j, hj⟩ := hv.exists_dist_lt x (by positivity : 0 < ε / 4)
  have hA' (n : ℕ) (y : H) : ‖A n y‖ ≤ ‖y‖ := by
    apply ((A n).le_opNorm y).trans
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (hA n) (norm_nonneg y)
  have hB' (y : H) : ‖B y‖ ≤ ‖y‖ := by
    apply (B.le_opNorm y).trans
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hB (norm_nonneg y)
  filter_upwards [(Metric.tendsto_nhds.mp (h j)) (ε / 2) (by positivity)] with n hn
  have ha : dist (A n x) (A n (v j)) ≤ dist x (v j) := by
    simpa only [dist_eq_norm, map_sub] using hA' n (x - v j)
  have hb : dist (B (v j)) (B x) ≤ dist x (v j) := by
    simpa only [dist_eq_norm, map_sub, norm_sub_rev] using hB' (v j - x)
  have ht := (dist_triangle (A n x) (A n (v j)) (B x)).trans
    (add_le_add le_rfl (dist_triangle (A n (v j)) (B (v j)) (B x)))
  linarith

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_UnitBallClosure
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Unit balls in norm closures of complex linear subspaces

Radial contraction keeps approximants in their original subspace. It
proves the norm-density statement needed for the separable test algebras.
-/

namespace KadisonKastler

noncomputable section

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B]

def unitBallClip (x : B) : B := (((max 1 ‖x‖)⁻¹ : ℝ) : ℂ) • x

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_QuotientUnitBall
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Closed star-homomorphism ranges and contractive lifts

The closed-range assertion uses the actual C-star quotient by the kernel.
Clipping a preimage then gives an exact contraction lift, including at the
boundary of the closed unit ball. No faithfulness assumption is needed.
-/

namespace KadisonKastler

noncomputable section

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

local instance quotientUnitBallOrder : PartialOrder A := CStarAlgebra.spectralOrder A
local instance quotientUnitBallStarOrder : StarOrderedRing A :=
  CStarAlgebra.spectralOrderedRing A

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PairedMatrixProjection
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The projection associated with two commuting matrix actions

This is the finite-matrix formula for Haagerup's central-vector projection:
the normalized sum of matching left and conjugate-right matrix units.
-/

namespace KadisonKastler

open Generator
open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  (E F : MatrixUnitSystem ι (H →L[ℂ] H))

def pairedMatrixProjection : H →L[ℂ] H :=
  (Fintype.card ι : ℂ)⁻¹ • ∑ i, ∑ j, E.entry i j * F.entry i j

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ThresholdCutIntegral
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Averaging finite spectral threshold cuts

Two spectral values are separated by a threshold on an interval of
length equal to their distance. Finite weighted sums give the exact
average cut energy and its Cauchy--Schwarz bound.
-/

namespace KadisonKastler

open MeasureTheory
open scoped BigOperators

noncomputable section

def thresholdDifference (x y t : ℝ) : ℝ :=
  (if t < x then 1 else 0) - (if t < y then 1 else 0)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteThresholdProjection
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Projection-valued threshold cuts of finite spectral sums -/

namespace KadisonKastler

open Finset MeasureTheory
open scoped BigOperators

noncomputable section

variable {H ι κ : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype ι] [Fintype κ]

def finiteThresholdProjection (P : ι → H →L[ℂ] H) (c : ι → ℝ) (t : ℝ) : H →L[ℂ] H :=
  ∑ i, ((if t < c i then 1 else 0 : ℝ) : ℂ) • P i

theorem finiteThresholdProjection_isProjection
    (P : ι → H →L[ℂ] H) (hP : ∀ i, IsStarProjection (P i))
    (ho : ∀ i j, i ≠ j → P i * P j = 0) (c : ι → ℝ) (t : ℝ) :
    IsStarProjection (finiteThresholdProjection P c t) := by
  classical
  have he : finiteThresholdProjection P c t = ∑ i ∈ univ.filter (fun i => t < c i), P i := by
    simp only [finiteThresholdProjection,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : t < c i <;> simp [hi]
  rw [he]
  exact isStarProjection_sum_orthogonal _ P (fun i _ => hP i) (fun i _ j _ hij => ho i j hij)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProjectionCommutatorEnergy
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The energy removed by a two-sided projection cut

For commuting left and right projections, the diagonal cut is an
orthogonal projection. Its discarded squared norm is exactly the
squared norm of their difference acting on the vector.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def pairedProjectionCut (p q : H →L[ℂ] H) : H →L[ℂ] H :=
  p * q + (1 - p) * (1 - q)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularPositiveReal
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The modular conjugation fixes the generated positive cone -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

def conjugationFixedCone (J : H ≃ₗᵢ⋆[ℂ] H) : ConvexCone ℝ H where
  carrier := {η | J η = η}
  smul_mem' c _ η hη := by
    change J ((c : ℂ) • η) = (c : ℂ) • η
    rw [J.map_smulₛₗ,Complex.conj_ofReal,hη]
  add_mem' η hη ζ hζ := by
    change J (η+ζ) = η+ζ
    rw [map_add,hη,hζ]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PositiveConeProjectionSupport
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Projection supports of positive vectors

A projection kills a positive vector precisely when its matching left-right
corner does. This proves that positive summands cannot cancel on a left
support. No self-duality or state-representation theorem is assumed.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

local instance positiveProjectionRealInner : InnerProductSpace ℝ H := InnerProductSpace.complexToReal

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PositiveConeOrthogonality
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Orthogonal positive vectors have orthogonal algebra supports

The quadratic positivity of the generated modular cone suffices for this
step of Araki's Theorem 4(7), Pacific J. Math. 50 (1974), 309–354.
No self-duality or positive decomposition is assumed.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

local instance positiveOrthogonalityRealInner : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PositiveConeDualProjection
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Projection onto the generated positive cone

The Hilbert projection theorem gives a positive part and an orthogonal
residual in the dual cone. Both vectors are fixed by the conjugation.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

local instance positiveDualProjectionRealInner : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PositiveConeSelfDual
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Self-duality on the conjugation-fixed real Hilbert space

A dual residual orthogonal to a positive vector is killed by its support.
Compressing the reference vector to the complementary corner then forces
that residual to vanish. Cyclicity of the reference is the only density
hypothesis. This proves the local self-duality needed for state estimates.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

local instance positiveSelfDualRealInner : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CuntzCommutator
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Scalar commutator bounds amplify along commuting Cuntz families -/

namespace KadisonKastler

open scoped BigOperators CStarAlgebra

noncomputable section

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Fintype ι] [DecidableEq ι]

local instance cuntzCommutatorOperatorOrder : PartialOrder (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrder _
local instance cuntzCommutatorOperatorStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixCommutantDistance
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Commutant distance in the presence of countable full matrix units

Finite matrix averaging and Cuntz amplification reduce the estimate to
the commutant-distance formula.
-/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance matrixDistanceOperatorOrder : PartialOrder (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrder _
local instance matrixDistanceOperatorStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SelfAdjointApproximation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Self-adjoint approximation by the algebra and its commutant -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def selfAdjointAlgebraCommutantSum (M : VonNeumannAlgebra H) : Set (H →L[ℂ] H) :=
  {T | ∃ a b : H →L[ℂ] H, a ∈ M ∧ b ∈ M.commutant ∧
    IsSelfAdjoint a ∧ IsSelfAdjoint b ∧ T = a + b}

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProjectionPinchedState
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Pinching a vector state across an almost central projection

This is the first state approximation in Haagerup's Lemma 3.6
(Acta Math.158(1987), p.138). The pinched state is constructed from
two vector functionals and retains faithfulness. Its norm distance from
the original state is controlled by the left/right projection gap.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

def projectionReflection (p : H →L[ℂ] H) : H →L[ℂ] H := (2:ℂ) • p - 1

theorem projectionReflection_unitary {p : H →L[ℂ] H} (hp : IsStarProjection p) :
    projectionReflection p ∈ unitary (H →L[ℂ] H) := by
  have hs : star (projectionReflection p) = projectionReflection p := by
    simp only [projectionReflection,star_sub,star_smul,hp.isSelfAdjoint.star_eq,star_one,
      star_ofNat]
  have hm : projectionReflection p * projectionReflection p = 1 := by
    simp only [projectionReflection,sub_mul,mul_sub,smul_mul_smul,mul_one,one_mul,
      hp.isIdempotentElem.eq]
    module
  exact ⟨by rw [hs,hm],by rw [hs,hm]⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PositiveConeStateEstimate
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The state norm estimate from an orthogonal positive decomposition

This is the last step of Araki's Theorem 4(8), Pacific J. Math. 50 (1974),
309–354. A reflection in the support of the positive part witnesses the
state norm. The existence of the orthogonal decomposition is left explicit.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

local instance positiveStateEstimateRealInner : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PositiveConePowersStormer
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Powers–Størmer estimate for the generated modular cone

Orthogonal positive decomposition follows from the constructed self-duality.
The support-reflection estimate then proves Araki's Theorem 4(8) in precisely
the represented cyclic setting used for matrix preparation.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

local instance powersStormerRealInner : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TwoCornerStateNorm
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Combining state comparisons on complementary corners

A functional centralizing a projection is the sum of its two compressed
functionals. Comparing normalized corner states and their scalar weights
therefore controls the norm distance of the original states.
-/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A]

def cornerFunctional (φ : A →L[ℂ] ℂ) (p : A) : A →L[ℂ] ℂ :=
  φ.comp (((ContinuousLinearMap.mul ℂ A).flip p).comp (ContinuousLinearMap.mul ℂ A p))

@[simp] theorem cornerFunctional_apply (φ : A →L[ℂ] ℂ) (p a : A) :
    cornerFunctional φ p a = φ (p*a*p) := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PairedMatrixColumn
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The partial isometry from a matrix corner to central vectors

This is the algebraic corner map in Haagerup, Acta Math.158(1987),
Lemma3.5. Its initial projection is the matching minimal corner; its
final projection is the finite-matrix central-vector projection.
-/

namespace KadisonKastler

open Generator
open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  (E F : MatrixUnitSystem ι (H →L[ℂ] H))
  (hc : ∀ i j k l, Commute (E.entry i j) (F.entry k l))

def pairedMatrixColumn (o : ι) : H →L[ℂ] H :=
  Complex.ofReal ((Real.sqrt (Fintype.card ι))⁻¹) •
    ∑ i, E.entry i o * F.entry i o

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PartialIsometryCorner
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A partial isometry between two isometrically embedded Hilbert spaces -/

namespace KadisonKastler

noncomputable section

variable {H K E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem corner_adjoint_comp (U : H →ₗᵢ[ℂ] E) (V : K →ₗᵢ[ℂ] E) (W : E →L[ℂ] E)
    (hU : W.adjoint.comp W = U.toContinuousLinearMap.comp U.toContinuousLinearMap.adjoint)
    (hV : W.comp W.adjoint = V.toContinuousLinearMap.comp V.toContinuousLinearMap.adjoint) :
    (V.toContinuousLinearMap.adjoint.comp (W.comp U.toContinuousLinearMap)).adjoint.comp
      (V.toContinuousLinearMap.adjoint.comp (W.comp U.toContinuousLinearMap)) = 1 := by
  let u := U.toContinuousLinearMap
  let v := V.toContinuousLinearMap
  have hu : u.adjoint.comp u = 1 := U.adjoint_comp_self
  change (v.adjoint.comp (W.comp u)).adjoint.comp (v.adjoint.comp (W.comp u)) = 1
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint]
  calc
    _ = u.adjoint.comp (W.adjoint.comp ((v.comp v.adjoint).comp (W.comp u))) := by
      simp only [ContinuousLinearMap.comp_assoc]
    _ = u.adjoint.comp (W.adjoint.comp ((W.comp W.adjoint).comp (W.comp u))) := by rw [hV]
    _ = u.adjoint.comp ((W.adjoint.comp W).comp ((W.adjoint.comp W).comp u)) := by
      simp only [ContinuousLinearMap.comp_assoc]
    _ = u.adjoint.comp ((u.comp u.adjoint).comp ((u.comp u.adjoint).comp u)) := by rw [hU]
    _ = 1 := by
      simp only [← ContinuousLinearMap.comp_assoc, hu, ContinuousLinearMap.one_def,
        ContinuousLinearMap.id_comp]

/-- Compress a partial isometry whose initial and final projections are the two range projections. -/
def partialIsometryCornerEquiv (U : H →ₗᵢ[ℂ] E) (V : K →ₗᵢ[ℂ] E) (W : E →L[ℂ] E)
    (hU : W.adjoint.comp W = U.toContinuousLinearMap.comp U.toContinuousLinearMap.adjoint)
    (hV : W.comp W.adjoint = V.toContinuousLinearMap.comp V.toContinuousLinearMap.adjoint) :
    H ≃ₗᵢ[ℂ] K := by
  let T := V.toContinuousLinearMap.adjoint.comp (W.comp U.toContinuousLinearMap)
  have hT : T.adjoint.comp T = 1 := corner_adjoint_comp U V W hU hV
  have hT' : T.comp T.adjoint = 1 := by
    have h := corner_adjoint_comp V U W.adjoint (by simpa using hV) (by simpa using hU)
    simpa only [T, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
      ContinuousLinearMap.comp_assoc] using h
  exact LinearIsometryEquiv.ofSurjective
    { T.toLinearMap with norm_map' := T.norm_map_iff_adjoint_comp_self.mpr hT }
    (fun y => ⟨T.adjoint y, by
      have h := congrArg (fun S : K →L[ℂ] K => S y) hT'
      simpa using h⟩)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SeparableAlgebraPair
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

def increasingCstarClosure (A : ℕ → StarSubalgebra ℂ (H →L[ℂ] H)) :
    StarSubalgebra ℂ (H →L[ℂ] H) := (iSup A).topologicalClosure

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.TracialSplitting_Model
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe uA uD uE uI uR uX

section

namespace Pureness

open Filter Topology

variable {A : Type uA} [NormedRing A]

def TopologicallySimple (A : Type uA) [NormedRing A] : Prop :=
  ∀ I : TwoSidedIdeal A, IsClosed (I : Set A) → I = ⊥ ∨ I = ⊤

end Pureness

end

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.TracialSplitting_SimpleIdeals
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe uA uC uι

namespace Pureness

section

open Filter Topology

variable {A : Type uA} [NormedRing A]

def closedTwoSidedIdeal (I : TwoSidedIdeal A) : TwoSidedIdeal A :=
  TwoSidedIdeal.mk' (closure (I : Set A))
    (subset_closure I.zero_mem)
    (by
      intro x y hx hy
      obtain ⟨u, hu, hux⟩ := mem_closure_iff_seq_limit.mp hx
      obtain ⟨v, hv, hvy⟩ := mem_closure_iff_seq_limit.mp hy
      exact isClosed_closure.mem_of_tendsto (hux.add hvy)
        (Eventually.of_forall fun j => subset_closure (I.add_mem (hu j) (hv j))))
    (by
      intro x hx
      obtain ⟨u, hu, hux⟩ := mem_closure_iff_seq_limit.mp hx
      exact isClosed_closure.mem_of_tendsto hux.neg
        (Eventually.of_forall fun j => subset_closure (I.neg_mem (hu j))))
    (by
      intro x y hy
      obtain ⟨u, hu, huy⟩ := mem_closure_iff_seq_limit.mp hy
      exact isClosed_closure.mem_of_tendsto (huy.const_mul x)
        (Eventually.of_forall fun j => subset_closure (I.mul_mem_left x (u j) (hu j))))
    (by
      intro x y hx
      obtain ⟨u, hu, hux⟩ := mem_closure_iff_seq_limit.mp hx
      exact isClosed_closure.mem_of_tendsto (hux.mul_const y)
        (Eventually.of_forall fun j => subset_closure (I.mul_mem_right (u j) y (hu j))))

@[simp] theorem coe_closedTwoSidedIdeal (I : TwoSidedIdeal A) :
    (closedTwoSidedIdeal I : Set A) = closure (I : Set A) := by
  simp [closedTwoSidedIdeal]

end

open Filter Topology

end Pureness

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.TracialSplitting_NuclearTransfer
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uR uS


section

noncomputable section

universe v

namespace Pureness

namespace NuclearLift

variable (B : Type) [CStarAlgebra B]

instance instStarULift_solutions : Star (ULift.{v} B) := ⟨fun x => ⟨star x.down⟩⟩

instance instStarRingULift_solutions : StarRing (ULift.{v} B) where
  star_involutive x := by apply ULift.down_injective; exact star_star x.down
  star_mul x y := by apply ULift.down_injective; exact star_mul x.down y.down
  star_add x y := by apply ULift.down_injective; exact star_add x.down y.down

instance instStarModuleComplexULift_solutions : StarModule ℂ (ULift.{v} B) where
  star_smul c x := by apply ULift.down_injective; exact star_smul c x.down

instance instCStarRingULift_solutions : CStarRing (ULift.{v} B) where
  norm_mul_self_le x := CStarRing.norm_mul_self_le x.down

instance instCStarAlgebraULift_solutions : CStarAlgebra (ULift.{v} B) where

end NuclearLift

open scoped TensorProduct

end Pureness

end

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteGroupAverage
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The normalized finite-group mean

Finite averaging gives the equivariant bimodule mean needed by quadratic correction, for every C-star algebra of values.
-/

namespace KadisonKastler

open scoped BigOperators BoundedContinuousFunction

noncomputable section

variable {G B : Type*} [Group G] [Fintype G] [TopologicalSpace G]
  [DiscreteTopology G] [CStarAlgebra B]

/-- Normalized counting average on bounded functions. -/
def finiteGroupAverage : (G →ᵇ B) →L[ℂ] B :=
  ((Fintype.card G : ℝ)⁻¹) • ∑ g : G, BoundedContinuousFunction.evalCLM ℂ g

omit [Group G] [DiscreteTopology G] in
@[simp]
theorem finiteGroupAverage_apply (f : G →ᵇ B) :
    finiteGroupAverage f = ((Fintype.card G : ℝ)⁻¹) • ∑ g : G, f g := by
  simp [finiteGroupAverage]

omit [DiscreteTopology G] in
theorem finiteGroupAverage_norm_le (f : G →ᵇ B) :
    ‖finiteGroupAverage f‖ ≤ ‖f‖ := by
  have hc : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  rw [finiteGroupAverage_apply, norm_smul, Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ (Fintype.card G : ℝ)⁻¹ * ∑ g : G, ‖f g‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ (Fintype.card G : ℝ)⁻¹ * ∑ _g : G, ‖f‖ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum (fun g _ => f.norm_coe_le_norm g)
    _ = ‖f‖ := by simp [Finset.sum_const, nsmul_eq_mul, hc.ne']

omit [DiscreteTopology G] in
@[simp]
theorem finiteGroupAverage_const (b : B) :
    finiteGroupAverage (BoundedContinuousFunction.const G b) = b := by
  have hc : (Fintype.card G : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card G ≠ 0)
  rw [finiteGroupAverage_apply]
  simp only [BoundedContinuousFunction.const_apply, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hc, one_smul]

omit [Group G] [DiscreteTopology G] in
theorem finiteGroupAverage_star (f : G →ᵇ B) :
    finiteGroupAverage (star f) = star (finiteGroupAverage f) := by
  simp only [finiteGroupAverage_apply, star_smul, star_trivial, star_sum,
    BoundedContinuousFunction.star_apply]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_IncreasingFiniteMean
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Invariant means from increasing finite subgroups

Normalized counting averages have a simultaneous scalar ultralimit. Every
fixed group translation preserves all sufficiently late averages.
-/

namespace KadisonKastler

open Filter
open scoped Topology BigOperators BoundedContinuousFunction

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G]

theorem finiteAverage_positive [Fintype G] (f : G →ᵇ ℂ)
    (hf : ∀ g, (f g).im = 0 ∧ 0 ≤ (f g).re) :
    (finiteGroupAverage f).im = 0 ∧ 0 ≤ (finiteGroupAverage f).re := by
  have hi : (∑ g, f g).im = 0 := by
    change Complex.imLm (∑ g, f g) = 0
    rw [map_sum]
    exact Finset.sum_eq_zero (fun g _ => (hf g).1)
  have hr : 0 ≤ (∑ g, f g).re := by
    change 0 ≤ Complex.reLm (∑ g, f g)
    rw [map_sum]
    exact Finset.sum_nonneg (fun g _ => (hf g).2)
  rw [finiteGroupAverage_apply]
  simp only [Complex.real_smul, Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, hi, mul_zero, zero_mul, add_zero, sub_zero]
  exact ⟨trivial, mul_nonneg (by positivity) hr⟩

def subgroupRestriction (K : Subgroup G) : (G →ᵇ ℂ) →L[ℂ] (K →ᵇ ℂ) :=
  BoundedContinuousFunction.compContinuousCLM ℂ ℂ ⟨Subtype.val, continuous_subtype_val⟩

def finiteSubgroupFunctional (K : Subgroup G) [Finite K] : (G →ᵇ ℂ) →L[ℂ] ℂ := by
  let := Fintype.ofFinite K
  exact finiteGroupAverage.comp (subgroupRestriction K)

theorem finiteSubgroupFunctional_norm (K : Subgroup G) [Finite K] (f : G →ᵇ ℂ) :
    ‖finiteSubgroupFunctional K f‖ ≤ ‖f‖ := by
  let := Fintype.ofFinite K
  change ‖finiteGroupAverage (subgroupRestriction K f)‖ ≤ ‖f‖
  exact (finiteGroupAverage_norm_le _).trans
    (BoundedContinuousFunction.norm_compContinuous_le f _)

theorem finiteSubgroupFunctional_const (K : Subgroup G) [Finite K] (c : ℂ) :
    finiteSubgroupFunctional K (BoundedContinuousFunction.const G c) = c := by
  let := Fintype.ofFinite K
  change finiteGroupAverage (BoundedContinuousFunction.const K c) = c
  exact finiteGroupAverage_const c

theorem finiteSubgroupFunctional_positive (K : Subgroup G) [Finite K]
    (f : G →ᵇ ℂ) (hf : ∀ g, (f g).im = 0 ∧ 0 ≤ (f g).re) :
    (finiteSubgroupFunctional K f).im = 0 ∧ 0 ≤ (finiteSubgroupFunctional K f).re := by
  let := Fintype.ofFinite K
  exact finiteAverage_positive (subgroupRestriction K f) (fun g : K => hf g.val)

variable (K : ℕ → Subgroup G) [∀ n, Finite (K n)]

def finiteChainUltrafilter : Ultrafilter ℕ := Ultrafilter.of atTop

theorem finiteChainUltrafilter_le :
    (finiteChainUltrafilter : Filter ℕ) ≤ atTop := Ultrafilter.of_le atTop

theorem exists_finiteChainMeanValue (f : G →ᵇ ℂ) :
    ∃ z : ℂ, ‖z‖ ≤ ‖f‖ ∧ Tendsto (fun n => finiteSubgroupFunctional (K n) f)
      (finiteChainUltrafilter : Filter ℕ) (𝓝 z) := by
  obtain ⟨z, hz, ht⟩ := (isCompact_closedBall (0 : ℂ) ‖f‖).ultrafilter_le_nhds
    (finiteChainUltrafilter.map (fun n : ℕ => finiteSubgroupFunctional (K n) f)) (by
      apply le_principal_iff.mpr
      change ∀ᶠ n in (finiteChainUltrafilter : Filter ℕ),
        finiteSubgroupFunctional (K n) f ∈ Metric.closedBall (0 : ℂ) ‖f‖
      exact Eventually.of_forall (fun n : ℕ => by
        simpa only [Metric.mem_closedBall, dist_zero_right] using
          finiteSubgroupFunctional_norm (K n) f))
  exact ⟨z, by simpa only [Metric.mem_closedBall, dist_zero_right] using hz, ht⟩

def finiteChainMeanValue (f : G →ᵇ ℂ) : ℂ :=
  Classical.choose (exists_finiteChainMeanValue K f)

theorem finiteChainMeanValue_norm (f : G →ᵇ ℂ) :
    ‖finiteChainMeanValue K f‖ ≤ ‖f‖ :=
  (Classical.choose_spec (exists_finiteChainMeanValue K f)).1

theorem finiteChainMeanValue_tendsto (f : G →ᵇ ℂ) :
    Tendsto (fun n => finiteSubgroupFunctional (K n) f)
      (finiteChainUltrafilter : Filter ℕ) (𝓝 (finiteChainMeanValue K f)) :=
  (Classical.choose_spec (exists_finiteChainMeanValue K f)).2

theorem finiteChainMeanValue_add (f h : G →ᵇ ℂ) :
    finiteChainMeanValue K (f + h) = finiteChainMeanValue K f + finiteChainMeanValue K h := by
  apply tendsto_nhds_unique (finiteChainMeanValue_tendsto K (f + h))
  simpa only [map_add] using (finiteChainMeanValue_tendsto K f).add
    (finiteChainMeanValue_tendsto K h)

theorem finiteChainMeanValue_smul (c : ℂ) (f : G →ᵇ ℂ) :
    finiteChainMeanValue K (c • f) = c • finiteChainMeanValue K f := by
  apply tendsto_nhds_unique (finiteChainMeanValue_tendsto K (c • f))
  simpa only [map_smul] using (finiteChainMeanValue_tendsto K f).const_smul c

theorem finiteChainMeanValue_const (c : ℂ) :
    finiteChainMeanValue K (BoundedContinuousFunction.const G c) = c := by
  apply tendsto_nhds_unique (finiteChainMeanValue_tendsto K _)
  simpa only [finiteSubgroupFunctional_const] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => c) (finiteChainUltrafilter : Filter ℕ) (𝓝 c))

theorem finiteChainMeanValue_positive (f : G →ᵇ ℂ)
    (hf : ∀ g, (f g).im = 0 ∧ 0 ≤ (f g).re) :
    (finiteChainMeanValue K f).im = 0 ∧ 0 ≤ (finiteChainMeanValue K f).re := by
  constructor
  · apply tendsto_nhds_unique ((Complex.continuous_im.tendsto _).comp
      (finiteChainMeanValue_tendsto K f))
    have hi : (fun n : ℕ => (finiteSubgroupFunctional (K n) f).im) = fun _ => 0 :=
      funext (fun n => (finiteSubgroupFunctional_positive (K n) f hf).1)
    change Tendsto (fun n => (finiteSubgroupFunctional (K n) f).im)
      (finiteChainUltrafilter : Filter ℕ) (𝓝 0)
    rw [hi]
    exact tendsto_const_nhds
  · exact ge_of_tendsto ((Complex.continuous_re.tendsto _).comp
      (finiteChainMeanValue_tendsto K f))
      (Eventually.of_forall (fun n => (finiteSubgroupFunctional_positive (K n) f hf).2))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_HilbertMatrixGeneration
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Finite or countable matrix coordinates on separable Hilbert spaces -/

namespace KadisonKastler

open Generator
open scoped BigOperators Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The initial rank-one corner of a natural-number Hilbert basis. -/
def hilbertBasisInitialSpace (b : HilbertBasis ℕ ℂ H) : Submodule ℂ H :=
  (InnerProductSpace.rankOne ℂ (b 0) (b 0)).range

instance instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace (b : HilbertBasis ℕ ℂ H) : CompleteSpace (hilbertBasisInitialSpace b) :=
  (ContinuousLinearMap.IsIdempotentElem.isClosed_range
    (InnerProductSpace.isIdempotentElem_rankOne_self (b.orthonormal.norm_eq_one 0))).completeSpace_coe

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_DerivationStarReduction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Reduction to anti-star derivations

Sakai's spatial construction treats derivations satisfying
`D (star x) = -star (D x)`. Every bounded complex derivation is a complex
linear combination of two such derivations. That decomposition transfers innerness from anti-star derivations
to arbitrary bounded complex derivations.
-/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A]

def starConjugateMap (D : A →L[ℂ] A) : A →L[ℂ] A where
  toFun x := star (D (star x))
  map_add' x y := by simp
  map_smul' c x := by simp
  cont := continuous_star.comp (D.continuous.comp continuous_star)

@[simp] theorem starConjugateMap_apply (D : A →L[ℂ] A) (x : A) :
    starConjugateMap D x = star (D (star x)) := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_WOTDistanceSeparation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Weak operator separation and operator-norm distance

A dual estimate on weak-operator continuous functionals annihilating a
closed subspace gives strict norm approximants in that subspace.
-/

namespace KadisonKastler

open scoped Pointwise

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def wotNormBall (r : ℝ) : Set (H →WOT[ℂ] H) := {T | ‖T.toCLM‖ ≤ r}

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TomiyamaNormGeometry
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Norm geometry used in the projection theorem

A quadratic norm bound at the identity of a corner forces the real
first-order term to vanish.  This is the elementary norm argument in
Tomiyama's proof, separated from any operator-field representation.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {B : Type*} [CStarAlgebra B]

local instance tomiyamaOrder : PartialOrder B := CStarAlgebra.spectralOrder B

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixStrictContraction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Strict diagonal contraction in two-by-two coordinates -/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A]

variable [PartialOrder A] [StarOrderedRing A]

local instance matrixStrictContractionInstance1 : LE (CStarMatrix (Fin 2) (Fin 2) A) :=
  (CStarAlgebra.spectralOrder (CStarMatrix (Fin 2) (Fin 2) A)).toLE
local instance matrixStrictContractionInstance2 : PartialOrder (CStarMatrix (Fin 2) (Fin 2) A) :=
  CStarAlgebra.spectralOrder _
local instance matrixStrictContractionInstance3 : Preorder (CStarMatrix (Fin 2) (Fin 2) A) :=
  (CStarAlgebra.spectralOrder (CStarMatrix (Fin 2) (Fin 2) A)).toPreorder

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TypeIIIConstantNorm
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Type III corners of a constant-norm convex family vanish

The nonzero corner can be made strictly positive by independent small
left and right contractions. Both contractions come from convex unitary
averages. Removing the resulting off-diagonal corner then contradicts
the constant norm of the family.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance typeIIIConstantNormInstance1 : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularFixedVectors
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Fixed vectors of the constructed modular group

The half-eigenspace of the bounded graph resolvent is fixed by every
regularized group and by its strong limit. It contains the state vector
and the vectors obtained from elements of the vector-state centralizer.
-/

namespace KadisonKastler

open Filter TopologicalSpace
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

theorem cfcHom_half_eigen (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (x : H) (hx : A x = (1 / 2 : ℂ) • x) (hs : (1 / 2 : ℂ) ∈ spectrum ℂ A)
    (f : C(spectrum ℂ A, ℂ)) : (cfcHom (R := ℂ) hA.isStarNormal f) x = f ⟨1 / 2, hs⟩ • x := by
  induction f using ContinuousMap.induction_on_of_compact with
  | const r =>
    change (cfcHom (R := ℂ) hA.isStarNormal (algebraMap ℂ C(spectrum ℂ A, ℂ) r)) x = r • x
    rw [AlgHomClass.commutes]
    rfl
  | id =>
    rw [cfcHom_id]
    exact hx
  | star_id =>
    rw [map_star, cfcHom_id, hA.star_eq]
    simpa only [ContinuousMap.star_apply, ContinuousMap.restrict_apply,
      ContinuousMap.id_apply, star_div₀, star_one, star_ofNat] using hx
  | add f g hf hg =>
    rw [map_add, add_apply, hf, hg, ← add_smul]
    rfl
  | mul f g hf hg =>
    rw [map_mul, mul_apply_eq_comp, hg, map_smul, hf, smul_smul, mul_comm]
    rfl
  | frequently f hf =>
    have hc : IsClosed {g : C(spectrum ℂ A, ℂ) |
        (cfcHom (R := ℂ) hA.isStarNormal g) x = g ⟨1 / 2, hs⟩ • x} :=
      isClosed_eq ((cfcHom_continuous hA.isStarNormal).clm_apply continuous_const)
        ((continuous_eval_const _).smul continuous_const)
    have hm := mem_closure_iff_frequently.mpr hf
    change f ∈ closure {g : C(spectrum ℂ A, ℂ) |
      (cfcHom (R := ℂ) hA.isStarNormal g) x = g ⟨1 / 2, hs⟩ • x} at hm
    rwa [hc.closure_eq] at hm

theorem cfc_half_eigen (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (x : H) (hx : A x = (1 / 2 : ℂ) • x) (f : ℂ → ℂ)
    (hf : ContinuousOn f (spectrum ℂ A)) : (cfc f A) x = f (1 / 2) • x := by
  by_cases hx0 : x = 0
  · simp [hx0]
  have hs : (1 / 2 : ℂ) ∈ spectrum ℂ A := by
    apply spectrum.mem_iff.mpr
    intro hu
    have hinj := (ContinuousLinearMap.isUnit_iff_bijective.mp hu).1
    have hz : (algebraMap ℂ (H →L[ℂ] H) (1 / 2) - A) x = 0 := by
      rw [sub_apply, ContinuousLinearMap.algebraMap_apply, hx, sub_self]
    exact hx0 (hinj (hz.trans (map_zero _).symm))
  rw [cfc_apply f A hA.isStarNormal hf]
  exact cfcHom_half_eigen A hA x hx hs ⟨_, hf.domRestrict⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCoreDensePeriods
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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

/-- Almost-everywhere periods form an actual additive subgroup. -/
def scalarAEPeriods (f : ℝ → ℂ) : AddSubgroup ℝ where
  carrier := {s | (fun t => f (t + s)) =ᵐ[volume] f}
  zero_mem' := by simp
  add_mem' := by
    intro s t hs ht
    change (fun x => f (x + (s + t))) =ᵐ[volume] f
    have ht' := (measurePreserving_add_right (volume : Measure ℝ) s).quasiMeasurePreserving.ae_eq_comp ht
    filter_upwards [ht', hs] with x ht hs
    simpa only [Function.comp_def, add_assoc] using ht.trans hs
  neg_mem' := by
    intro s hs
    have hs' := (measurePreserving_add_right (volume : Measure ℝ) (-s)).quasiMeasurePreserving.ae_eq_comp hs
    filter_upwards [hs'] with x hx
    simpa only [Function.comp_def, add_assoc, neg_add_cancel, add_zero] using hx.symm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CompleteConjugation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The complete displacement of an inner conjugation -/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- Inner conjugation, with its linear-map structure. -/
def unitaryConjugationLinear (u : unitary B) : B →ₗ[ℂ] B :=
  (Unitary.conjStarAlgAut ℂ B u).toAlgEquiv.toLinearMap

omit [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem unitaryConjugationLinear_apply (u : unitary B) (x : B) :
    unitaryConjugationLinear u x = (u : B) * x * star (u : B) := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ConcreteUCP
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# The UCP criterion for concrete von Neumann algebras

The ordinary Kadison--Kastler gap supplies precisely the reverse unit-ball
approximation used in the UCP range argument.
-/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance instPartialOrderContinuousLinearMapComplexId_solutions_1 : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
local instance instStarOrderedRingContinuousLinearMapComplexId_solutions_1 : StarOrderedRing (H →L[ℂ] H) := CStarAlgebra.spectralOrderedRing _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_UCPDescent
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

section Concrete

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M N : VonNeumannAlgebra H}

local instance descentOperatorOrder {J : Type*} [NormedAddCommGroup J]
    [InnerProductSpace ℂ J] [CompleteSpace J] : PartialOrder (J →L[ℂ] J) :=
  CStarAlgebra.spectralOrder _
local instance descentOperatorStarOrder {J : Type*} [NormedAddCommGroup J]
    [InnerProductSpace ℂ J] [CompleteSpace J] : StarOrderedRing (J →L[ℂ] J) :=
  CStarAlgebra.spectralOrderedRing _

end Concrete

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProbabilityOperatorAlgebra
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Algebra membership of vectorwise probability averages -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {S H : Type*} [MeasurableSpace S]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem integrable_bounded_operator_vector (μ : Measure S) [IsProbabilityMeasure μ]
    (F : S → H →L[ℂ] H) (hm : ∀ x, AEStronglyMeasurable (fun s => F s x) μ)
    {C : ℝ} (hb : ∀ᵐ s ∂μ, ‖F s‖ ≤ C) (x : H) :
    Integrable (fun s => F s x) μ := by
  apply (integrable_const (C * ‖x‖)).mono' (hm x)
  filter_upwards [hb] with s hs
  exact ((F s).le_opNorm x).trans (mul_le_mul_of_nonneg_right hs (norm_nonneg x))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PositiveConeFaithfulApproximation
attribute [-instance] _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Faithful positive perturbations in the original Hilbert space

Adding a positive vector to a separating positive vector preserves
separation. A small positive multiple of the reference vector therefore
approximates any cone vector by cyclic separating cone vectors.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

local instance positiveApproximationRealInner : InnerProductSpace ℝ H := InnerProductSpace.complexToReal

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PositiveConeQuadraticSupport
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The left support of a modular quadratic vector

For a positive vector, the kernel of `a J a J` on that vector is already
the kernel of the left action of `a`. This is the support calculation
needed for faithful finite matrix averaging.
-/

namespace KadisonKastler

open Generator

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

local instance positiveQuadraticRealInner : InnerProductSpace ℝ H := InnerProductSpace.complexToReal

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PositiveMatrixAveraging
attribute [-instance] _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Faithfulness of finite matrix averaging on the positive cone

The explicit central-vector projection preserves separation. Positivity
prevents cancellation between its matrix-unit quadratic summands, and
the diagonal matrix units sum to the identity.
-/

namespace KadisonKastler

open Generator Generator.Tracial
open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

local instance positiveMatrixAverageRealInner : InnerProductSpace ℝ H := InnerProductSpace.complexToReal

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PositiveVectorPinching
attribute [-instance] _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Pinching positive vectors directly in the original representation

The matching two-sided cut preserves the positive cone and faithfulness,
centralizes the chosen projection, and has exactly the original
left-right projection gap as its displacement.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

local instance positivePinchRealInner : InnerProductSpace ℝ H := InnerProductSpace.complexToReal

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_NormalizedPositivePinching
attribute [-instance] _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A nearby faithful positive unit vector centralizing a projection

Two-sided pinching followed by normalization costs at most twice the
original left-right projection gap.
-/

namespace KadisonKastler

open Generator Generator.Tracial
open NormedSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

local instance normalizedPinchRealInner : InnerProductSpace ℝ H := InnerProductSpace.complexToReal

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_NormalizedMatrixAveraging
attribute [-instance] _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Faithful central unit vectors from finite matrix averaging

The explicit central-vector projection of a faithful positive unit vector
is nonzero. Normalizing it retains positivity, faithfulness and cyclicity,
with at most twice the displacement of the orthogonal projection.
-/

namespace KadisonKastler

open Generator NormedSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

local instance normalizedMatrixRealInner : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BicentralizerScalarHulls
attribute [-instance] _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Scalar weak orbit hulls from triviality of the bicentralizer

This constructs the implication in Haagerup, Acta Math. 158 (1987),
Proposition 1.3(2)(a) to (b). No orbit-averaging hypothesis is used.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

local instance scalarHullsRealInner : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ExponentialRemainder
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Uniform estimates for the exponential inverse near zero

These elementary Banach-algebra estimates are used to recover a small
normalizer's infinitesimal generator inside its invariant algebra.
-/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [NormedRing A]

section ComplexAlgebra

variable [NormedAlgebra ℂ A] [CompleteSpace A]

/-- The exponential after removing its constant and linear terms. -/
def exponentialRemainder (x : A) : A := NormedSpace.exp x - 1 - x

end ComplexAlgebra

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ClosedExponentialGenerator
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Recovering a small exponential generator in a closed subalgebra

The radius is absolute, independent of the ambient complex Banach algebra.
This is the logarithm-series step needed for a small exact normalizer.
-/

namespace KadisonKastler

noncomputable section

open Filter
open scoped NNReal Topology

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

omit [NormedAlgebra ℂ A] [CompleteSpace A] in
@[simp] theorem exponentialRemainder_zero : exponentialRemainder (0 : A) = 0 := by
  simp [exponentialRemainder]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.Naimark_Basic
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe u v w
namespace NaimarkZFC


def IsIrreducible {A : Type u} [CStarAlgebra A]
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) : Prop :=
  π ≠ 0 ∧ ∀ M : Submodule ℂ H, IsClosed (M : Set H) →
    (∀ a : A, ∀ x ∈ M, π a x ∈ M) → M = ⊥ ∨ M = ⊤

section GNS

open scoped ComplexOrder InnerProductSpace
open UniformSpace

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def IsPureState (f : A →L[ℂ] ℂ) : Prop :=
  f ∈ Set.extremePoints ℝ {g : A →L[ℂ] ℂ | IsState g}

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

variable {A : Type u} [CStarAlgebra A]
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [PartialOrder A] [StarOrderedRing A]

variable {A : Type u} [CStarAlgebra A]
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {A : Type u} [CStarAlgebra A]
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {K : Type w} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def cyclicGNSMap (f : A →ₚ[ℂ] ℂ) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (hcoeff : ∀ a : A, f a = ⟪ξ, π a ξ⟫_ℂ) : f.GNS →L[ℂ] H :=
  (cyclicPreGNS f π ξ hcoeff).toContinuousLinearMap.fromCompletion

@[simp] theorem cyclicGNSMap_apply (f : A →ₚ[ℂ] ℂ)
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (hcoeff : ∀ a : A, f a = ⟪ξ, π a ξ⟫_ℂ) (a : A) :
    cyclicGNSMap f π ξ hcoeff (f.toPreGNS a : f.GNS) = π a ξ := by
  simp [cyclicGNSMap]

end GNS

open Topology

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_HilbertSumOperators
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Uniformly bounded operators on a countable Hilbert sum -/

namespace KadisonKastler

noncomputable section

variable {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)]
  [∀ n, InnerProductSpace ℂ (E n)]
  (F : ∀ n, E n →L[ℂ] E n) (C : ℝ) (hC : 0 ≤ C) (hF : ∀ n, ‖F n‖ ≤ C)

include hC hF in
theorem hilbertSumOperator_memLp (f : lp E 2) : Memℓp (fun n => F n (f n)) 2 := by
  apply ((lp.memℓp f).const_smul (C : ℂ)).mono'
  intro n
  simpa only [Pi.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hC] using
    ((F n).le_opNorm (f n)).trans (mul_le_mul_of_nonneg_right (hF n) (norm_nonneg _))

def hilbertSumOperatorLinear : lp E 2 →ₗ[ℂ] lp E 2 where
  toFun f := ⟨fun n => F n (f n), hilbertSumOperator_memLp F C hC hF f⟩
  map_add' f g := by
    apply lp.ext
    funext n
    exact (F n).map_add (f n) (g n)
  map_smul' c f := by
    apply lp.ext
    funext n
    exact (F n).map_smul c (f n)

theorem hilbertSumOperatorLinear_norm_le (f : lp E 2) :
    ‖hilbertSumOperatorLinear F C hC hF f‖ ≤ C * ‖f‖ := by
  calc
    _ ≤ ‖(C : ℂ) • f‖ := by
      apply lp.norm_mono (by norm_num)
      intro n
      change ‖F n (f n)‖ ≤ ‖((C : ℂ) • f) n‖
      simpa only [lp.coeFn_smul, Pi.smul_apply, norm_smul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hC] using
        ((F n).le_opNorm (f n)).trans (mul_le_mul_of_nonneg_right (hF n) (norm_nonneg _))
    _ = _ := by rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC]

def hilbertSumOperator : lp E 2 →L[ℂ] lp E 2 :=
  (hilbertSumOperatorLinear F C hC hF).mkContinuous C
    (hilbertSumOperatorLinear_norm_le F C hC hF)

@[simp] theorem hilbertSumOperator_apply (f : lp E 2) (n : ℕ) :
    hilbertSumOperator F C hC hF f n = F n (f n) := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_IsometricCornerAlgebra
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The von Neumann algebra on a reducing isometric range -/

namespace KadisonKastler

open KadisonSimilarity

noncomputable section

variable {E H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (J : E →ₗᵢ[ℂ] H)

def rangeCompression (T : H →L[ℂ] H) : E →L[ℂ] E :=
  J.toContinuousLinearMap.adjoint.comp (T.comp J.toContinuousLinearMap)

theorem rangeCompression_intertwines_apply
    (A : StarSubalgebra ℂ (H →L[ℂ] H))
    (hA : ∀ a : A, isometricExtension J 1 * a.val = a.val * isometricExtension J 1)
    (a : A) (v : E) : J (rangeCompression J a v) = a.val (J v) := by
  have h := congrArg (fun T : H →L[ℂ] H => T (J v)) (hA a)
  change J (J.toContinuousLinearMap.adjoint (a.val (J v))) = a.val (isometricExtension J 1 (J v)) at h
  simpa only [rangeCompression, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, isometricExtension_on_range,
    one_apply_eq_self] using h

variable (M : VonNeumannAlgebra H) (hJM : isometricExtension J 1 ∈ M)

include hJM in
theorem rangeProjection_commutes_commutant (a : M.commutant.toStarSubalgebra) :
    isometricExtension J 1 * a.val = a.val * isometricExtension J 1 :=
  (VonNeumannAlgebra.mem_commutant_iff.mp a.property) _ hJM

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_HilbertSumCorners
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The reducing coordinate corners of a Hilbert sum -/

namespace KadisonKastler

open KadisonSimilarity
open scoped InnerProductSpace

noncomputable section

variable {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)]
  [∀ n, InnerProductSpace ℂ (E n)] [∀ n, CompleteSpace (E n)]

def hilbertSumInclusion (n : ℕ) : E n →ₗᵢ[ℂ] lp E 2 where
  toLinearMap := (lp.singleContinuousLinearMap ℂ E 2 n).toLinearMap
  norm_map' v := lp.norm_single (by norm_num) n v

omit [∀ n, CompleteSpace (E n)] in
@[simp] theorem hilbertSumInclusion_apply (n : ℕ) (v : E n) :
    hilbertSumInclusion n v = lp.single 2 n v := rfl

theorem hilbertSumInclusion_adjoint_apply (n : ℕ) (f : lp E 2) :
    (hilbertSumInclusion (E := E) n).toContinuousLinearMap.adjoint f = f n := by
  apply ext_inner_left ℂ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact lp.inner_single_left n v f

abbrev hilbertSumProjection (n : ℕ) : lp E 2 →L[ℂ] lp E 2 :=
  isometricExtension (hilbertSumInclusion n) 1

@[simp] theorem hilbertSumProjection_apply (n : ℕ) (f : lp E 2) :
    hilbertSumProjection n f = lp.single 2 n (f n) := by
  change hilbertSumInclusion n ((hilbertSumInclusion n).toContinuousLinearMap.adjoint f) = _
  rw [hilbertSumInclusion_adjoint_apply, hilbertSumInclusion_apply]

def hilbertSumCompression (n : ℕ) (T : lp E 2 →L[ℂ] lp E 2) : E n →L[ℂ] E n :=
  rangeCompression (hilbertSumInclusion n) T

@[simp] theorem hilbertSumCompression_apply (n : ℕ) (T : lp E 2 →L[ℂ] lp E 2) (v : E n) :
    hilbertSumCompression n T v = T (lp.single 2 n v) n :=
  hilbertSumInclusion_adjoint_apply n _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CommonRankOperatorFields
attribute [-instance] _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # Fields of all central-commutant operators in the rank coordinates -/

namespace KadisonKastler

open MeasureTheory KadisonSimilarity
open scoped lp

noncomputable section

variable {A B H : Type*}
  [CommCStarAlgebra A]
  [TopologicalSpace.SeparableSpace A]
  [CStarAlgebra B]
  [TopologicalSpace.SeparableSpace B]
  [NormedAddCommGroup H]
  [InnerProductSpace ℂ H]
  [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  {π : A →⋆ₐ[ℂ] (H →L[ℂ] H)}
  {D : CyclicDecompositionData π.range}
  {σ : B →⋆ₐ[ℂ] (H →L[ℂ] H)}

attribute [local instance] commonCyclicMeasurable commonCyclicBorel commonCyclicCountable

local instance rankFieldCoordinateMeasurable :
    MeasurableSpace (ScalarHilbertCoordinates D.generators) := borel _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CommonRankFactorFibers
attribute [-instance] _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # Factor fibers for a source and its commuting generating source -/

namespace KadisonKastler

open MeasureTheory KadisonSimilarity

noncomputable section

universe u

variable {Z H : Type u}
  [CommCStarAlgebra Z]
  [TopologicalSpace.SeparableSpace Z]
  [NormedAddCommGroup H]
  [InnerProductSpace ℂ H]
  [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  {π : Z →⋆ₐ[ℂ] (H →L[ℂ] H)}
  {D : CyclicDecompositionData π.range}
  (S : StarSubalgebra ℂ (H →L[ℂ] H))
  [IsClosed (S : Set (H →L[ℂ] H))]
  [TopologicalSpace.SeparableSpace S]

attribute [local instance] commonCyclicMeasurable commonCyclicBorel commonCyclicCountable

local instance rankFactorCoordinateMeasurable :
    MeasurableSpace (ScalarHilbertCoordinates D.generators) := borel _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CompleteLinearOperations
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Elementary operations on complete bounds -/

namespace KadisonKastler

noncomputable section

variable {A B C : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem matrix_map_add (F G : A →ₗ[ℂ] B) {p q : ℕ}
    (X : CStarMatrix (Fin p) (Fin q) A) :
    CStarMatrix.mapₗ (F + G) X = CStarMatrix.mapₗ F X + CStarMatrix.mapₗ G X := by
  ext i j
  rfl

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem matrix_map_zero {p q : ℕ} (X : CStarMatrix (Fin p) (Fin q) A) :
    CStarMatrix.mapₗ (0 : A →ₗ[ℂ] B) X = 0 := by
  ext i j
  rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CompleteCorrectionProducts
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Uniform complete bounds on the successive correction products -/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def correctionProducts (S : ℕ → A →L[ℂ] A) : ℕ → A →L[ℂ] A
  | 0 => ContinuousLinearMap.id ℂ A
  | n + 1 => (S n).comp (correctionProducts S n)

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] theorem correctionProducts_zero (S : ℕ → A →L[ℂ] A) :
    correctionProducts S 0 = ContinuousLinearMap.id ℂ A := rfl

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] theorem correctionProducts_succ (S : ℕ → A →L[ℂ] A) (n : ℕ) :
    correctionProducts S (n + 1) = (S n).comp (correctionProducts S n) := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ConjugationComparison
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Complete bounds for two operator conjugations

The smoothing operators need not be unitary. Their conjugation maps still
have a complete comparison bound controlled by their norms and distance.
-/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

def operatorConjugationLinear (v : B) : B →ₗ[ℂ] B where
  toFun x := v * x * star v
  map_add' x y := by simp only [mul_add, add_mul]
  map_smul' c x := by simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, RingHom.id_apply]

omit [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem operatorConjugationLinear_apply (v x : B) :
    operatorConjugationLinear v x = v * x * star v := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_InfinitesimalExponentiation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Exponentiating the infinitesimal normalizer estimate -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Products of an algebra unitary and a commutant unitary. -/
def separateUnitaryProducts (M : VonNeumannAlgebra H) : Set (H →L[ℂ] H) :=
  {T | ∃ a b : unitary (H →L[ℂ] H), (a : H →L[ℂ] H) ∈ M ∧
    (b : H →L[ℂ] H) ∈ M.commutant ∧ T = (a * b : unitary (H →L[ℂ] H))}

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_NormalizerLogarithm
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The logarithm of a small normalizer preserves the algebra

The bounded operators preserving a closed linear subspace form a closed
subalgebra. Uniform exponential inversion recovers the commutator generator
inside that subalgebra.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Bounded maps on the ambient operator algebra preserving `P`. -/
def preservingOperatorAlgebra (P : VonNeumannAlgebra H) :
    Subalgebra ℂ ((H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H)) where
  carrier := {T | ∀ a ∈ P, T a ∈ P}
  zero_mem' := by intro a ha; exact P.zero_mem
  one_mem' := by intro a ha; exact ha
  add_mem' := by intro T U hT hU a ha; exact P.add_mem (hT a ha) (hU a ha)
  mul_mem' := by intro T U hT hU a ha; exact hT _ (hU a ha)
  algebraMap_mem' := by
    intro c a ha
    change c • a ∈ P
    exact P.smul_mem ha c

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ConstructedNormalizerAveraging
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Averaging close exact normalizers within the normalizer group

Separate the near-identity residual into its algebra and commutant
factors, average these separately, and take their polar unitaries inside
the respective algebras. The quadratic covariance estimate controls the
loss from separating the average of the product.
-/

namespace KadisonKastler

open scoped CStarAlgebra BoundedContinuousFunction

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]

local instance constructedNormalizerAverageFamilyCStar : CStarAlgebra (G →ᵇ (H →L[ℂ] H)) where

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ConstructedNormalizerCorrection
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Quadratic correction while preserving normalizers

Averages are corrected inside the algebra and its commutant before they
are multiplied. The iteration therefore takes place in the complete space
of normalizing families, not in all ambient unitary families.
-/

namespace KadisonKastler

open scoped BoundedContinuousFunction

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]

local instance constructedNormalizerCorrectionCStar : CStarAlgebra (G →ᵇ (H →L[ℂ] H)) where

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ConstructedPairedAmplification
attribute [-instance] _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Complete closeness from the proved finite-factor estimate -/

namespace KadisonKastler
noncomputable section
universe u
variable {A : Type*} [CStarAlgebra A]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
variable {P : VonNeumannAlgebra (Generator.FiniteHilbert (Fin 2) H)}
local instance constructedPairedAmplificationSourceOrder : PartialOrder A := CStarAlgebra.spectralOrder _
local instance constructedPairedAmplificationSourceStarOrder : StarOrderedRing A := CStarAlgebra.spectralOrderedRing _
local instance constructedPairedAmplificationOperatorOrder : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
local instance constructedPairedAmplificationOperatorStarOrder : StarOrderedRing (H →L[ℂ] H) := CStarAlgebra.spectralOrderedRing _

end
end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ContinuousPolarPath
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Continuous polar unitary paths

The polar decomposition identifies its unitary factor with
`a * inverse(abs a)`. This gives norm continuity for continuous paths
of invertible operators, together with quantitative smoothing bounds.
-/

namespace KadisonKastler

open scoped Topology CStarAlgebra

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def polarUnitary (t : Aˣ) : unitary A := (exists_unitary_mul_abs t).choose

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CoreFrequencyUnitWindow
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A nonzero bounded frequency window in the modular core

The unit interval supplies an explicit isometric family of vectors fixed by
its frequency projection. No trace or finiteness assertion is used here.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def unitFrequencyScalar : Lp ℂ 2 (volume : Measure ℝ) :=
  indicatorConstLp (s := Set.Ioc (0 : ℝ) 1) 2 measurableSet_Ioc
    (measure_Ioc_lt_top (μ := volume)).ne (1 : ℂ)

@[simp] theorem norm_unitFrequencyScalar : ‖unitFrequencyScalar‖ = 1 := by
  rw [unitFrequencyScalar, norm_indicatorConstLp (by norm_num) (by norm_num)]
  simp [measureReal_def, Real.volume_Ioc]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CoreHalfFrequencyWindow
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A nonzero half-window and inclusions between core frequency cuts -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def halfFrequencyScalar : Lp ℂ 2 (volume : Measure ℝ) :=
  indicatorConstLp (s := Set.Ioc (0 : ℝ) (1 / 2)) 2 measurableSet_Ioc
    (measure_Ioc_lt_top (μ := volume)).ne (1 : ℂ)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CoreTraceSymmetry
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The weakly closed vector symmetry used for the core trace

Its scalar formulation is linear in the operator and passes to weak
operator limits. An involutive antiunitary then turns it into the exact
tracial norm identity needed by the finite-window criterion.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def coreTraceSymmetrySpace (C : H ≃ₗᵢ⋆[ℂ] H) (ξ : H) :
    Submodule ℂ (H →L[ℂ] H) where
  carrier := {T | ∀ η, inner ℂ η (T ξ) = inner ℂ ξ (T (C η))}
  zero_mem' := by intro η; simp
  add_mem' := by
    intro A B hA hB η
    simp only [add_apply, inner_add_right, hA η, hB η]
  smul_mem' := by
    intro z A hA η
    simp only [smul_apply, inner_smul_right, hA η]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CoreTraceMonomialReduction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Reduction of corner trace symmetry to regular monomials -/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def cornerCompressionLinear (p : H →L[ℂ] H) :
    (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H) where
  toFun T := p * T * p
  map_add' A B := by rw [mul_add, add_mul]
  map_smul' z A := by simp only [mul_smul_comm, smul_mul_assoc, RingHom.id_apply]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CoreTraceReciprocal
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A bounded reciprocal for the core trace packet

The reciprocal is cut off outside the unit frequency window. Its
spectral multiplier recovers the unweighted unit packet exactly.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

def coreTraceReciprocal (t : ℝ) : ℂ :=
  (Set.Ioc (0 : ℝ) 1).indicator (fun s => (Real.exp (Real.pi * (1 - s)) : ℂ)) t

theorem coreTraceReciprocal_measurable : Measurable coreTraceReciprocal :=
  (show Continuous (fun s : ℝ => (Real.exp (Real.pi * (1 - s)) : ℂ)) by
    fun_prop).measurable.indicator measurableSet_Ioc

theorem coreTraceReciprocal_bound (t : ℝ) :
    ‖coreTraceReciprocal t‖ ≤ Real.exp Real.pi := by
  by_cases ht : t ∈ Set.Ioc (0 : ℝ) 1
  · simp only [coreTraceReciprocal, Set.indicator_of_mem ht,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos, ht.1]
  · simp only [coreTraceReciprocal, Set.indicator_of_notMem ht, norm_zero]
    exact (Real.exp_pos _).le

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CyclicStateCompression
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Compression along a state-preserving inclusion

The GNS isometry supplies a concrete unital positive compression and its
matrix coefficients. It will be used to prescribe the two product marginals.
-/

namespace KadisonKastler

open NaimarkZFC
open scoped ComplexOrder

noncomputable section

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

def gnsInclusion (P : B →ₚ[ℂ] ℂ) (Q : A →ₚ[ℂ] ℂ)
    (ι : A →⋆ₐ[ℂ] B) (hPQ : ∀ a, Q a=P (ι a)) : Q.GNS →L[ℂ] P.GNS :=
  cyclicGNSMap Q (P.gnsStarAlgHom.comp ι).toNonUnitalStarAlgHom (gnsVector P)
    (fun a => (hPQ a).trans (gnsVector_coefficient P (ι a)).symm)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MaximalClosedStarIdeal
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A maximal proper closed star ideal in a unital C-star algebra

This supplies the quotient step in the unital specialization of Sakai's
ideal-extension argument. The closure of a proper ideal remains proper:
otherwise the original ideal meets the open set of invertible elements.
-/

namespace KadisonKastler

noncomputable section

open Filter Topology

variable {B : Type*} [CStarAlgebra B]

def idealChainUnion (c : Set (TwoSidedIdeal B)) (hc : IsChain (· ≤ ·) c)
    (hne : c.Nonempty) : TwoSidedIdeal B :=
  TwoSidedIdeal.mk' {x | ∃ I ∈ c, x ∈ I}
    (by obtain ⟨I, hI⟩ := hne; exact ⟨I, hI, I.zero_mem⟩)
    (by
      rintro x y ⟨I, hI, hx⟩ ⟨J, hJ, hy⟩
      obtain ⟨K, hK, hIK, hJK⟩ := hc.directedOn I hI J hJ
      exact ⟨K, hK, K.add_mem (hIK hx) (hJK hy)⟩)
    (by rintro x ⟨I, hI, hx⟩; exact ⟨I, hI, I.neg_mem hx⟩)
    (by rintro x y ⟨I, hI, hy⟩; exact ⟨I, hI, I.mul_mem_left x y hy⟩)
    (by rintro x y ⟨I, hI, hx⟩; exact ⟨I, hI, I.mul_mem_right x y hx⟩)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_DerivationExtensionFactor
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

local instance derivationExtensionFactorInstance1 : PartialOrder B := CStarAlgebra.spectralOrder B

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixStagesInClosure
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Regarding finite stages as subalgebras of their own closure -/

namespace KadisonKastler

open Generator

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

def matrixStagesInClosure (A : ℕ → FiniteMatrixStage M) (n : ℕ) :
    FiniteMatrixStage (FiniteMatrixStage.generatedVonNeumann A) where
  size := (A n).size
  positive := (A n).positive
  units := {
    entry := fun i j => ⟨((A n).units.entry i j).val,
      FiniteMatrixStage.stage_le_generated A n
        (((A n).units.mem_concreteAlgebra _).mpr ((A n).units.entry_mem i j))⟩
    star_entry := by
      intro i j
      apply Subtype.ext
      change star ((A n).units.entry i j).val = ((A n).units.entry j i).val
      exact congrArg (fun a : M.toStarSubalgebra => a.val) ((A n).units.star_entry i j)
    mul_entry := by
      intro i j k l
      apply Subtype.ext
      by_cases h : j = k
      · simp only [ite_eq_left h]
        change ((A n).units.entry i j).val * ((A n).units.entry k l).val =
          ((A n).units.entry i l).val
        exact congrArg (fun a : M.toStarSubalgebra => a.val)
          (((A n).units.mul_entry i j k l).trans (ite_eq_left h))
      · simp only [ite_eq_right h]
        change ((A n).units.entry i j).val * ((A n).units.entry k l).val = 0
        exact congrArg (fun a : M.toStarSubalgebra => a.val)
          (((A n).units.mul_entry i j k l).trans (ite_eq_right h))
    total := by
      apply Subtype.ext
      change (FiniteMatrixStage.generatedVonNeumann A).toStarSubalgebra.subtype
        (∑ i, (⟨((A n).units.entry i i).val, _⟩ :
          (FiniteMatrixStage.generatedVonNeumann A).toStarSubalgebra)) = 1
      rw [map_sum]
      have h := congrArg M.toStarSubalgebra.subtype (A n).units.total
      simp only [map_sum, map_one] at h
      change (∑ i, ((A n).units.entry i i).val) = 1 at h ⊢
      exact h }

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TomiyamaPositive
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Positivity of unital contractions

This is the first step of the norm-one projection argument.  Positivity
and adjoint preservation are derived from the norm bound and the unit.
-/

namespace KadisonKastler

noncomputable section

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

local instance tomiyamaSourceOrder_r32c67e_1 : PartialOrder A := CStarAlgebra.spectralOrder A
local instance tomiyamaSourceStarOrder_r32c67e_1 : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
local instance tomiyamaTargetOrder : PartialOrder B := CStarAlgebra.spectralOrder B

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_IncreasingMatrixPreparation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Increasing full matrix stages in the preparation argument

The finite-stage construction and the graph comparison use two equivalent
presentations of the same concrete matrix algebras. Their generated
von Neumann algebras agree, so approximate finite dimensionality gives
injectivity on both sides of the prepared graph.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

/-- The ambient matrix units of a finite stage. -/
def matrixStageConcreteUnits (A : ℕ → FiniteMatrixStage M) (n : ℕ) :
    MatrixUnitSystem (Fin (A n).size) (H →L[ℂ] H) :=
  (A n).units.map M.toStarSubalgebra.subtype

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TomiyamaProjection
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The projection part of Tomiyama's theorem

A unital contractive retraction onto a C-star subalgebra respects left
and right multiplication by projections in that subalgebra.
-/

namespace KadisonKastler

noncomputable section

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

local instance tomiyamaProjectionSourceOrder_r32c67e_1 : PartialOrder A := CStarAlgebra.spectralOrder A
local instance tomiyamaProjectionSourceStarOrder_r32c67e_1 : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
local instance tomiyamaProjectionTargetOrder : PartialOrder B := CStarAlgebra.spectralOrder B

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_NormalizedStageReference
attribute [-instance] _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Normalizing the faithful projected reference vector -/

namespace KadisonKastler

open Generator Generator.Tracial NormedSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

local instance normalizedStageRealInner : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_UnitaryResidualGap
attribute [-instance] _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Near-central unitaries with a uniform residual gap

The scalar hull conclusion of Haagerup's Proposition 1.3 gives the
unitary gap in Lemma 3.2. Centered cyclic approximation extends the
operator-vector calculation to every vector orthogonal to the reference.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

local instance unitaryResidualRealInner : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RelativePositiveDecomposition
attribute [-instance] _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Positive decomposition inside a finite-matrix central space

Orthogonal positive parts of a central vector remain central: the positive
central projection cannot discard a common nonzero component of those parts.
Their support projections therefore belong to the relative commutant.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}
  {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

local instance relativePositiveDecompositionRealInner : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RelativePowersStormer
attribute [-instance] _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The state-to-vector estimate in a finite-matrix relative commutant

The positive parts remain in the central-vector space. Their support
reflection belongs to the relative algebra, so its restricted state norm
already controls the ambient vector distance.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}
  {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

local instance relativePowersStormerRealInner : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RelativeUnitaryStateDefect
attribute [-instance] _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # State commutator bounds in a finite-matrix relative commutant

The relative Powers–Størmer estimate supplies the unitary defect bound
on the central-vector space, without treating the relative algebra as
cyclic on the full ambient Hilbert space.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}
  {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

local instance relativeUnitaryStateRealInner : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RelativeBicentralizerGap
attribute [-instance] _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Bicentralizer projection gaps in the matrix relative algebra

The residual vector is approximated only in the central-vector space.
The original positive cone supplies the relative state-to-vector bound.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}
  {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

local instance relativeBicentralizerRealInner : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RelativeMatrixExtension
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Extending a finite matrix stage inside its relative commutant -/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem matrix_relative_commutes (E : FiniteMatrixStage M)
    (F : FiniteMatrixStage E.units.relativeVonNeumann) :
    ∀ i j k l, Commute (E.units.entry i j)
      ((F.units.map (StarSubalgebra.inclusion E.units.relativeVonNeumann_le)).entry k l) := by
  intro i j k l
  apply Subtype.ext
  exact ((E.units.relativeStar_mem _).mp (F.units.entry k l).property).2 i j

def relativeMatrixExtension (E : FiniteMatrixStage M)
    (F : FiniteMatrixStage E.units.relativeVonNeumann) : FiniteMatrixStage M := by
  classical
  let I := Fin E.size × Fin F.size
  let : Nonempty I := ⟨⟨⟨0,E.positive⟩,⟨0,F.positive⟩⟩⟩
  let G := F.units.map (StarSubalgebra.inclusion E.units.relativeVonNeumann_le)
  let P := E.units.product G (matrix_relative_commutes E F)
  exact ⟨Fintype.card I,Fintype.card_pos,P.reindex (Fintype.equivFin I).symm⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RelativeRankMatrixState
attribute [-instance] _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Prescribed-rank positive states inside a matrix relative commutant

The comparison matrix stays in the relative algebra. Averaging over
its product with the initial matrix algebra produces a faithful positive
vector central for both algebras on the original Hilbert space.
-/

namespace KadisonKastler

open Generator Generator.Tracial
open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

local instance relativeRankRealInner : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RelativeMatrixStateHomogeneity
attribute [-instance] _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Faithful matrix-state approximation in a relative algebra

The matrix comparison is performed in the relative algebra, while positivity,
faithfulness and the central-vector conditions stay on the original space.
Connes–Størmer homogeneity remains an explicit input.
-/

namespace KadisonKastler

open Generator Generator.Tracial
open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

local instance relativeMatrixHomogeneityRealInner : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RelativePositivePinching
attribute [-instance] _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Positive pinching that preserves the initial matrix centralizer -/

namespace KadisonKastler

open Generator Generator.Tracial NormedSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

local instance relativePinchRealInner : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RelativeMatrixPreparation
attribute [-instance] _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A nearby relative matrix stage containing an almost-central projection

Relative Powers–Størmer converts state approximation into approximation
on the original Hilbert space. The resulting stage extends the initial one.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

local instance relativePreparationRealInner : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RelativeProjectionInsertion
attribute [-instance] _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Inserting a bicentralizer projection cut into a larger matrix stage

The fixed residual gap survives exact containment of the chosen projection.
The reference displacement can be made arbitrarily small.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

local instance relativeInsertionRealInner : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ExpectedFromRelativeBicentralizers
attribute [-instance] _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Expected matrix subfactors from relative bicentralizer triviality

Faithful-state homogeneity and scalar bicentralizers for finite-matrix
relative algebras give expected matrix subfactors on the original space.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H] [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

local instance expectedRelativeRealInner : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ExpectedFromBicentralizer
attribute [-instance] _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The expected subfactor from the ambient state properties

The relative algebras require no additional homogeneity or bicentralizer
assumptions: both properties transfer through the constructed spatial
matrix-corner isomorphism.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H] [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

local instance expectedBicentralizerRealInner : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ExpectedFromOneBicentralizer
attribute [-instance] _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The expected matrix subfactor needs one scalar bicentralizer

Faithful-state homogeneity transports scalarity to the other states used
in the finite-matrix refinement. The chosen reference state is arbitrary.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H] [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

local instance expectedOneBicentralizerRealInner : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteHaagerupBounds
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! Finite index changes for bilinear amplifications. -/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
/-- The bilinear amplification with arbitrary finite index types. -/
def finiteBilinearProduct (f : A →ₗ[ℂ] A →ₗ[ℂ] A)
    {ι κ τ : Type*} [Fintype κ] (X : CStarMatrix ι κ A) (Y : CStarMatrix κ τ A) :
    CStarMatrix ι τ A := CStarMatrix.ofMatrix fun i j => ∑ k, f (X i k) (Y k j)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteCochainDifferential
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! Hochschild matrix identities with arbitrary finite intermediate indices. -/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A]

@[simp] theorem finiteBilinearProduct_apply (f : A →ₗ[ℂ] A →ₗ[ℂ] A)
    {p r q : Type*} [Fintype r] (X : CStarMatrix p r A) (Y : CStarMatrix r q A)
    (i : p) (j : q) : finiteBilinearProduct f X Y i j = ∑ k, f (X i k) (Y k j) := rfl

@[simp] theorem finiteBilinearProduct_mul {p r q : Type*} [Fintype r]
    (X : CStarMatrix p r A) (Y : CStarMatrix r q A) :
    finiteBilinearProduct (LinearMap.mul ℂ A) X Y = X * Y := by ext; rfl

@[simp] theorem finiteBilinearProduct_add (f g : A →ₗ[ℂ] A →ₗ[ℂ] A) {p r q : Type*} [Fintype r]
    (X : CStarMatrix p r A) (Y : CStarMatrix r q A) :
    finiteBilinearProduct (f + g) X Y = finiteBilinearProduct f X Y + finiteBilinearProduct g X Y := by
  ext i j
  simp only [finiteBilinearProduct_apply, LinearMap.add_apply, Finset.sum_add_distrib, CStarMatrix.add_apply]

@[simp] theorem finiteBilinearProduct_sub (f g : A →ₗ[ℂ] A →ₗ[ℂ] A) {p r q : Type*} [Fintype r]
    (X : CStarMatrix p r A) (Y : CStarMatrix r q A) :
    finiteBilinearProduct (f - g) X Y = finiteBilinearProduct f X Y - finiteBilinearProduct g X Y := by
  ext i j
  simp only [finiteBilinearProduct_apply, LinearMap.sub_apply, Finset.sum_sub_distrib, CStarMatrix.sub_apply]

@[simp] theorem finiteBilinearProduct_add_left (f : A →ₗ[ℂ] A →ₗ[ℂ] A) {p r q : Type*} [Fintype r]
    (X X' : CStarMatrix p r A) (Y : CStarMatrix r q A) :
    finiteBilinearProduct f (X + X') Y = finiteBilinearProduct f X Y + finiteBilinearProduct f X' Y := by
  ext i j
  simp [map_add, Finset.sum_add_distrib]

@[simp] theorem finiteBilinearProduct_add_right (f : A →ₗ[ℂ] A →ₗ[ℂ] A) {p r q : Type*} [Fintype r]
    (X : CStarMatrix p r A) (Y Y' : CStarMatrix r q A) :
    finiteBilinearProduct f X (Y + Y') = finiteBilinearProduct f X Y + finiteBilinearProduct f X Y' := by
  ext i j
  simp [map_add, Finset.sum_add_distrib]

@[simp] theorem finiteBilinearProduct_smul (z : ℂ) (f : A →ₗ[ℂ] A →ₗ[ℂ] A) {p r q : Type*} [Fintype r]
    (X : CStarMatrix p r A) (Y : CStarMatrix r q A) :
    finiteBilinearProduct (z • f) X Y = z • finiteBilinearProduct f X Y := by
  ext i j
  change (∑ k, z • f (X i k) (Y k j)) = z • ∑ k, f (X i k) (Y k j)
  rw [Finset.smul_sum]

/-- The degree-two Hochschild differential, already amplified to matrices. -/
def finiteMatrixDifferential (f : A →ₗ[ℂ] A →ₗ[ℂ] A) {p r s q : Type*} [Fintype r] [Fintype s]
    (X : CStarMatrix p r A) (Y : CStarMatrix r s A)
    (Z : CStarMatrix s q A) : CStarMatrix p q A :=
  X * finiteBilinearProduct f Y Z - finiteBilinearProduct f (X * Y) Z +
    finiteBilinearProduct f X (Y * Z) - finiteBilinearProduct f X Y * Z

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_HilbertContractionFactor
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Contractive factorization through a Hilbert-space operator

This is the range-extension step used for contractive block completions in
the finite-nest distance argument. The factor is constructed on the closed
range and extended by zero on its orthogonal complement.
-/

namespace KadisonKastler

noncomputable section

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-- The same operator, with target restricted to the closure of its range. -/
def operatorClosedRangeMap (S : E →L[ℂ] F) :
    E →L[ℂ] S.toLinearMap.range.topologicalClosure :=
  S.codRestrict _ (fun x => Submodule.le_topologicalClosure _ ⟨x, rfl⟩)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_HilbertDefect
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

def operatorDefect (A : E →L[ℂ] F) : E →L[ℂ] E :=
  CFC.sqrt (1 - A.adjoint.comp A)

theorem operatorDefect_selfadjoint (A : E →L[ℂ] F) :
    IsSelfAdjoint (operatorDefect A) := (CFC.sqrt_nonneg _).isSelfAdjoint

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteOperatorDuality
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Finite operator coefficient duality

The polar factor and a positive rank-one decomposition give vector
coefficients whose two square sums are bounded by the functional norm.
This is the finite-dimensional part of the commutant distance formula.
-/

namespace KadisonKastler

open InnerProductSpace
open scoped BigOperators

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- A finite sum of vector coefficient functionals on bounded operators. -/
def finiteOperatorCoefficient {ι : Type*} [Fintype ι] (x y : ι → E) :
    (E →L[ℂ] E) →L[ℂ] ℂ :=
  ∑ i, (innerSL ℂ (y i)).comp (ContinuousLinearMap.apply ℂ E (x i))

omit [CompleteSpace E] in
@[simp]
theorem finiteOperatorCoefficient_apply {ι : Type*} [Fintype ι]
    (x y : ι → E) (S : E →L[ℂ] E) :
    finiteOperatorCoefficient x y S = ∑ i, inner ℂ (y i) (S (x i)) := by
  simp [finiteOperatorCoefficient]

variable [FiniteDimensional ℂ E]

/-- The trace pairing is kept as a bounded functional so that its norm is
the ordinary dual norm, with no additional trace-class definitions. -/
def operatorTracePairing (T : E →L[ℂ] E) : (E →L[ℂ] E) →L[ℂ] ℂ :=
  ({ toFun S := LinearMap.trace ℂ E (T.adjoint.comp S).toLinearMap
     map_add' S R := by simp
     map_smul' c S := by simp } : (E →L[ℂ] E) →ₗ[ℂ] ℂ).toContinuousLinearMap

@[simp]
theorem operatorTracePairing_apply (T S : E →L[ℂ] E) :
    operatorTracePairing T S = LinearMap.trace ℂ E (T.adjoint.comp S).toLinearMap := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_IsometryComplement
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Complementary projection of an isometric embedding

The formulas below retain the concrete adjoint of the embedding, as needed
for a contractive lift with prescribed first coordinate.
-/

namespace KadisonKastler

open scoped InnerProductSpace

noncomputable section

variable {E K : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def isometryComplement (V : E →ₗᵢ[ℂ] K) : K →L[ℂ] K :=
  1 - V.toContinuousLinearMap.comp V.toContinuousLinearMap.adjoint

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteCoefficientFactorization
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Sharp finite coefficient factorization on an arbitrary Hilbert space

All vectors involved lie in a finite-dimensional subspace. Compression and
extension by zero preserve the dual norm, so finite-dimensional polar
duality applies without a separability assumption on the ambient space.
-/

namespace KadisonKastler

open scoped BigOperators InnerProductSpace

noncomputable section

variable {E H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def isometricOperatorLift (J : E →ₗᵢ[ℂ] H) (S : E →L[ℂ] E) : H →L[ℂ] H :=
  J.toContinuousLinearMap.comp (S.comp J.toContinuousLinearMap.adjoint)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteCoordinateL2
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Density of finite-coordinate Hilbert functions

The random-walk proof needs approximants depending on a finite block. The
orthogonal complement is zero because its integrals over all cylinder sets
vanish, and cylinders generate the product sigma algebra.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory Set

variable {G K : Type*} [MeasurableSpace G]
  {μ : Measure (ℤ → G)} [IsProbabilityMeasure μ]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def finiteCoordinateL2 (μ : Measure (ℤ → G)) : Submodule ℂ (Lp K 2 μ) where
  carrier := {f | ∃ I : Finset ℤ, AEStronglyMeasurable[cylinderEvents (X := fun _ : ℤ => G) (I : Set ℤ)] f μ}
  zero_mem' := ⟨∅, aestronglyMeasurable_zero.congr (Lp.coeFn_zero K 2 μ).symm⟩
  add_mem' := by
    rintro f g ⟨I, hI⟩ ⟨J, hJ⟩
    refine ⟨I ∪ J, ?_⟩
    have hi := hI.mono (cylinderEvents_mono
      (show (I : Set ℤ) ⊆ ((I ∪ J : Finset ℤ) : Set ℤ) from fun _ h => Finset.mem_union_left J h))
    have hj := hJ.mono (cylinderEvents_mono
      (show (J : Set ℤ) ⊆ ((I ∪ J : Finset ℤ) : Set ℤ) from fun _ h => Finset.mem_union_right I h))
    exact (hi.add hj).congr (Lp.coeFn_add f g).symm
  smul_mem' := by
    rintro c f ⟨I, hI⟩
    exact ⟨I, (hI.const_smul c).congr (Lp.coeFn_smul c f).symm⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SignedSquareThreshold
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Signed-square coordinates for spectral cuts

Passing from a spectral value x to x |x| absorbs the weight |t| in
Haagerup's spectral-cut integral. The estimates here are scalar.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

def signedSquare (x : ℝ) : ℝ := x*|x|

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_OutwardSpectralCuts
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Finite outward spectral cuts

Negative thresholds take the lower spectral projection, positive thresholds
take the upper one. Signed-square coordinates make their integrated vector
mass equal to the squared norm of the original finite spectral sum.
-/

namespace KadisonKastler

open MeasureTheory Finset
open scoped BigOperators

noncomputable section

variable {H ι κ : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype ι] [Fintype κ]

def finiteOutwardProjection (P : ι → H →L[ℂ] H) (c : ι → ℝ) (t : ℝ) : H →L[ℂ] H :=
  if t < 0 then 1-finiteThresholdProjection P (signedSquare ∘ c) t
    else finiteThresholdProjection P (signedSquare ∘ c) t

theorem finiteOutwardProjection_isProjection
    (P : ι → H →L[ℂ] H) (hP : ∀ i, IsStarProjection (P i))
    (ho : ∀ i j, i ≠ j → P i*P j=0) (c : ι → ℝ) (t : ℝ) :
    IsStarProjection (finiteOutwardProjection P c t) := by
  unfold finiteOutwardProjection
  split
  · exact (finiteThresholdProjection_isProjection P hP ho _ t).one_sub
  · exact finiteThresholdProjection_isProjection P hP ho _ t

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_GaussianStateKernel
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Gaussian kernels for analytic smearing of a state-preserving action -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

def gaussianStateKernel (r : ℝ) (z : ℂ) (t : ℝ) : ℂ :=
  Complex.exp (-(r : ℂ) * ((t : ℂ) - z) ^ 2)

theorem gaussianStateKernel_norm (r : ℝ) (z : ℂ) (t : ℝ) :
    ‖gaussianStateKernel r z t‖ =
      Real.exp (r * z.im ^ 2) * Real.exp (-r * (t - z.re) ^ 2) := by
  rw [gaussianStateKernel, Complex.norm_exp, ← Real.exp_add]
  congr 1
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.ofReal_re, Complex.sub_re, Complex.ofReal_im, Complex.sub_im, Complex.neg_im]
  ring

theorem gaussianStateKernel_integrable {r : ℝ} (hr : 0 < r) (z : ℂ) :
    Integrable (gaussianStateKernel r z) := by
  have h := ((integrable_exp_neg_mul_sq hr).comp_sub_right z.re).const_mul
    (Real.exp (r * z.im ^ 2))
  have hc : Continuous (gaussianStateKernel r z) := by
    unfold gaussianStateKernel
    fun_prop
  apply h.mono' hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun t => (gaussianStateKernel_norm r z t).le

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_GaussianStateBounds
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Locally uniform bounds for analytic Gaussian kernels -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

def gaussianStateKernelDeriv (r : ℝ) (z : ℂ) (t : ℝ) : ℂ :=
  (2 * (r : ℂ) * ((t : ℂ) - z)) * gaussianStateKernel r z t

theorem gaussianStateKernel_local_bound {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    {z : ℂ} (hz : ‖z‖ ≤ R) (t : ℝ) :
    ‖gaussianStateKernel r z t‖ ≤
      Real.exp (2 * r * R ^ 2) * Real.exp (-(r / 2) * t ^ 2) := by
  have hre : |z.re| ≤ R := (Complex.abs_re_le_norm z).trans hz
  have him : |z.im| ≤ R := (Complex.abs_im_le_norm z).trans hz
  have hr2 : z.re ^ 2 ≤ R ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hR).2 hre
  have hi2 : z.im ^ 2 ≤ R ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hR).2 him
  have hq : t ^ 2 / 2 - z.re ^ 2 ≤ (t - z.re) ^ 2 := by
    nlinarith [sq_nonneg (t - 2 * z.re)]
  rw [gaussianStateKernel_norm, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_left hr2 hr.le,
    mul_le_mul_of_nonneg_left hi2 hr.le, mul_le_mul_of_nonneg_left hq hr.le]

theorem gaussianStateKernelDeriv_local_bound {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    {z : ℂ} (hz : ‖z‖ ≤ R) (t : ℝ) :
    ‖gaussianStateKernelDeriv r z t‖ ≤
      (2 * r * Real.exp (2 * r * R ^ 2)) *
        ((|t| + R) * Real.exp (-(r / 2) * t ^ 2)) := by
  have hdist : ‖(t : ℂ) - z‖ ≤ |t| + R := by
    calc
      _ ≤ ‖(t : ℂ)‖ + ‖z‖ := norm_sub_le _ _
      _ ≤ _ := by simpa only [Complex.norm_real, Real.norm_eq_abs] using
        add_le_add_right hz ‖(t : ℂ)‖
  have hb := gaussianStateKernel_local_bound hr hR hz t
  rw [gaussianStateKernelDeriv, norm_mul, norm_mul]
  have hc : ‖2 * (r : ℂ)‖ = 2 * r := by
    norm_num [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  rw [hc]
  calc
    _ ≤ (2 * r * (|t| + R)) *
        (Real.exp (2 * r * R ^ 2) * Real.exp (-(r / 2) * t ^ 2)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hdist (by positivity)) hb
        (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem gaussianStateKernelDeriv_bound_integrable {r : ℝ} (hr : 0 < r) (R : ℝ) :
    Integrable (fun t : ℝ =>
      (2 * r * Real.exp (2 * r * R ^ 2)) *
        ((|t| + R) * Real.exp (-(r / 2) * t ^ 2))) := by
  have hhalf : 0 < r / 2 := by positivity
  have ht : Integrable (fun t : ℝ => |t| * Real.exp (-(r / 2) * t ^ 2)) := by
    simpa only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)] using
      (integrable_mul_exp_neg_mul_sq hhalf).norm
  have hc := (integrable_exp_neg_mul_sq hhalf).const_mul R
  convert (ht.add hc).const_mul (2 * r * Real.exp (2 * r * R ^ 2)) using 1
  all_goals try with_reducible_and_instances rfl
  funext t
  change _ = (2 * r * Real.exp (2 * r * R ^ 2)) *
    (|t| * Real.exp (-(r / 2) * t ^ 2) + R * Real.exp (-(r / 2) * t ^ 2))
  ring

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_GaussianStateDerivative
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Bounded operators representing the derivative of Gaussian smearing -/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

def gaussianDerivativeEnvelope (r R t : ℝ) : ℝ :=
  (2 * r * Real.exp (2 * r * R ^ 2)) *
    ((|t| + R) * Real.exp (-(r / 2) * t ^ 2))

theorem gaussianDerivativeEnvelope_integrable {r : ℝ} (hr : 0 < r) (R : ℝ) :
    Integrable (gaussianDerivativeEnvelope r R) :=
  gaussianStateKernelDeriv_bound_integrable hr R

theorem gaussianStateKernelDeriv_integrable {r : ℝ} (hr : 0 < r) (z : ℂ) :
    Integrable (gaussianStateKernelDeriv r z) := by
  have hc : Continuous (gaussianStateKernelDeriv r z) := by
    unfold gaussianStateKernelDeriv gaussianStateKernel
    fun_prop
  exact (gaussianDerivativeEnvelope_integrable hr ‖z‖).mono' hc.aestronglyMeasurable
    (Eventually.of_forall fun t =>
      gaussianStateKernelDeriv_local_bound hr (norm_nonneg z) le_rfl t)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ScalarPacketMeasure
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The probability measure and action average of a scalar packet -/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

def scalarPacketMeasure (φ : Lp ℂ 2 (volume : Measure ℝ)) : Measure ℝ :=
  volume.withDensity (fun t => ENNReal.ofReal (‖φ t‖^2))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ShortFrequencyScalar
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Unit scalar packets in arbitrarily short frequency intervals -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

def shortFrequencyIndicator (δ : ℝ) : Lp ℂ 2 (volume : Measure ℝ) :=
  indicatorConstLp (s:=Set.Ioc 0 (δ/(2*Real.pi))) 2 measurableSet_Ioc
    (measure_Ioc_lt_top (μ:=volume)).ne (1 : ℂ)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PositiveReferenceCone
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Changing the cyclic reference inside the same positive cone

The quadratic positivity and the generated cone are unchanged when the
reference is replaced by a cyclic vector in that cone. These are the
reference-transport facts needed for projection-family amplification.
-/

namespace KadisonKastler

open Generator

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

local instance positiveReferenceRealInner : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PositiveReferenceModular
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The polar conjugation is unchanged at positive cyclic references

The old quadratic cone supplies positivity at the new reference. The
proved uniqueness theorem then identifies its constructed conjugation.
-/

namespace KadisonKastler

noncomputable section

open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

local instance positiveReferenceModularRealInner : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixFixedCorners
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A matrix automorphism fixing the two diagonal projections

Its off-diagonal coefficient is unitary and conjugates the two corner
actions. This is the finite algebraic step in the modular cocycle argument.
-/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A]

def matrixSlot (i j : Fin 2) (a : A) : CStarMatrix (Fin 2) (Fin 2) A :=
  CStarMatrix.ofMatrix (Matrix.single i j a)

theorem matrixSlot_injective (i j : Fin 2) : Function.Injective (matrixSlot (A := A) i j) := by
  intro a b hab
  simpa [matrixSlot, Matrix.single_apply] using
    congrArg (fun x : CStarMatrix (Fin 2) (Fin 2) A => x i j) hab

theorem matrixSlot_mul (i j k : Fin 2) (a b : A) :
    matrixSlot i j a * matrixSlot j k b = matrixSlot i k (a * b) :=
  Matrix.single_mul_single_same a i j k b

theorem matrixSlot_star (i j : Fin 2) (a : A) :
    star (matrixSlot i j a) = matrixSlot j i (star a) :=
  Matrix.conjTranspose_single i j a

theorem matrixSlot_sandwich (i j : Fin 2) (x : CStarMatrix (Fin 2) (Fin 2) A) :
    matrixSlot i i 1 * x * matrixSlot j j 1 = matrixSlot i j (x i j) := by
  apply CStarMatrix.ofMatrix.symm.injective
  change Matrix.single i i (1 : A) * CStarMatrix.ofMatrix.symm x * Matrix.single j j 1 =
    Matrix.single i j (x i j)
  simpa only [one_mul, mul_one, CStarMatrix.ofMatrix_symm_apply] using
    Matrix.single_mul_mul_single i i j j (1 : A) (CStarMatrix.ofMatrix.symm x) 1

theorem matrixSlot_reconstruct (i j : Fin 2) (x : CStarMatrix (Fin 2) (Fin 2) A)
    (hl : matrixSlot i i 1 * x = x) (hr : x * matrixSlot j j 1 = x) :
    x = matrixSlot i j (x i j) := by
  calc
    x = matrixSlot i i 1 * x * matrixSlot j j 1 := by rw [hl, hr]
    _ = _ := matrixSlot_sandwich i j x

variable (θ : CStarMatrix (Fin 2) (Fin 2) A ≃⋆ₐ[ℂ] CStarMatrix (Fin 2) (Fin 2) A)

theorem matrixSlot_image_reconstruct (i j : Fin 2)
    (hi : θ (matrixSlot i i 1) = matrixSlot i i 1)
    (hj : θ (matrixSlot j j 1) = matrixSlot j j 1) (a : A) :
    θ (matrixSlot i j a) = matrixSlot i j (θ (matrixSlot i j a) i j) := by
  apply matrixSlot_reconstruct
  · rw [← hi, ← map_mul, matrixSlot_mul, one_mul]
  · rw [← hj, ← map_mul, matrixSlot_mul, mul_one]

def matrixOffDiagonalCoefficient : A := θ (matrixSlot 1 0 1) 1 0

theorem matrixOffDiagonalCoefficient_unitary
    (h0 : θ (matrixSlot 0 0 1) = matrixSlot 0 0 1)
    (h1 : θ (matrixSlot 1 1 1) = matrixSlot 1 1 1) :
    matrixOffDiagonalCoefficient θ ∈ unitary A := by
  have he := matrixSlot_image_reconstruct θ 1 0 h1 h0 (1 : A)
  change θ (matrixSlot 1 0 1) = matrixSlot 1 0 (matrixOffDiagonalCoefficient θ) at he
  have hleft : star (θ (matrixSlot 1 0 1)) * θ (matrixSlot 1 0 1) = matrixSlot 0 0 1 := by
    rw [← map_star, ← map_mul, matrixSlot_star, star_one, matrixSlot_mul, one_mul, h0]
  have hright : θ (matrixSlot 1 0 1) * star (θ (matrixSlot 1 0 1)) = matrixSlot 1 1 1 := by
    rw [← map_star, ← map_mul, matrixSlot_star, star_one, matrixSlot_mul, one_mul, h1]
  rw [he, matrixSlot_star, matrixSlot_mul] at hleft hright
  exact ⟨matrixSlot_injective 0 0 hleft, matrixSlot_injective 1 1 hright⟩

theorem matrixCorner_actions_conjugate
    (h0 : θ (matrixSlot 0 0 1) = matrixSlot 0 0 1)
    (h1 : θ (matrixSlot 1 1 1) = matrixSlot 1 1 1) (a : A) :
    θ (matrixSlot 1 1 a) 1 1 = matrixOffDiagonalCoefficient θ *
      (θ (matrixSlot 0 0 a) 0 0) * star (matrixOffDiagonalCoefficient θ) := by
  have he := matrixSlot_image_reconstruct θ 1 0 h1 h0 (1 : A)
  have hx := matrixSlot_image_reconstruct θ 0 0 h0 h0 a
  have hrep : matrixSlot 1 1 a =
      matrixSlot 1 0 1 * matrixSlot 0 0 a * star (matrixSlot 1 0 (1 : A)) := by
    rw [matrixSlot_star, star_one, matrixSlot_mul, matrixSlot_mul, one_mul, mul_one]
  have h := congrArg θ hrep
  rw [map_mul, map_mul, map_star, he, hx, matrixSlot_star,
    matrixSlot_mul, matrixSlot_mul] at h
  have heq := congrArg (fun x : CStarMatrix (Fin 2) (Fin 2) A => x 1 1) h
  simpa [matrixSlot, matrixOffDiagonalCoefficient, Matrix.single_apply] using heq

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixCornerAutomorphism
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Restricting a matrix automorphism to a fixed diagonal corner -/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A]

theorem matrixSlot_add (i j : Fin 2) (a b : A) :
    matrixSlot i j (a + b) = matrixSlot i j a + matrixSlot i j b := by
  ext k l
  by_cases h : i = k ∧ j = l <;> simp [matrixSlot, h]

theorem matrixSlot_smul (i j : Fin 2) (r : ℂ) (a : A) :
    matrixSlot i j (r • a) = r • matrixSlot i j a := by
  ext k l
  simp [matrixSlot, Matrix.single_apply, smul_ite]

theorem matrixSlot_zero (i j : Fin 2) : matrixSlot (A := A) i j 0 = 0 := by
  ext k l
  simp [matrixSlot]

variable (θ : CStarMatrix (Fin 2) (Fin 2) A ≃⋆ₐ[ℂ] CStarMatrix (Fin 2) (Fin 2) A)
  (i : Fin 2) (hi : θ (matrixSlot i i 1) = matrixSlot i i 1)

def matrixCornerValue (a : A) : A := θ (matrixSlot i i a) i i

include hi in
theorem matrixCornerValue_reconstruct (a : A) :
    θ (matrixSlot i i a) = matrixSlot i i (matrixCornerValue θ i a) :=
  matrixSlot_image_reconstruct θ i i hi hi a

def matrixCornerHom : A →⋆ₐ[ℂ] A where
  toFun := matrixCornerValue θ i
  map_one' := by
    have h := congrArg (fun x : CStarMatrix (Fin 2) (Fin 2) A => x i i) hi
    simpa [matrixCornerValue, matrixSlot, Matrix.single_apply] using h
  map_mul' a b := by
    apply matrixSlot_injective i i
    calc
      matrixSlot i i (matrixCornerValue θ i (a * b)) = θ (matrixSlot i i (a * b)) :=
        (matrixCornerValue_reconstruct θ i hi _).symm
      _ = θ (matrixSlot i i a) * θ (matrixSlot i i b) := by
        rw [← matrixSlot_mul i i i a b, map_mul]
      _ = matrixSlot i i (matrixCornerValue θ i a * matrixCornerValue θ i b) := by
        rw [matrixCornerValue_reconstruct θ i hi, matrixCornerValue_reconstruct θ i hi,
          matrixSlot_mul]
  map_zero' := by
    change θ (matrixSlot i i 0) i i = 0
    rw [matrixSlot_zero, map_zero]
    rfl
  map_add' a b := by
    change θ (matrixSlot i i (a + b)) i i = _
    rw [matrixSlot_add, map_add, CStarMatrix.add_apply]
    rfl
  commutes' r := by
    change θ (matrixSlot i i (algebraMap ℂ A r)) i i = algebraMap ℂ A r
    rw [Algebra.algebraMap_eq_smul_one, matrixSlot_smul, map_smul, hi,
      CStarMatrix.smul_apply]
    simp [matrixSlot]
  map_star' a := by
    apply matrixSlot_injective i i
    calc
      matrixSlot i i (matrixCornerValue θ i (star a)) = θ (matrixSlot i i (star a)) :=
        (matrixCornerValue_reconstruct θ i hi _).symm
      _ = star (θ (matrixSlot i i a)) := by rw [← matrixSlot_star, map_star]
      _ = matrixSlot i i (star (matrixCornerValue θ i a)) := by
        rw [matrixCornerValue_reconstruct θ i hi, matrixSlot_star]

theorem matrixCornerHom_injective : Function.Injective (matrixCornerHom θ i hi) := by
  intro a b hab
  apply matrixSlot_injective i i
  apply θ.injective
  change θ (matrixSlot i i a) = θ (matrixSlot i i b)
  rw [matrixCornerValue_reconstruct θ i hi, matrixCornerValue_reconstruct θ i hi]
  exact congrArg (matrixSlot i i) hab

theorem matrixCornerHom_surjective : Function.Surjective (matrixCornerHom θ i hi) := by
  have hs : θ.symm (matrixSlot i i 1) = matrixSlot i i 1 := by
    calc
      _ = θ.symm (θ (matrixSlot i i 1)) := congrArg θ.symm hi.symm
      _ = _ := θ.symm_apply_apply _
  intro a
  refine ⟨matrixCornerValue θ.symm i a, ?_⟩
  apply matrixSlot_injective i i
  change matrixSlot i i (matrixCornerValue θ i (matrixCornerValue θ.symm i a)) = _
  rw [← matrixCornerValue_reconstruct θ i hi, ← matrixCornerValue_reconstruct θ.symm i hs,
    θ.apply_symm_apply]

def matrixCornerAut : A ≃⋆ₐ[ℂ] A :=
  StarAlgEquiv.ofBijective (matrixCornerHom θ i hi)
    ⟨matrixCornerHom_injective θ i hi, matrixCornerHom_surjective θ i hi⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixActionCocycle
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The cocycle obtained from an action fixing matrix corners -/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A]
  (α : Multiplicative ℝ →* (CStarMatrix (Fin 2) (Fin 2) A ≃⋆ₐ[ℂ]
    CStarMatrix (Fin 2) (Fin 2) A))
  (hfix : ∀ t i, α t (matrixSlot i i 1) = matrixSlot i i 1)

def matrixCornerAction (i : Fin 2) : Multiplicative ℝ →* (A ≃⋆ₐ[ℂ] A) where
  toFun t := matrixCornerAut (α t) i (hfix t i)
  map_one' := by
    apply StarAlgEquiv.ext
    intro a
    change α 1 (matrixSlot i i a) i i = a
    rw [map_one]
    simp [matrixSlot]
  map_mul' s t := by
    apply StarAlgEquiv.ext
    intro a
    change α (s * t) (matrixSlot i i a) i i =
      α s (matrixSlot i i (α t (matrixSlot i i a) i i)) i i
    rw [map_mul]
    change α s (α t (matrixSlot i i a)) i i = _
    exact congrArg (fun x => α s x i i)
      (matrixSlot_image_reconstruct (α t) i i (hfix t i) (hfix t i) a)

def matrixActionCocycleValue (t : Multiplicative ℝ) : unitary A :=
  ⟨matrixOffDiagonalCoefficient (α t),
    matrixOffDiagonalCoefficient_unitary (α t) (hfix t 0) (hfix t 1)⟩

theorem matrixActionCocycleValue_mul (s t : Multiplicative ℝ) :
    (matrixActionCocycleValue α hfix (s * t) : A) =
      (matrixActionCocycleValue α hfix s : A) *
        matrixCornerAction α hfix 0 s (matrixActionCocycleValue α hfix t : A) := by
  let c (r : Multiplicative ℝ) := matrixOffDiagonalCoefficient (α r)
  have he (r : Multiplicative ℝ) : α r (matrixSlot 1 0 1) = matrixSlot 1 0 (c r) :=
    matrixSlot_image_reconstruct (α r) 1 0 (hfix r 1) (hfix r 0) 1
  have hx : matrixSlot 1 0 (c t) = matrixSlot 1 0 1 * matrixSlot 0 0 (c t) := by
    rw [matrixSlot_mul, one_mul]
  have h : α (s * t) (matrixSlot 1 0 1) =
      matrixSlot 1 0 (c s * (α s (matrixSlot 0 0 (c t)) 0 0)) := by
    rw [map_mul]
    change α s (α t (matrixSlot 1 0 1)) = _
    calc
      α s (α t (matrixSlot 1 0 1)) =
          matrixSlot 1 0 (c s) * α s (matrixSlot 0 0 (c t)) := by
        rw [he t, hx, map_mul, he s]
      _ = matrixSlot 1 0 (c s) *
          matrixSlot 0 0 (α s (matrixSlot 0 0 (c t)) 0 0) :=
        congrArg (fun x => matrixSlot 1 0 (c s) * x)
          (matrixSlot_image_reconstruct (α s) 0 0 (hfix s 0) (hfix s 0) (c t))
      _ = _ := matrixSlot_mul 1 0 0 _ _
  rw [he (s * t)] at h
  exact matrixSlot_injective 1 0 h

theorem matrixCornerAction_conjugate (t : Multiplicative ℝ) (a : A) :
    matrixCornerAction α hfix 1 t a =
      (matrixActionCocycleValue α hfix t : A) * matrixCornerAction α hfix 0 t a *
        star (matrixActionCocycleValue α hfix t : A) :=
  matrixCorner_actions_conjugate (α t) (hfix t 0) (hfix t 1) a

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TwoStateCornerEmbedding
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Isometric embeddings of the two diagonal state spaces -/

namespace KadisonKastler

open Generator

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def twoStateVectorAt (Ω ξ : H) (i : Fin 2) : H := if i = 0 then Ω else ξ

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_NormalizingRepresentations
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Transporting normalization between nearby representations

This is the final change of position in modular alignment. The exact
normalizing representation is conjugated to the given representation
using the actual averaged intertwiner and its polar unitary.
-/

namespace KadisonKastler

open scoped CStarAlgebra BoundedContinuousFunction

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {G : Type*} [Group G]

variable [TopologicalSpace G] [DiscreteTopology G]

local instance normalizingFunctionCStar : CStarAlgebra (G →ᵇ (H →L[ℂ] H)) where

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularTensorGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Complete matrix bounds control the regular tensor gap

The scalar Hilbert coordinates identify the actual regular tensor algebra
with the canonical countable amplification. Uniform finite-matrix
approximation, or actual common countable matrix units, therefore bounds
its gap. No ordinary-gap amplification principle is assumed.
-/

namespace KadisonKastler

open MeasureTheory
open scoped Topology CStarAlgebra

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

local instance regularTensorGapOrder {J : Type*} [NormedAddCommGroup J]
    [InnerProductSpace ℂ J] [CompleteSpace J] : PartialOrder (J →L[ℂ] J) :=
  CStarAlgebra.spectralOrder _
local instance regularTensorGapStarOrder {J : Type*} [NormedAddCommGroup J]
    [InnerProductSpace ℂ J] [CompleteSpace J] : StarOrderedRing (J →L[ℂ] J) :=
  CStarAlgebra.spectralOrderedRing _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SpatialMatrix
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Finite matrix amplification in a spatial tensor product

An actual matrix-unit system in the second tensor factor gives a star
representation of operator-valued matrices. Its norm is the C-star matrix
norm: multiplying on both sides by matrix units recovers each coefficient,
so the representation is faithful whenever the second Hilbert space is
nonzero. No assertion about amplification of an ordinary algebra gap is
used here.
-/

namespace KadisonKastler

open Generator
open scoped BigOperators TensorProduct InnerProductSpace

noncomputable section

def matrixEntryStarHom {A B : Type*} [Ring A] [StarRing A] [_root_.Algebra ℂ A]
    [Ring B] [StarRing B] [_root_.Algebra ℂ B] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : A →⋆ₐ[ℂ] B) : Matrix ι ι A →⋆ₐ[ℂ] Matrix ι ι B where
  toAlgHom := φ.toAlgHom.mapMatrix
  map_star' X := by
    ext i j
    exact StarHomClass.map_star φ (X j i)

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance spatialMatrixOrder : PartialOrder (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrder _
local instance spatialMatrixStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SpatialMatrixImage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

namespace OAI

/-! # Finite spatial matrix images and their unit balls -/

namespace KadisonKastler

open Generator
open scoped BigOperators

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance spatialImageOperatorOrder : PartialOrder (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrder _
local instance spatialImageOperatorStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TwoRatioScalingWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Integer powers of the two fixed state-scaling ratios

Distinct finite sites realize each ratio `lambda^k * mu^l` exactly.
-/

namespace KadisonKastler

noncomputable section

def signedSiteRow (k : ℤ) : Fin 2 := if k < 0 then 1 else 0
def signedSiteColumn (k : ℤ) : Fin 2 := if k < 0 then 0 else 1
def signedSiteScale (ν : ℝ) (k : ℤ) : ℝ := if k < 0 then ν⁻¹ else ν

open Generator

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PositiveReferenceHaagerup
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

open Generator Generator.Tracial Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

local instance positiveHaagerupRealInner : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

universe u

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PositiveIsometryPullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Faithful positive references pulled back from a modular corner -/

namespace KadisonKastler

open NormedSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

local instance positivePullbackRealInner : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PositiveCornerWitness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Noncollinear projection witnesses in a modular corner

The corner reference is pulled back by the isometry and normalized. Its
faithfulness and polar conjugation are constructed, so the local witness
requires no independent corner standard-form or state-transitivity premise.
-/

namespace KadisonKastler

open Generator.Tracial NormedSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

local instance positiveCornerWitnessRealInner : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_NearlyFullCornerWitness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A uniform projection witness in every nearly full corner

The constant is independent of the corner. The hypotheses are the actual
positive reference and the all-vector remote coisometries already constructed
in the spatial two-ratio product.
-/

namespace KadisonKastler

open Generator.Tracial NormedSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

local instance nearlyFullRealInner : InnerProductSpace ℝ H := InnerProductSpace.complexToReal

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_StrictPinchingRefinement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A strict admissible refinement of every nearly full remainder

Both quantitative invariants survive the split, and the test-vector
energy increases strictly. This is the local contradiction for a maximal
orthogonal projection family.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

local instance strictPinchingRealInner : InnerProductSpace ℝ H := InnerProductSpace.complexToReal

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_UniformPinchingGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A uniform test-vector gap for an admissible projection family

A maximal admissible family cannot have a small gap: its remaining corner
would admit the strict refinement already constructed. This is the
projection-family amplification of the local Haagerup witness.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

local instance uniformPinchingRealInner : InnerProductSpace ℝ H := InnerProductSpace.complexToReal

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FinitePinchingApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Finite subfamilies retain a strict pinching gap -/

namespace KadisonKastler

open Generator.Tracial Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

variable [TopologicalSpace.SeparableSpace H]

local instance finitePinchingRealInner : InnerProductSpace ℝ H := InnerProductSpace.complexToReal

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FourierIntegralL2
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Agreement of the integral and Hilbert-space Fourier transforms

The reproducing kernels used by Hardy evaluation are integrable square-integrable
functions, rather than Schwartz functions. This bridge identifies their explicit
integral transforms with the existing unitary Fourier transform.
-/

namespace KadisonKastler

open MeasureTheory SchwartzMap
open scoped FourierTransform

noncomputable section

/-- An integrable scalar function whose Fourier transform is square integrable
has the same transform in the concrete `L²` Fourier representation. -/
theorem fourierInv_toLp_of_integrable {f : ℝ → ℂ} (hf : Integrable f)
    (hf2 : MemLp f 2) (hF2 : MemLp (𝓕⁻ f) 2) :
    𝓕⁻ (hf2.toLp f) = hF2.toLp (𝓕⁻ f) := by
  apply (LinearMap.ker_eq_bot.mp
    (Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ) (μ := volume) (p := 2)))
  change Lp.toTemperedDistribution (𝓕⁻ (hf2.toLp f)) =
    Lp.toTemperedDistribution (hF2.toLp (𝓕⁻ f))
  rw [← Lp.fourierInv_toTemperedDistribution_eq]
  ext g
  rw [TemperedDistribution.fourierInv_apply, Lp.toTemperedDistribution_apply,
    Lp.toTemperedDistribution_apply]
  have hl : (∫ x, (𝓕⁻ g) x • hf2.toLp f x) = ∫ x, (𝓕⁻ g) x • f x := by
    apply integral_congr_ae
    filter_upwards [hf2.coeFn_toLp] with x hx
    rw [hx]
  have hr : (∫ x, g x • hF2.toLp (𝓕⁻ f) x) = ∫ x, g x • (𝓕⁻ f) x := by
    apply integral_congr_ae
    filter_upwards [hF2.coeFn_toLp] with x hx
    rw [hx]
  rw [hl, hr]
  simpa only [SchwartzMap.fourierInv_coe, Real.fourierInv_eq, VectorFourier.fourierIntegral,
    LinearMap.flip_apply, LinearMap.neg_apply, neg_neg, innerₗ_apply_apply, real_inner_comm, smul_eq_mul] using!
    (VectorFourier.integral_fourierIntegral_smul_eq_flip
    (μ := volume) (ν := volume) (L := -innerₗ ℝ) Real.continuous_fourierChar (by fun_prop) g.integrable hf)


end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProbabilityMatrixDistance
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Distance to an algebra after vector integration

Diagonal amplification commutes with the actual vector integral. Applying
the published complete commutant-distance bound to the commutant gives
an algebra approximation without choosing measurable nearest points.
-/

namespace KadisonKastler

open MeasureTheory
open scoped BigOperators Pointwise

noncomputable section

variable {S H : Type*} [MeasurableSpace S]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance matrixIntegralOrder : PartialOrder (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrder _
local instance matrixIntegralStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PoissonCharacter
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Actual Poisson averages of scalar characters -/

namespace KadisonKastler

open MeasureTheory ProbabilityTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Scalar characters, regarded as a concrete field of operators. -/
def poissonCharacterField (s t : ℝ) : H →L[ℂ] H := (Circle.exp (s * t) : ℂ) • 1

omit [CompleteSpace H] in
theorem poissonCharacterField_measurable (s : ℝ) (x : H) :
    AEStronglyMeasurable (fun t => poissonCharacterField s t x) volume := by
  change AEStronglyMeasurable (fun t => (Circle.exp (s * t) : ℂ) • x) volume
  exact (((continuous_subtype_val.comp Circle.exp.continuous).comp
    (continuous_const.mul continuous_id)).smul continuous_const).aestronglyMeasurable

omit [CompleteSpace H] in
theorem norm_poissonCharacterField_le (s t : ℝ) : ‖poissonCharacterField (H := H) s t‖ ≤ 1 := by
  rw [poissonCharacterField, norm_smul, Circle.norm_coe, one_mul]
  exact ContinuousLinearMap.norm_id_le

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SmoothingHeightSequence
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Positive smoothing heights tending to the boundary -/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

def smoothingHeight (δ : ℝ) (n : ℕ) : ℝ := δ / ((n : ℝ) + 1)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_NormalizedPolarPath
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Based approximate-normalizer paths from smoothed algebra relations -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H]

local instance polarPathOrder : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FrequencyActionAlignment
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

def modularComparisonField
    (U V : Multiplicative ℝ →* unitary (H →L[ℂ] H)) (t : ℝ) :
    unitary (H →L[ℂ] H) := V (Multiplicative.ofAdd t) * star (U (Multiplicative.ofAdd t))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_GeneratedDerivationExtension
attribute [-instance] _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The concrete generated algebra and its faithful maximal quotient

This constructs the one-implementer extension used in the unital case of
Sakai's argument. Its generation property is retained through the quotient.
No innerness or ideal membership of the implementer is assumed here.
-/

namespace KadisonKastler

noncomputable section

universe u v

variable {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]

def generatedExtensionAlgebra (φ : A →⋆ₐ[ℂ] B) (d : B) : StarSubalgebra ℂ B :=
  (StarAlgebra.adjoin ℂ (Set.range φ ∪ {d})).topologicalClosure

instance generatedExtension_complete (φ : A →⋆ₐ[ℂ] B) (d : B) :
    CompleteSpace (generatedExtensionAlgebra φ d) :=
  inferInstanceAs
    (CompleteSpace (StarAlgebra.adjoin ℂ (Set.range φ ∪ {d})).topologicalClosure)

instance generatedExtension_cstar (φ : A →⋆ₐ[ℂ] B) (d : B) :
    CStarAlgebra (generatedExtensionAlgebra φ d) := {}

theorem generatedExtensionAlgebra_source (φ : A →⋆ₐ[ℂ] B) (d : B) (a : A) :
    φ a ∈ generatedExtensionAlgebra φ d :=
  StarSubalgebra.le_topologicalClosure _
    (StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨a, rfl⟩))

theorem generatedExtensionAlgebra_element (φ : A →⋆ₐ[ℂ] B) (d : B) :
    d ∈ generatedExtensionAlgebra φ d :=
  StarSubalgebra.le_topologicalClosure _
    (StarAlgebra.subset_adjoin ℂ _ (Or.inr (Set.mem_singleton d)))

def generatedExtensionEmbedding (φ : A →⋆ₐ[ℂ] B) (d : B) :
    A →⋆ₐ[ℂ] generatedExtensionAlgebra φ d :=
  φ.codRestrict _ (generatedExtensionAlgebra_source φ d)

def generatedExtensionElement (φ : A →⋆ₐ[ℂ] B) (d : B) :
    generatedExtensionAlgebra φ d := ⟨d, generatedExtensionAlgebra_element φ d⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_WeakMatrixLimits
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! Uniform rectangular matrix bounds are closed under entrywise weak limits. -/

namespace KadisonKastler

noncomputable section

open Filter Generator
open scoped Topology InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance weakMatrixOrder : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
local instance weakMatrixStarOrder : StarOrderedRing (H →L[ℂ] H) := CStarAlgebra.spectralOrderedRing _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_HaagerupWeakLimits
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! Haagerup bounds are closed under pointwise weak operator limits. -/

namespace KadisonKastler

noncomputable section

open Filter
open scoped Topology InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance haagerupWeakOperatorOrder : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_HardyCauchyKernel
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The one-sided exponential and its Cauchy transform

These are the concrete kernels for evaluating a positive-frequency multiplier.
All transforms here are computed from the half-line exponential integral.
-/

namespace KadisonKastler

open MeasureTheory
open scoped FourierTransform

noncomputable section

/-- The exponentially decreasing kernel on the positive frequency half-line. -/
def positiveLaplaceKernel (z : ℂ) : ℝ → ℂ :=
  Set.Ioi (0 : ℝ) |>.indicator (fun s => Complex.exp (-z * s))

theorem integrable_positiveLaplaceKernel {z : ℂ} (hz : 0 < z.re) :
    Integrable (positiveLaplaceKernel z) := by
  exact (integrableOn_exp_mul_complex_Ioi (a := -z) (by simpa using hz) 0).integrable_indicator
    measurableSet_Ioi

theorem positiveLaplaceKernel_memLp {z : ℂ} (hz : 0 < z.re) :
    MemLp (positiveLaplaceKernel z) 2 := by
  apply (memLp_two_iff_integrable_sq_norm
    (integrable_positiveLaplaceKernel hz).aestronglyMeasurable).mpr
  have hi := (integrableOn_exp_mul_Ioi (a := -2 * z.re) (by linarith) 0).integrable_indicator
    measurableSet_Ioi
  apply hi.congr
  filter_upwards [] with s
  by_cases hs : 0 < s
  · simp only [positiveLaplaceKernel, Set.indicator, Set.mem_Ioi, ite_eq_left hs,
      Complex.norm_exp, Complex.mul_re, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, ← Real.exp_nat_mul]
    congr 1
    ring
  · simp [positiveLaplaceKernel, hs]

theorem fourier_positiveLaplaceKernel {z : ℂ} (hz : 0 < z.re) (ξ : ℝ) :
    𝓕 (positiveLaplaceKernel z) ξ = (z + (2 * Real.pi * ξ : ℝ) * Complex.I)⁻¹ := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have he : (fun s : ℝ =>
      Complex.exp ((↑(-2 * Real.pi * s * ξ) : ℂ) * Complex.I) • positiveLaplaceKernel z s) =
      (Set.Ioi (0 : ℝ)).indicator
        (fun s => Complex.exp ((-z - (2 * Real.pi * ξ : ℝ) * Complex.I) * s)) := by
    funext s
    by_cases hs : 0 < s
    · simp only [positiveLaplaceKernel, Set.indicator, Set.mem_Ioi, ite_eq_left hs,
        smul_eq_mul, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    · simp [positiveLaplaceKernel, hs]
  rw [he, integral_indicator measurableSet_Ioi]
  rw [integral_exp_mul_complex_Ioi (by simpa using (neg_lt_zero.mpr hz))]
  have hn : -z - (2 * Real.pi * ξ : ℝ) * Complex.I =
      -(z + (2 * Real.pi * ξ : ℝ) * Complex.I) := by ring
  rw [hn]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, neg_div_neg_eq, one_div]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_HardyCauchyBoundary
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

def hardyCauchyFunction (z : ℂ) (s : ℝ) : ℂ :=
  (z - (2 * Real.pi * s : ℝ) * Complex.I)⁻¹

theorem fourierInv_positiveLaplaceKernel {z : ℂ} (hz : 0 < z.re) (s : ℝ) :
    𝓕⁻ (positiveLaplaceKernel z) s = hardyCauchyFunction z s := by
  rw [Real.fourierInv_eq_fourier_neg, fourier_positiveLaplaceKernel hz]
  unfold hardyCauchyFunction
  congr 1
  push_cast
  ring

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_HardyCompression
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Algebra evaluation from an invariant reproducing-kernel quotient

The Hardy-space evaluation is a compression. Multiplicativity follows when
its kernel is invariant and the operators preserve the positive-frequency
space.
-/

namespace KadisonKastler

noncomputable section

variable {H E : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
  [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The compression used for Hardy evaluation. The first identity preserves
the positive-frequency space on the kernel vectors, and the second expresses
invariance of the evaluation kernel inside that space. -/
def hardyCompressionAlgHom (A : Subalgebra ℂ (E →L[ℂ] E))
    (i : H →L[ℂ] E) (j : E →L[ℂ] H) (P : E →L[ℂ] E)
    (hji : j.comp i = ContinuousLinearMap.id ℂ H)
    (hleft : ∀ T : A, P.comp (T.val.comp i) = T.val.comp i)
    (hright : ∀ T : A,
      (j.comp T.val).comp P = ((j.comp T.val).comp i).comp j) :
    A →ₐ[ℂ] (H →L[ℂ] H) where
  toFun T := (j.comp T.val).comp i
  map_one' := by
    change (j.comp (ContinuousLinearMap.id ℂ E)).comp i = ContinuousLinearMap.id ℂ H
    rw [ContinuousLinearMap.comp_id, hji]
  map_zero' := by simp
  map_add' T S := by simp [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]
  map_mul' T S := by
    change (j.comp (T.val.comp S.val)).comp i =
      ((j.comp T.val).comp i).comp ((j.comp S.val).comp i)
    calc
      _ = (j.comp T.val).comp (S.val.comp i) := by
        simp only [ContinuousLinearMap.comp_assoc]
      _ = (j.comp T.val).comp (P.comp (S.val.comp i)) := by rw [hleft S]
      _ = ((j.comp T.val).comp P).comp (S.val.comp i) := by
        simp only [ContinuousLinearMap.comp_assoc]
      _ = (((j.comp T.val).comp i).comp j).comp (S.val.comp i) := by rw [hright T]
      _ = _ := by simp only [ContinuousLinearMap.comp_assoc]
  commutes' z := by
    change (j.comp (z • ContinuousLinearMap.id ℂ E)).comp i =
      z • ContinuousLinearMap.id ℂ H
    simp only [ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_id,
      ContinuousLinearMap.smul_comp, hji]

@[simp] theorem hardyCompressionAlgHom_apply (A : Subalgebra ℂ (E →L[ℂ] E))
    (i : H →L[ℂ] E) (j : E →L[ℂ] H) (P : E →L[ℂ] E)
    (hji : j.comp i = ContinuousLinearMap.id ℂ H)
    (hleft : ∀ T : A, P.comp (T.val.comp i) = T.val.comp i)
    (hright : ∀ T : A,
      (j.comp T.val).comp P = ((j.comp T.val).comp i).comp j) (T : A) :
    hardyCompressionAlgHom A i j P hji hleft hright T = (j.comp T.val).comp i := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_HermitianAnnihilatorBall
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The compact annihilator ball for Sakai's separation argument -/

namespace KadisonKastler

noncomputable section

open scoped Topology

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

def hermitianAnnihilatorBall (φ : A →⋆ₐ[ℂ] B) : Set (WeakDual ℂ B) :=
  {f | ‖f.toStrongDual‖ ≤ 1 ∧ (∀ b, f (star b) = star (f b)) ∧ ∀ a, f (φ a) = 0}

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_HilbertBlockCompletion
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Contractive completion of a Hilbert-space operator block

A contractive row and a contractive column with the same corner have a
common contractive completion. The construction uses the defect isometry
and the complementary lift, and is the finite completion step for nests.
-/

namespace KadisonKastler

open scoped InnerProductSpace

noncomputable section

variable {E F G H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def firstCoordinateIsometry : F →ₗᵢ[ℂ] WithLp 2 (F × E) where
  toFun y := WithLp.toLp 2 (y, 0)
  map_add' x y := by simp [← WithLp.toLp_add]
  map_smul' c x := by simp [← WithLp.toLp_smul]
  norm_map' y := WithLp.norm_toLp_fst 2 F E y

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_IsometricRestriction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Restricting a representation through a reducing isometry

Compression by an isometry is multiplicative when its range projection
commutes with the represented algebra. The intertwining identity is kept
explicit for later weak-continuity and faithfulness arguments.
-/

namespace KadisonKastler

noncomputable section

theorem isometry_equiv_comp_projection
    {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (U : F ≃ₗᵢ[ℂ] G) (J : E →ₗᵢ[ℂ] F) :
    (U.toLinearIsometry.comp J).toContinuousLinearMap.comp
        (U.toLinearIsometry.comp J).toContinuousLinearMap.adjoint =
      U.conjStarAlgEquiv (J.toContinuousLinearMap.comp J.toContinuousLinearMap.adjoint) := by
  change ((U : F →L[ℂ] G).comp J.toContinuousLinearMap).comp
    ((U : F →L[ℂ] G).comp J.toContinuousLinearMap).adjoint = _
  rw [ContinuousLinearMap.adjoint_comp, U.adjoint_eq_symm,
    LinearIsometryEquiv.conjStarAlgEquiv_apply]
  simp only [ContinuousLinearMap.comp_assoc]

variable {E F A : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [CStarAlgebra A]

theorem isometry_adjoint_apply (J : E →ₗᵢ[ℂ] F) (x : E) :
    J.toContinuousLinearMap.adjoint (J x) = x :=
  DFunLike.congr_fun J.adjoint_comp_self x

def isometricCompression (J : E →ₗᵢ[ℂ] F) (T : F →L[ℂ] F) : E →L[ℂ] E :=
  J.toContinuousLinearMap.adjoint.comp (T.comp J.toContinuousLinearMap)

theorem isometricCompression_intertwines (J : E →ₗᵢ[ℂ] F) (T : F →L[ℂ] F)
    (hT : T * (J.toContinuousLinearMap.comp J.toContinuousLinearMap.adjoint) =
      (J.toContinuousLinearMap.comp J.toContinuousLinearMap.adjoint) * T) (x : E) :
    J (isometricCompression J T x) = T (J x) := by
  have h := DFunLike.congr_fun hT (J x)
  change T (J (J.toContinuousLinearMap.adjoint (J x))) =
    J (J.toContinuousLinearMap.adjoint (T (J x))) at h
  rw [isometry_adjoint_apply] at h
  exact h.symm

def isometricRestriction (J : E →ₗᵢ[ℂ] F) (π : A →⋆ₐ[ℂ] (F →L[ℂ] F))
    (hπ : ∀ a, π a * (J.toContinuousLinearMap.comp J.toContinuousLinearMap.adjoint) =
      (J.toContinuousLinearMap.comp J.toContinuousLinearMap.adjoint) * π a) :
    A →⋆ₐ[ℂ] (E →L[ℂ] E) where
  toFun a := isometricCompression J (π a)
  map_zero' := by ext x; simp [isometricCompression]
  map_one' := by
    ext x
    change J.toContinuousLinearMap.adjoint (π 1 (J x)) = x
    rw [map_one]
    exact isometry_adjoint_apply J x
  map_add' a b := by ext x; simp [isometricCompression]
  map_mul' a b := by
    ext x
    have h := isometricCompression_intertwines J (π b) (hπ b) x
    change J.toContinuousLinearMap.adjoint (π (a * b) (J x)) =
      J.toContinuousLinearMap.adjoint (π a (J (isometricCompression J (π b) x)))
    rw [h, map_mul]
    rfl
  commutes' c := by
    ext x
    simp only [Algebra.algebraMap_eq_smul_one, map_smul, map_one]
    change J.toContinuousLinearMap.adjoint (c • J x) = c • x
    rw [map_smul, isometry_adjoint_apply]
  map_star' a := by
    change J.toContinuousLinearMap.adjoint.comp ((π (star a)).comp J.toContinuousLinearMap) =
      star (J.toContinuousLinearMap.adjoint.comp ((π a).comp J.toContinuousLinearMap))
    simp only [map_star, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.comp_assoc]

@[simp] theorem isometricRestriction_apply (J : E →ₗᵢ[ℂ] F)
    (π : A →⋆ₐ[ℂ] (F →L[ℂ] F))
    (hπ : ∀ a, π a * (J.toContinuousLinearMap.comp J.toContinuousLinearMap.adjoint) =
      (J.toContinuousLinearMap.comp J.toContinuousLinearMap.adjoint) * π a)
    (a : A) (x : E) :
    J (isometricRestriction J π hπ a x) = π a (J x) :=
  isometricCompression_intertwines J (π a) (hπ a) x

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixNearCommutant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Commutant estimates from individual matrix approximants

A matrix approximant from `N` commutes entrywise with a contraction in
`N′`. The complete commutator is therefore bounded by twice the matrix
error. The commutant distance formula gives distance at most
that error to `M′`; normalization costs a further factor two for unit balls.
No linear map selecting the matrix approximants is assumed.
-/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance matrixNearCommutantOrder : PartialOrder (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrder _
local instance matrixNearCommutantStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PartialSupportSpan
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! The projection onto the closed span of the initial spaces of a family
of partial isometries. All constructions remain in the original algebra. -/

namespace KadisonKastler

noncomputable section

open Generator Generator.Tracial

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

def partialSupportVectors (S : Set (PartialIsometry M)) : Set H :=
  {y | ∃ v ∈ S, ∃ ξ, y = (v.support.val : H →L[ℂ] H) ξ}

def partialSupportSpace (S : Set (PartialIsometry M)) : Submodule ℂ H :=
  (Submodule.span ℂ (partialSupportVectors S)).topologicalClosure

instance partialSupportSpace_complete (S : Set (PartialIsometry M)) :
    CompleteSpace (partialSupportSpace S) :=
  inferInstanceAs (CompleteSpace (Submodule.span ℂ (partialSupportVectors S)).topologicalClosure)

theorem partialSupportProjection_mem (S : Set (PartialIsometry M)) :
    (partialSupportSpace S).starProjection ∈ M := by
  apply (VonNeumannAlgebra.IsStarProjection.mem_iff isStarProjection_starProjection M).mpr
  intro T hT
  rw [Submodule.range_starProjection]
  have hinv : partialSupportSpace S ≤ (partialSupportSpace S).comap T.toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro y ⟨v, hv, ξ, rfl⟩
      apply Submodule.le_topologicalClosure
      apply Submodule.subset_span
      refine ⟨v, hv, T ξ, ?_⟩
      have hc := VonNeumannAlgebra.mem_commutant_iff.mp hT v.support.val.val
        v.support.val.property
      exact (congrArg (fun A : H →L[ℂ] H => A ξ) hc).symm
    · exact (Submodule.isClosed_topologicalClosure _).preimage T.continuous
  exact fun y hy => hinv hy

def partialSupportProjection (S : Set (PartialIsometry M)) : AlgebraProjection M :=
  ⟨⟨(partialSupportSpace S).starProjection, partialSupportProjection_mem S⟩, by
    constructor
    · apply Subtype.ext
      exact (isStarProjection_starProjection (U := partialSupportSpace S)).isIdempotentElem.eq
    · apply Subtype.ext
      exact (isStarProjection_starProjection (U := partialSupportSpace S)).isSelfAdjoint.star_eq⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PartitionSignAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 0

namespace OAI

/-! # The sign average of a finite projection partition -/

namespace KadisonKastler

open Generator.Tracial
open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance partitionOperatorNNRat : Module ℚ≥0 (H →L[ℂ] H) :=
  Module.compHom (H →L[ℂ] H) (algebraMap ℚ≥0 ℂ)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PartitionProjectionGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # One projection retains a finite pinching gap

This is the finite sign-averaging argument in Haagerup, Acta Math. 158
(1987), Lemma 2.16. The reference error is bounded uniformly over all signs.
-/

namespace KadisonKastler

open Generator.Tracial
open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance projectionOperatorNNRat : Module ℚ≥0 (H →L[ℂ] H) :=
  Module.compHom (H →L[ℂ] H) (algebraMap ℚ≥0 ℂ)

local instance projectionVectorNNRat : Module ℚ≥0 H :=
  Module.compHom H (algebraMap ℚ≥0 ℂ)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProjectionReflectionOrbit
attribute [-instance] _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 0

namespace OAI

/-! # A reflection exchanges projection defects for vector distance

At the sum of two vectors the defect is the error term; at their difference
it is the improvement term. This is the quantitative step for state orbits.
-/

namespace KadisonKastler
open Generator.Tracial
noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

local instance reflectionOrbitReal : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

end
end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_UniformProjectionGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Uniform projection witnesses from modular coisometries -/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

local instance uniformGapRealInner : InnerProductSpace ℝ H := InnerProductSpace.complexToReal

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PositiveOrbitContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A uniform contraction in the orbit of positive unit vectors -/

namespace KadisonKastler
open Generator.Tracial NormedSpace
noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

local instance positiveOrbitContractionReal : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

end
end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PositiveOrbitDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Vanishing distance between positive unitary orbits

The uniform contraction forces the infimum of squared orbit distances to
vanish. Only the modular coisometries of the concrete product are used.
-/

namespace KadisonKastler
open Generator.Tracial
noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

local instance positiveOrbitDensityReal : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

end
end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProjectionCentralScalar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Projection centrality forces scalar vectors -/

namespace KadisonKastler

open Generator.Tracial NormedSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

local instance projectionScalarRealInner : InnerProductSpace ℝ H := InnerProductSpace.complexToReal

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RandomWalkShiftLaw
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Independence of the first increment and the remaining random walk -/

namespace KadisonKastler

noncomputable section

open MeasureTheory ProbabilityTheory

variable {G : Type*} [MeasurableSpace G]

theorem independent_first_increment_tail (μ : Measure G) [IsProbabilityMeasure μ] :
    IndepFun (fun x : ℕ → G => x 0) (fun x : ℕ → G => fun n => x (n + 1))
      (Measure.infinitePi (fun _ : ℕ => μ)) := by
  let m : ℕ → MeasurableSpace (ℕ → G) := fun n =>
    MeasurableSpace.comap (fun x => x n) inferInstance
  have hi : iIndep m (Measure.infinitePi (fun _ : ℕ => μ)) :=
    iIndepFun_infinitePi (X := fun _ (x : G) => x) (fun _ => measurable_id)
  have hm (n : ℕ) : m n ≤ (inferInstance : MeasurableSpace (ℕ → G)) :=
    (measurable_pi_apply n).comap_le
  have hh := indep_iSup_of_disjoint hm hi
    (show Disjoint ({0} : Set ℕ) {n | n ≠ 0} by simp)
  have hleft : m 0 ≤ ⨆ n ∈ ({0} : Set ℕ), m n :=
    le_iSup_of_le 0 (le_iSup_of_le (Set.mem_singleton 0) le_rfl)
  have hright : MeasurableSpace.comap (fun x : ℕ → G => fun n => x (n + 1)) inferInstance ≤
      ⨆ n ∈ {n : ℕ | n ≠ 0}, m n := by
    rw [MeasurableSpace.comap_process_pi]
    apply iSup_le
    intro n
    exact le_iSup_of_le (n + 1) (le_iSup_of_le (by change n + 1 ≠ 0; omega) le_rfl)
  exact indep_of_indep_of_le_right (indep_of_indep_of_le_left hh hleft) hright

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RectangularWeakCompact
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! Weak operator compactness for the rectangular operators in a fixed
factorization. The source and target Hilbert spaces may differ. -/

namespace KadisonKastler

noncomputable section

open Filter
open scoped Topology InnerProductSpace

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def weakRectangularBall (H K : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] (d : ℝ) : Set (H →WOT[ℂ] K) :=
  {R | ‖R.toCLM‖ ≤ d}

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RowOperatorFactorization
attribute [-instance] _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! Operator factorizations and their exact behavior under finite row averages.
The representation is supplied by the proved Paulsen--Stinespring construction.
-/

namespace KadisonKastler

noncomputable section

open scoped InnerProductSpace
open BoundedHochschild.KadisonRingrose

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

local instance rowFactorOperatorOrder : PartialOrder (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrder _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RowRepresentationContraction
attribute [-instance] _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! The representation-side row action preserves the factorization bound. -/

namespace KadisonKastler

noncomputable section

open Generator
open scoped InnerProductSpace

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

local instance rowRepOrder : PartialOrder (K →L[ℂ] K) := CStarAlgebra.spectralOrder _
local instance rowRepStarOrder : StarOrderedRing (K →L[ℂ] K) :=
  CStarAlgebra.spectralOrderedRing _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SeparableReducingSpace
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A separable reducing subspace containing finitely many vectors

The closed complex span of the algebra orbits of a finite vector family
is separable when the algebra is norm separable. It is invariant under
the algebra and its adjoints, so its orthogonal projection commutes with
every element of the algebra.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def finiteAlgebraOrbit (A : StarSubalgebra ℂ (H →L[ℂ] H)) (V : Finset H) : Set H :=
  Set.range (fun p : A × V => (p.1 : H →L[ℂ] H) (p.2 : H))

def finiteReducingSpace (A : StarSubalgebra ℂ (H →L[ℂ] H)) (V : Finset H) :
    Submodule ℂ H :=
  (Submodule.span ℂ (finiteAlgebraOrbit A V)).topologicalClosure

instance finiteReducingSpaceComplete (A : StarSubalgebra ℂ (H →L[ℂ] H))
    (V : Finset H) : CompleteSpace (finiteReducingSpace A V) :=
  inferInstanceAs (CompleteSpace (Submodule.span ℂ (finiteAlgebraOrbit A V)).topologicalClosure)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SignedFunctionalCompression
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Compression identities for signed vector functionals -/

namespace KadisonKastler

noncomputable section

open HochschildNormalPart
open scoped InnerProductSpace

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def signedVectorFunctional (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (S : H →L[ℂ] H) (ξ : H) :
    A →L[ℂ] ℂ := coefficient π (S ξ) ξ

@[simp] theorem signedVectorFunctional_apply (π : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (S : H →L[ℂ] H) (ξ : H) (a : A) :
    signedVectorFunctional π S ξ a = inner ℂ (S ξ) (π a ξ) := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SpatialMatrixAmplification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Finite matrix amplification of spatial matrix images

Finite matrices over a generated operator algebra generate the matrix
von Neumann algebra.  The proof uses the existing strong approximation
theorem entry by entry.  Flattening the two finite matrix indices then
preserves the complete unit-ball approximation constant.
-/

namespace KadisonKastler

open Generator Filter
open scoped Topology BigOperators

noncomputable section

universe u

variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance spatialAmplificationOrder : PartialOrder (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrder _
local instance spatialAmplificationStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SpatialCompleteGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Complete proximity of spatial products with matrix-generated factors

The finite-stage approximants retain all matrix levels.  Kaplansky
density and weak compactness extend the same bound to the spatial
products.  Only the original complete proximity hypothesis is used.
-/

namespace KadisonKastler

open Generator Filter
open scoped Topology BigOperators

noncomputable section

universe u

variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [Nontrivial K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]

local instance spatialCompleteOrder : PartialOrder (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrder _
local instance spatialCompleteStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SpatialTensorDescent
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Removing the auxiliary spatial tensor factor

A concrete unit vector slice removes the auxiliary factor. Thus an upstairs
unitary yields an original-space unitary with the explicit UCP descent bound.
-/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

local instance tensorDescentOrder {J : Type*} [NormedAddCommGroup J]
    [InnerProductSpace ℂ J] [CompleteSpace J] : PartialOrder (J →L[ℂ] J) :=
  CStarAlgebra.spectralOrder _
local instance tensorDescentStarOrder {J : Type*} [NormedAddCommGroup J]
    [InnerProductSpace ℂ J] [CompleteSpace J] : StarOrderedRing (J →L[ℂ] J) :=
  CStarAlgebra.spectralOrderedRing _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SpatialTensorModulus
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Quantitative removal of a fixed auxiliary factor -/

namespace KadisonKastler

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The auxiliary tolerance used before choosing any representation or algebra. -/
def spatialDescentTolerance (ε : ℝ) : ℝ := min (ε / 512) (1 / 4000)

end

end KadisonKastler

end OAI
end


