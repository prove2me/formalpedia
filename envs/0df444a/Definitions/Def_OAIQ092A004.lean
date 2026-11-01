-- Prove2me | Definitions.Def_OAIQ092A004
-- name    : OAIQ092A004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T19:50:49.58958+00:00
-- url     : https://prove2.me/theorems/3c666a11-cf8d-495e-a84e-0a64ed41f5ad
-- title:
--   Definitions bundle OAIQ092A004 of the split of OpenAI, QMA-hardness of continuum Coulomb energy (result family 275)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ContinuumCoulomb.binary_coulomb_qmaHard` and `OAI.ContinuumCoulomb.unit_coulomb_qmaHard`, carved from OpenAI's openai/math development (OpenAI, *QMA-hardness of continuum Coulomb energy (result family 275)*, OpenAI Math Release, September 24, 2026, result family 275, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1113 declarations of OpenAI's Lean: 988 definitions and 125 theorems. The definitions and types are `OAI.ContinuumCoulomb.AffinePhysicalOutput.argumentProgram`, `OAI.ContinuumCoulomb.AffinePhysicalOutput.program`, `OAI.ContinuumCoulomb.AffinePhysicalOutput.value`, `OAI.ContinuumCoulomb.AffinePhysicalThreshold.argumentProgram`, `OAI.ContinuumCoulomb.AffinePhysicalThreshold.exactFinite`, `OAI.ContinuumCoulomb.AffinePhysicalThreshold.exactValue`, `OAI.ContinuumCoulomb.AffinePhysicalThreshold.finiteProgram`, `OAI.ContinuumCoulomb.AffinePhysicalThreshold.geometryProgram`, `OAI.ContinuumCoulomb.AffinePhysicalThreshold.pairProgram`, `OAI.ContinuumCoulomb.AffinePhysicalThreshold.program`, `OAI.ContinuumCoulomb.AffinePhysicalThreshold.tauProgram`, `OAI.ContinuumCoulomb.AffinePhysicalThreshold.weightsProgram`, `OAI.ContinuumCoulomb.AutomaticCalibration.argumentProgram`, `OAI.ContinuumCoulomb.AutomaticCalibration.baseProgram`, `OAI.ContinuumCoulomb.AutomaticCalibration.coefficientProgram`, `OAI.ContinuumCoulomb.AutomaticCalibration.environmentProgram`, `OAI.ContinuumCoulomb.AutomaticCalibration.inputCode`, `OAI.ContinuumCoulomb.AutomaticCalibration.intervalProgram`, `OAI.ContinuumCoulomb.AutomaticCalibration.normalizedProgram`, `OAI.ContinuumCoulomb.AutomaticCalibration.normalizedValue`, `OAI.ContinuumCoulomb.AutomaticCalibration.precisionProgram`, `OAI.ContinuumCoulomb.AutomaticCalibration.program`, `OAI.ContinuumCoulomb.AutomaticCalibration.queryProgram`, `OAI.ContinuumCoulomb.AutomaticCalibration.scaleProgram`, `OAI.ContinuumCoulomb.AutomaticCalibration.scaledSizeProgram`, `OAI.ContinuumCoulomb.AutomaticCalibration.spacingProgram`, `OAI.ContinuumCoulomb.AutomaticCalibration.tailProgram`, `OAI.ContinuumCoulomb.AutomaticCalibration.targetScaleProgram`, `OAI.ContinuumCoulomb.AutomaticCalibration.unaryPowerProgram`, `OAI.ContinuumCoulomb.AutomaticCalibration.value`, `OAI.ContinuumCoulomb.AutomaticCalibrationList.elementProgram`, `OAI.ContinuumCoulomb.AutomaticCalibrationList.environmentCode`, `OAI.ContinuumCoulomb.AutomaticCalibrationList.inputCode`, `OAI.ContinuumCoulomb.AutomaticCalibrationList.program`, `OAI.ContinuumCoulomb.AutomaticCalibrationList.value`, `OAI.ContinuumCoulomb.BisectionProgram.advanceProgram`, `OAI.ContinuumCoulomb.BisectionProgram.configCode`, `OAI.ContinuumCoulomb.BisectionProgram.initialProgram`, `OAI.ContinuumCoulomb.BisectionProgram.inputCode`, `OAI.ContinuumCoulomb.BisectionProgram.middleProgram` and 948 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, lean/OAI/Computability, lean/OAI/MathematicalPhysics, in whole or in part: `Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Smoothing`, `ContinuumCoulomb_ManyBody_MediatorIteration`, `ContinuumCoulomb_ManyBody_MediatorParameters`, `ContinuumCoulomb_Nuclei_EulerInitialBox`, `ContinuumCoulomb_Nuclei_EulerRegisters`, `ContinuumCoulomb_Nuclei_EulerTrajectory`, `ContinuumCoulomb_Nuclei_MoserDifferenceBudget`, `ContinuumCoulomb_Nuclei_NuclearCoordinateOutput`, `ContinuumCoulomb_Nuclei_SlabOriginValue`, `ContinuumCoulomb_OneParticle_AffinePhysicalOutput`, `ContinuumCoulomb_OneParticle_AffinePhysicalThreshold`, `ContinuumCoulomb_OneParticle_CalibratedBisection`, `ContinuumCoulomb_OneParticle_CalibratedBisectionMachine`, `ContinuumCoulomb_OneParticle_CalibratedBisectionSchedule`, `ContinuumCoulomb_OneParticle_CalibratedContactCorrectness`, `ContinuumCoulomb_OneParticle_CalibratedEvaluationComponents`, `ContinuumCoulomb_OneParticle_CalibratedEvaluationParameters`, `ContinuumCoulomb_OneParticle_CalibratedLipschitzBound`, `ContinuumCoulomb_OneParticle_CenteredGaussEquiv`, `ContinuumCoulomb_OneParticle_CenteredGaussLabels`, `ContinuumCoulomb_OneParticle_CenteredPhysicalThreshold`, `ContinuumCoulomb_OneParticle_ContactCalibratedGeometry`, `ContinuumCoulomb_OneParticle_ContactClosedCoordinates`, `ContinuumCoulomb_OneParticle_ContactGlobalSeparation`, `ContinuumCoulomb_OneParticle_ContactHeightBisection`, `ContinuumCoulomb_OneParticle_ContactHeightEvaluation`, `ContinuumCoulomb_OneParticle_ContactQuotientBounds`, `ContinuumCoulomb_OneParticle_ContactRationalCoordinates`, `ContinuumCoulomb_OneParticle_ContactRationalGadget`, `ContinuumCoulomb_OneParticle_ContactRationalGlobal`, `ContinuumCoulomb_OneParticle_ContactRationalLocal`, `ContinuumCoulomb_OneParticle_CoulombCalibration`, `ContinuumCoulomb_OneParticle_CoulombPacketTests`, `ContinuumCoulomb_OneParticle_CoulombPairSum`, `ContinuumCoulomb_OneParticle_CoulombTargetLipschitz`, `ContinuumCoulomb_OneParticle_CoulombTruncationSchedule`, `ContinuumCoulomb_OneParticle_CountertermEvaluation`, `ContinuumCoulomb_OneParticle_HoppingQuadrature`, `ContinuumCoulomb_OneParticle_HoppingSchedule`, `ContinuumCoulomb_OneParticle_LocalizedCoulomb`, `ContinuumCoulomb_OneParticle_LocalizedCoulombTranslation`, `ContinuumCoulomb_OneParticle_LocalizedDualMatrix`, `ContinuumCoulomb_OneParticle_LocalizedFourIndex`, `ContinuumCoulomb_OneParticle_LocalizedGram`, `ContinuumCoulomb_OneParticle_LocalizedGramConstants`, `ContinuumCoulomb_OneParticle_ManufacturedEuler`, `ContinuumCoulomb_OneParticle_ManufacturedFieldBounds`, `ContinuumCoulomb_OneParticle_ManufacturedFieldEvaluation`, `ContinuumCoulomb_OneParticle_ManufacturedVelocityEvaluation`, `ContinuumCoulomb_OneParticle_NormalizationArithmetic`, `ContinuumCoulomb_OneParticle_NormalizationQuadrature`, `ContinuumCoulomb_OneParticle_PlanarFieldBounds`, `ContinuumCoulomb_OneParticle_PlanarForcing`, `ContinuumCoulomb_OneParticle_PlanarGroundTransform`, `ContinuumCoulomb_OneParticle_PlanarHeatKernel`, `ContinuumCoulomb_OneParticle_PlanarHopping`, `ContinuumCoulomb_OneParticle_PlanarModeProperties`, `ContinuumCoulomb_OneParticle_PlanarResolvent`, `ContinuumCoulomb_OneParticle_PlanarWellNumerics`, `ContinuumCoulomb_OneParticle_RationalBoxRound`, `ContinuumCoulomb_OneParticle_RationalClamp`, `ContinuumCoulomb_OneParticle_RationalFieldDifferences`, `ContinuumCoulomb_OneParticle_RationalGaussNodes`, `ContinuumCoulomb_OneParticle_RationalHeatBox`, `ContinuumCoulomb_OneParticle_RationalHeatSample`, `ContinuumCoulomb_OneParticle_RationalSixQuadrature`, `ContinuumCoulomb_OneParticle_RationalSmoothTransition`, `ContinuumCoulomb_OneParticle_RationalSquareRoot`, `ContinuumCoulomb_OneParticle_RationalTaylorRegisters`, `ContinuumCoulomb_OneParticle_RationalTripleQuadrature`, `ContinuumCoulomb_OneParticle_ResolventSchedule`, `ContinuumCoulomb_OneParticle_TransformedGauss`, `ContinuumCoulomb_OneParticle_TransformedGaussList`, `ContinuumCoulomb_Programs_AffinePhysicalThresholdProgram`, `ContinuumCoulomb_Programs_AmplificationProgram`, `ContinuumCoulomb_Programs_AutomaticCalibrationProgram`, `ContinuumCoulomb_Programs_BisectionProgram`, `ContinuumCoulomb_Programs_BisectionRegisters`, `ContinuumCoulomb_Programs_CalibratedBisectionProgram`, `ContinuumCoulomb_Programs_CalibratedContactProgram`, `ContinuumCoulomb_Programs_CalibratedEvaluationProgram`, `ContinuumCoulomb_Programs_CalibrationRationalBracketProgram`, `ContinuumCoulomb_Programs_CappedKernelProgram`, `ContinuumCoulomb_Programs_CenteredGaussProgram`, `ContinuumCoulomb_Programs_CenteredNuclearProgram`, `ContinuumCoulomb_Programs_CenteredPhysicalThresholdProgram`, `ContinuumCoulomb_Programs_ChargePrograms`, `ContinuumCoulomb_Programs_ContactCanonicalEdgeProgram`, `ContinuumCoulomb_Programs_ContactEdgeNumberProgram`, `ContinuumCoulomb_Programs_ContactGeometryBlockProgram`, `ContinuumCoulomb_Programs_ContactHeightProgram`, `ContinuumCoulomb_Programs_ContactHeightScheduleProgram`, `ContinuumCoulomb_Programs_ContactLocalInputProgram`, `ContinuumCoulomb_Programs_ContactPlacedGadgetProgram`, `ContinuumCoulomb_Programs_ContactRationalGadgetProgram`, `ContinuumCoulomb_Programs_ContactRationalPlaceProgram`, `ContinuumCoulomb_Programs_ContactSourceInputProgram`, `ContinuumCoulomb_Programs_ContactVertexProgram`, `ContinuumCoulomb_Programs_CoulombEvaluationProgram`, `ContinuumCoulomb_Programs_CoulombNormalizationProgram`, `ContinuumCoulomb_Programs_CoulombPairProgram`, `ContinuumCoulomb_Programs_CoulombPairSumProgram`, `ContinuumCoulomb_Programs_CountertermProgram`, `ContinuumCoulomb_Programs_DyadicRootProgram`, `ContinuumCoulomb_Programs_EncodingPrograms`, `ContinuumCoulomb_Programs_EnumeratedGridNuclei`, `ContinuumCoulomb_Programs_EulerProgram`, `ContinuumCoulomb_Programs_EulerVectorPrograms`, `ContinuumCoulomb_Programs_FiniteDifferenceProgram`, `ContinuumCoulomb_Programs_GaussNodeProgram`, `ContinuumCoulomb_Programs_GaussianFrequencyProgram`, `ContinuumCoulomb_Programs_GaussianPacketProgram`, `ContinuumCoulomb_Programs_HoppingProgram`, `ContinuumCoulomb_Programs_ManufacturedFieldProgram`, `ContinuumCoulomb_Programs_ManufacturedVelocityProgram`, `ContinuumCoulomb_Programs_MediatorListProgram`, `ContinuumCoulomb_Programs_MoserCoordinateProgram`, `ContinuumCoulomb_Programs_MoserDifferenceProgram`, `ContinuumCoulomb_Programs_NormalizationProgram`, `ContinuumCoulomb_Programs_PhysicalNuclearProgram`, `ContinuumCoulomb_Programs_PiProgram`, `ContinuumCoulomb_Programs_PlanarForcingProgram`, `ContinuumCoulomb_Programs_PlanarWellProgram`, `ContinuumCoulomb_Programs_PrefixListPrograms`, `ContinuumCoulomb_Programs_PrefixPrograms`, `ContinuumCoulomb_Programs_RationalExponentialProgram`, `ContinuumCoulomb_Programs_RationalLogScaleProgram`, `ContinuumCoulomb_Programs_RationalQuadratureProgram`, `ContinuumCoulomb_Programs_RationalRectangleProgram`, `ContinuumCoulomb_Programs_RationalSumProgram`, `ContinuumCoulomb_Programs_RawCoulombSampleProgram`, `ContinuumCoulomb_Programs_RawDensitySampleProgram`, `ContinuumCoulomb_Programs_SlabBoxProgram`, `ContinuumCoulomb_Programs_SlabOriginProgram`, `ContinuumCoulomb_Programs_SmoothTransitionProgram`, `ContinuumCoulomb_Programs_SourceMetadataProgram`, `ContinuumCoulomb_Programs_SourceNormalizationProgram`, `ContinuumCoulomb_Programs_SourcePrograms`, `ContinuumCoulomb_Programs_SquareRootProgram`, `ContinuumCoulomb_Programs_TransformedGaussProgram`, `ContinuumCoulomb_Programs_UnitCoulombProgram`, `ContinuumCoulomb_Programs_VerticalCutoffProgram`, `ContinuumCoulomb_Reduction_AutomaticCalibrationList`, `ContinuumCoulomb_Reduction_AutomaticCalibrationNormalization`, `ContinuumCoulomb_Reduction_AutomaticCalibrationParameters`, `ContinuumCoulomb_Reduction_ComputableHopping`, `CoulombRadii_FieldAnalysis_CoulombTest`, `CoulombRadii_Packets_CoulombKernel`, `CoulombRadii_Variational_Axis`, `CoulombRadii_Variational_WeakLaplacian`, `QuantumFactoring_BitStackAdder`, `QuantumFactoring_BitStackBooleans`, `QuantumFactoring_BitStackConstants`, `QuantumFactoring_BitStackDependentChoice`, `QuantumFactoring_BitStackIntegers`, `QuantumFactoring_BitStackListCode`, `QuantumFactoring_BitStackListFold`, `QuantumFactoring_BitStackListIndex`, `QuantumFactoring_BitStackListMapWith`, `QuantumFactoring_BitStackListOps`, `QuantumFactoring_BitStackListWords`, `QuantumFactoring_BitStackMultiplier`, `QuantumFactoring_BitStackPowers`, `QuantumFactoring_BitStackPrograms`, `QuantumFactoring_BitStackRationalDivision`, `QuantumFactoring_BitStackRationalFloor`, `QuantumFactoring_BitStackRationals`, `QuantumFactoring_BitStackTabulate`, `QuantumFactoring_BitStackUnary`, `QuantumFactoring_BitStackWords`.
--
--   **Imports.** It imports the published bundle `Def_ContinuumCoulombHardness`; the bundles `OAIQ092A000` and `OAIQ092A001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ092A008`, `OAIQ092A009` and `OAIQ092A011`; the statements `OAI.ContinuumCoulomb.CalibratedEvaluation.scheduled_residual`, `OAI.ContinuumCoulomb.ContactCalibratedGeometry.calibrated_edge_residual`, `OAI_ContinuumCoulomb_ContactCalibratedGeometry_nonedge_separation` and `OAI.ContinuumCoulomb.ContactCalibratedGeometry.separation`; the proof of `OAI_ContinuumCoulomb_CoulombNormalization_approximation_error`.
-- source:
--   OpenAI, QMA-hardness of continuum Coulomb energy (result family 275), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 275; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Continuum-Coulomb-hardness-with-binary-nuclear-charges-September-24-2026/Continuum-Coulomb-hardness-with-binary-nuclear-charges-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis, lean/OAI/Computability, lean/OAI/MathematicalPhysics at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Round
import Mathlib.Algebra.Ring.Int.Units
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.EReal.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Set
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Order.Fin.Basic
import Mathlib.Order.Hom.PowersetCard
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Moments.Variance
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.Antilipschitz
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_ContinuumCoulombHardness
import Definitions.Def_OAIQ092A000
import Definitions.Def_OAIQ092A001

section
-- module Solutions.OAIQ092_CC.Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Smoothing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

/-!
# `L²` compactness criterion: smoothing setup (Euclidean)

This file provides the basic “extend by zero + smooth by convolution” infrastructure used in the
Fréchet–Kolmogorov / Riesz–Kolmogorov approach to Euclidean Rellich–Kondrachov.

## Main results

- `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.extendByZeroL2`:
  extend `u : L²(volume.restrict K)` by zero to an element of `L²(volume)`.
- `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.smoothL2`:
  a smoothing operator obtained by convolution with a compactly supported continuous kernel `ψ`.
-/

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean
namespace L2Compactness

open scoped ENNReal MeasureTheory Topology Convolution Pointwise
open MeasureTheory Set

noncomputable section

section Volume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instMeasurableSpace_solutions_1
local instance instBorelSpace_solutions_1 : BorelSpace E := ⟨rfl⟩
end Volume

end

end L2Compactness
end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_BitStackPrograms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

/-! A literal finite Boolean-stack compiler for circuit descriptions.
Branches inspect and consume one symbol, not an entire encoded word.
Operational derivations below count actual finite-state TM2 transitions.
-/
namespace ExactQuantumFactoring.BitStackProgram
open Turing.TM2 StateTransition

def Node {K : Type} : Program K → Type
  | .skip | .push _ _ => Unit
  | .seq p q => Node p ⊕ Node q
  | .cases _ a b c => Unit ⊕ (Node a ⊕ (Node b ⊕ Node c))
  | .loop _ b c => Unit ⊕ (Node b ⊕ Node c)

def entry {K : Type} : (p : Program K) → Node p
  | .skip | .push _ _ => ()
  | .seq p _ => .inl (entry p)
  | .cases _ _ _ _ | .loop _ _ _ => .inl ()

def configured {K Λ : Type} (l : Λ) (s : Store K) : Config K Λ := ⟨some l,none,s⟩
end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_BitStackConstants
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ExactQuantumFactoring.BitStackProgram.sumStore_left _root_.OAI.ExactQuantumFactoring.BitStackProgram.sumStore_right _root_.OAI.ExactQuantumFactoring.BitStackProgram.sumStore_update_left _root_.OAI.ExactQuantumFactoring.BitStackProgram.sumStore_update_right _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {K : Type} [DecidableEq K]
namespace Procedure
variable {α β : Type} (ea : α→List Bool) (eb : β→List Bool)

noncomputable def quote (ea : α→List Bool) : Procedure ea (fun a=>quoteBits (ea a)) id where
  K:=Fin 3
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=0
  output:=1
  program:=quoteMove 0 1 2
  bound:=Polynomial.C 7*Polynomial.X+Polynomial.C 5
  runs a:=by
    have hh:=quoteMove_runs (0 : Fin 3) 1 2 (by decide) (by decide) (by decide)
      (singletonStore 0 (ea a)) (by simp [singletonStore])
    refine ⟨7*(ea a).length+5,by simp,?_⟩
    convert hh using 1
    · funext k; fin_cases k <;> simp [singletonStore,Function.update]
    · simp [singletonStore]

end Procedure
end ExactQuantumFactoring.BitStackProgram

end


end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_BitStackWords
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
namespace Procedure
variable {α : Type}

noncomputable def append : Procedure (prodCode (id : List Bool→List Bool) id) id
    (fun x=>x.1++x.2) where
  K:=Fin 4
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=0
  output:=0
  program:=.seq (unquoteMove 0 1 2 3) (.seq (reverseMove 1 2) (reverseMove 2 0))
  bound:=Polynomial.C 11*Polynomial.X+Polynomial.C 8
  runs x:=by
    let s : Store (Fin 4):=singletonStore 0 (prodCode id id x)
    let u : Store (Fin 4):=Function.update (singletonStore 0 x.2) 1 x.1
    let v : Store (Fin 4):=Function.update (singletonStore 0 x.2) 2 x.1.reverse
    have h1 : Runs (unquoteMove 0 1 2 3) s u (7*x.1.length+6):=by
      have hh:=unquoteMove_runs (0 : Fin 4) 1 2 3 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) x.1 x.2 s
        (by simp [s,singletonStore,prodCode,pairBits])
        (by simp [s,singletonStore]) (by simp [s,singletonStore])
      convert hh using 1
      all_goals try with_reducible_and_instances rfl
      funext k;fin_cases k <;> simp [s,u,singletonStore,Function.update]
    have h2 : Runs (reverseMove 1 2) u v (2*x.1.length+1):=by
      have hh:=reverseMove_runs (1 : Fin 4) 2 (by decide) u
      convert hh using 1
      · funext k;fin_cases k <;> simp [u,v,singletonStore,Function.update]
      · simp [u]
    have h3 : Runs (reverseMove 2 0) v (singletonStore 0 (x.1++x.2)) (2*x.1.length+1):=by
      have hh:=reverseMove_runs (2 : Fin 4) 0 (by decide) v
      convert hh using 1
      · funext k;fin_cases k <;> simp [v,singletonStore,Function.update]
      · simp [v]
    refine ⟨(2*x.1.length+1)+(2*x.1.length+1)+(7*x.1.length+6),?_,
      Runs.seq h1 (Runs.seq h2 h3)⟩
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,
      prodCode,pairBits_length,id_eq]
    omega
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_BitStackBooleans
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram.Procedure
variable {β : Type}

noncomputable def boolXor : Procedure (prodCode boolCode boolCode) boolCode
    (fun x=>xor x.1 x.2) := ofBool₂ boolCode xor

end ExactQuantumFactoring.BitStackProgram.Procedure

end



end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_BitStackUnary
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram

namespace Procedure

noncomputable def unaryPred : Procedure unaryCode unaryCode (fun n=>n-1) :=
  (tail.precompose unaryCode).result (by intro n;simp [unaryCode])

noncomputable def unaryZero : Procedure unaryCode boolCode (fun n=>decide (n=0)) :=
  (isEmpty.precompose unaryCode).congrFun (by intro n;simp [unaryCode])

end Procedure
end ExactQuantumFactoring.BitStackProgram

end


end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_BitStackAdder
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram

lemma addMeasure_step (s : AddState) : addMeasure (addStep s)≤addMeasure s-1 := by
  rcases s with ⟨xs,ys,c,zs⟩
  cases xs with
  | nil=>cases ys with
    | nil=>cases c <;> simp [addMeasure,addStep,carryBit]
    | cons b bs=>cases b <;> cases c <;> simp [addMeasure,addStep,carryBit]
  | cons a as=>cases ys with
    | nil=>cases a <;> cases c <;> simp [addMeasure,addStep,carryBit]
    | cons b bs=>cases a <;> cases b <;> cases c <;>
        simp [addMeasure,addStep,carryBit] <;> omega

lemma addMeasure_iterate (i : ℕ) (s : AddState) :
    addMeasure (addStep^[i] s)≤addMeasure s-i := by
  induction i with
  | zero=>simp
  | succ i ih=>
    rw [Function.iterate_succ_apply']
    exact (addMeasure_step _).trans (by omega)

lemma residual_zero {s : AddState} (h : addMeasure s=0) : residual s=0 := by
  have hx : s.1=[]:=List.length_eq_zero_iff.mp (by unfold addMeasure at h;omega)
  have hy : s.2.1=[]:=List.length_eq_zero_iff.mp (by unfold addMeasure at h;omega)
  have hc : s.2.2.1.toNat=0:=by unfold addMeasure at h;omega
  simp [residual,hx,hy,hc,binaryValue]

lemma wordAdd_value (x : List Bool×List Bool) :
    binaryValue (wordAdd x)=binaryValue x.1+binaryValue x.2 := by
  let s : AddState:=(x.1,x.2,false,[])
  let i:=x.1.length+x.2.length+1
  have hz : addMeasure (addStep^[i] s)=0:=by
    have hh:=addMeasure_iterate i s
    simp only [s,i,addMeasure,Bool.toNat_false,Nat.add_zero] at hh
    dsimp only [s,i,addMeasure]
    omega
  have hh:=addInvariant_iterate i s
  simp only [addInvariant,residual_zero hz,Nat.mul_zero,Nat.add_zero] at hh
  simpa [s,i,wordAdd,residual,binaryValue] using hh

namespace Procedure
variable {α : Type} {ea : α→List Bool} {f : α→α}

noncomputable def binaryAdd : Procedure (prodCode Nat.bits Nat.bits) Nat.bits
    (fun x=>x.1+x.2) :=
  ((normalize.comp wordAddP).precompose (fun x : ℕ×ℕ=>(x.1.bits,x.2.bits))).congrFun
    (by
      intro x
      change binaryValue (wordAdd (x.1.bits,x.2.bits))=x.1+x.2
      rw [wordAdd_value,binaryValue_bits,binaryValue_bits])

end Procedure
end ExactQuantumFactoring.BitStackProgram

end


end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_BitStackMultiplier
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram

lemma bits_length_value (xs : List Bool) : (binaryValue xs).bits.length≤xs.length := by
  rw [Nat.size_eq_bits_len,Nat.size_le]
  exact binaryValue_lt xs

lemma mul_fold (xs : List Bool) (x : ℕ×ℕ) :
    xs.foldl (bitAction mulZeroStep mulOneStep) x=
      (x.1,x.1*binaryValue xs.reverse+2^xs.length*x.2) := by
  induction xs generalizing x with
  | nil=>simp [binaryValue]
  | cons b bs ih=>
    rw [List.foldl_cons,ih]
    simp only [List.reverse_cons,binaryValue_append,List.length_reverse,List.length_cons,
      binaryValue,pow_succ]
    cases b <;> simp [bitAction,mulZeroStep,mulOneStep] <;> ring

namespace Procedure
noncomputable def mulZeroStepP : Procedure (prodCode Nat.bits Nat.bits)
    (prodCode Nat.bits Nat.bits) mulZeroStep :=
  ((first Nat.bits Nat.bits).pair (double.comp (second Nat.bits Nat.bits))).congrFun (by intro x;rfl)
noncomputable def mulOneStepP : Procedure (prodCode Nat.bits Nat.bits)
    (prodCode Nat.bits Nat.bits) mulOneStep := by
  let first:=first Nat.bits Nat.bits
  let second:=second Nat.bits Nat.bits
  exact (first.pair (binaryAdd.comp ((double.comp second).pair first))).congrFun (by intro x;rfl)

noncomputable def mulFoldP : Procedure (prodCode id (prodCode Nat.bits Nat.bits))
    (prodCode Nat.bits Nat.bits) (fun x=>x.1.foldl (bitAction mulZeroStep mulOneStep) x.2) :=
  foldBits mulZeroStepP mulOneStepP (Polynomial.C 3*Polynomial.X+Polynomial.C 3) (by
    intro xs x i
    rw [mul_fold]
    simp only [prodCode,pairBits_length]
    have hs:=bits_length_add (x.1*binaryValue (xs.take i).reverse) (2^(xs.take i).length*x.2)
    have hm:=bits_length_mul x.1 (binaryValue (xs.take i).reverse)
    have hn:=bits_length_mul (2^(xs.take i).length) x.2
    have hv:=bits_length_value (xs.take i).reverse
    rw [List.length_reverse] at hv
    rw [bits_length_pow2] at hn
    have hl : (xs.take i).length≤xs.length:=by simp only [List.length_take];omega
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
    omega)

noncomputable def binaryMul : Procedure (prodCode Nat.bits Nat.bits) Nat.bits
    (fun x=>x.1*x.2) := by
  let first:=first Nat.bits Nat.bits
  let second:=second Nat.bits Nat.bits
  let bits : Procedure Nat.bits (id : List Bool→List Bool) Nat.bits:=
    (identity (id : List Bool→List Bool)).precompose Nat.bits
  let start:=(reverse.comp (bits.comp second)).pair
    (first.pair (constant (prodCode Nat.bits Nat.bits) Nat.bits 0))
  exact ((Procedure.second Nat.bits Nat.bits).comp (mulFoldP.comp start)).congrFun (by
    intro x
    simp [mul_fold,binaryValue_bits])
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_AmplificationProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A binary stack-machine implementation of the exact rational Taylor
amplification used for the binary nuclear charges. The input parameter D is
unary; the large output and every arithmetic register are binary. -/

namespace ContinuumCoulomb.AmplificationProgram
open ExactQuantumFactoring.BitStackProgram
open scoped BigOperators

theorem encodeDigits_quote (bits : List Bool) : BinaryEncoding.encodeDigits bits = quoteBits bits := by
  induction bits with
  | nil => rfl
  | cons b bs ih => simp only [BinaryEncoding.encodeDigits, quoteBits_cons, ih]

end ContinuumCoulomb.AmplificationProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_BitStackIntegers
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram

lemma intOfSign_data (z : ℤ) : intOfSign (intData z)=z := by
  by_cases h : z<0
  · simp only [intData,intOfSign,h,decide_true,ite_true, if_true]
    exact (Int.eq_neg_natAbs_of_nonpos (le_of_lt h)).symm
  · simp only [intData,intOfSign,h,decide_false,Bool.false_eq_true,ite_false, if_false]
    exact Int.natAbs_of_nonneg (le_of_not_gt h)

lemma signedAdd_value (x : (Bool×ℕ)×(Bool×ℕ)) :
    intOfSign (signedAdd x)=intOfSign x.1+intOfSign x.2 := by
  rcases x with ⟨⟨s,a⟩,⟨t,b⟩⟩
  cases s <;> cases t <;> simp only [signedAdd,intOfSign,Bool.false_eq_true,
    Bool.true_eq_false,ite_true, if_true,ite_false, if_false,Int.natCast_add]
  all_goals first | omega | (split <;> simp only [ite_true, if_true,Bool.false_eq_true,ite_false, if_false] <;> omega)

lemma signedMul_value (x : (Bool×ℕ)×(Bool×ℕ)) :
    intOfSign (xor x.1.1 x.2.1,x.1.2*x.2.2)=intOfSign x.1*intOfSign x.2 := by
  rcases x with ⟨⟨s,a⟩,⟨t,b⟩⟩
  cases s <;> cases t <;> simp [intOfSign]

lemma intOfSign_not (x : Bool×ℕ) : intOfSign (!x.1,x.2) = -intOfSign x := by
  rcases x with ⟨s,n⟩
  cases s <;> simp [intOfSign]

namespace Procedure

noncomputable def intNeg : Procedure intCode intCode Neg.neg :=
  (signedInt.comp ((boolNot.comp intSign).pair intAbs)).congrFun (by
    intro z
    change intOfSign (!(intData z).1,(intData z).2) = -z
    rw [intOfSign_not,intOfSign_data])

noncomputable def signedAddP : Procedure
    (prodCode (prodCode boolCode Nat.bits) (prodCode boolCode Nat.bits))
    (prodCode boolCode Nat.bits) signedAdd := by
  let a:=first (prodCode boolCode Nat.bits) (prodCode boolCode Nat.bits)
  let b:=second (prodCode boolCode Nat.bits) (prodCode boolCode Nat.bits)
  let s:=(first boolCode Nat.bits).comp a
  let t:=(first boolCode Nat.bits).comp b
  let m:=(second boolCode Nat.bits).comp a
  let n:=(second boolCode Nat.bits).comp b
  let eqs:=boolNot.comp (boolXor.comp (s.pair t))
  let same:=s.pair (binaryAdd.comp (m.pair n))
  let le:=binaryLe.comp (m.pair n)
  let small:=t.pair (binarySub.comp (n.pair m))
  let large:=s.pair (binarySub.comp (m.pair n))
  exact (conditional eqs same (conditional le small large)).congrFun (by
    rintro ⟨⟨s,m⟩,⟨t,n⟩⟩
    cases s <;> cases t <;> simp [signedAdd,Function.comp_apply])

noncomputable def intAdd : Procedure (prodCode intCode intCode) intCode (fun x=>x.1+x.2) :=
  ((signedInt.comp signedAddP).precompose (fun x : ℤ×ℤ=>(intData x.1,intData x.2))).congrFun
    (by intro x;change intOfSign (signedAdd (intData x.1,intData x.2))=x.1+x.2
        rw [signedAdd_value,intOfSign_data,intOfSign_data])

noncomputable def intSub : Procedure (prodCode intCode intCode) intCode (fun x=>x.1-x.2) :=
  (intAdd.comp ((first intCode intCode).pair (intNeg.comp (second intCode intCode)))).congrFun
    (by intro x;rfl)

noncomputable def intMul : Procedure (prodCode intCode intCode) intCode (fun x=>x.1*x.2) := by
  let a:=first intCode intCode
  let b:=second intCode intCode
  let sign:=boolXor.comp ((intSign.comp a).pair (intSign.comp b))
  let mag:=binaryMul.comp ((intAbs.comp a).pair (intAbs.comp b))
  exact (signedInt.comp (sign.pair mag)).congrFun (by
    intro x
    change intOfSign (xor (intData x.1).1 (intData x.2).1,
      (intData x.1).2*(intData x.2).2)=x.1*x.2
    rw [signedMul_value (intData x.1,intData x.2),intOfSign_data,intOfSign_data])
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_EncodingPrograms
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite-stack parsing and serialization routines for the coordinate codes. Sign bits, natural-number marker bits, and field tails
are read by the program rather than by an assumed record-decoding operation. -/

namespace ContinuumCoulomb.EncodingPrograms
open ExactQuantumFactoring.BitStackProgram

noncomputable def naturalInput : Procedure BinaryEncoding.natural.encode Nat.bits id := by
  let p := (Procedure.first Nat.bits (fun _ : Unit => [])).precompose (fun n : ℕ => (n, ()))
  exact p.congrEncoding (by
    intro n
    change quoteBits n.bits ++ [] = BinaryEncoding.encodeDigits n.bits
    rw [List.append_nil, AmplificationProgram.encodeDigits_quote]) (by intro n; rfl)

noncomputable def naturalOutput : Procedure Nat.bits BinaryEncoding.natural.encode id :=
  (Procedure.quote Nat.bits).result
    (by intro n; exact (AmplificationProgram.encodeDigits_quote n.bits).symm)

/-- Serialize two already encoded fields by actual word concatenation. -/
noncomputable def appendPair {α β : Type} (c : BinaryEncoding.Codec α)
    (d : BinaryEncoding.Codec β) :
    Procedure (prodCode c.encode d.encode) (BinaryEncoding.pair c d).encode id :=
  (Procedure.append.precompose (fun x : α × β => (c.encode x.1, d.encode x.2))).result
    (by intro x; rfl)

/-- Read and remove the actual sign bit, retaining the coordinate payload
and the entire following encoded field. -/
noncomputable def integerPairPayload {α : Type} (c : BinaryEncoding.Codec α) :
    Procedure (BinaryEncoding.pair BinaryEncoding.integer c).encode
      (prodCode Nat.bits c.encode) (fun x => (integerPayload x.1, x.2)) :=
  (Procedure.tail.precompose (BinaryEncoding.pair BinaryEncoding.integer c).encode).result (by
    rintro ⟨z, y⟩
    cases z with
    | ofNat n =>
      change BinaryEncoding.encodeDigits n.bits ++ c.encode y = quoteBits n.bits ++ c.encode y
      rw [AmplificationProgram.encodeDigits_quote]
    | negSucc n =>
      change BinaryEncoding.encodeDigits n.bits ++ c.encode y = quoteBits n.bits ++ c.encode y
      rw [AmplificationProgram.encodeDigits_quote])

noncomputable def integerPairSign {α : Type} (c : BinaryEncoding.Codec α) :
    Procedure (BinaryEncoding.pair BinaryEncoding.integer c).encode Procedure.boolCode
      (fun x => integerNegative x.1) :=
  (Procedure.head.precompose (BinaryEncoding.pair BinaryEncoding.integer c).encode).congrFun (by
    rintro ⟨z, y⟩
    cases z <;> rfl)

noncomputable def integerFirst {α : Type} (c : BinaryEncoding.Codec α) :
    Procedure (BinaryEncoding.pair BinaryEncoding.integer c).encode intCode Prod.fst := by
  let payload := (Procedure.first Nat.bits c.encode).comp (integerPairPayload c)
  let positive := Procedure.natToInt.comp payload
  let negative := Procedure.intNeg.comp (Procedure.natToInt.comp
    (Procedure.successor.comp payload))
  exact (Procedure.conditional (integerPairSign c) negative positive).congrFun (by
    rintro ⟨z, y⟩
    cases z with
    | ofNat n => rfl
    | negSucc n =>
      change -(↑(n + 1) : ℤ) = Int.negSucc n
      omega)

noncomputable def integerInput : Procedure BinaryEncoding.integer.encode intCode id :=
  ((integerFirst emptyUnit).precompose (fun z => (z, ()))).congrEncoding
    (by intro z; exact List.append_nil _) (by intro z; rfl)

/-- Convert signed-magnitude stack integers to the exact signed-coordinate convention
whose negative payload is one less than its absolute value. -/
noncomputable def integerOutput : Procedure intCode BinaryEncoding.integer.encode id := by
  let positivePrefix : Procedure Nat.bits BinaryEncoding.integer.encode (fun n => (n : ℤ)) :=
    ((Procedure.prepend BinaryEncoding.natural.encode [false]).comp naturalOutput).result
      (by intro n; rfl)
  let negativePrefix : Procedure Nat.bits BinaryEncoding.integer.encode
      (fun n => Int.negSucc n) :=
    ((Procedure.prepend BinaryEncoding.natural.encode [true]).comp naturalOutput).result
      (by intro n; rfl)
  let magnitudePred := Procedure.binarySub.comp
    (Procedure.intAbs.pair (Procedure.constant intCode Nat.bits 1))
  exact (Procedure.conditional Procedure.intSign
    (negativePrefix.comp magnitudePred) (positivePrefix.comp Procedure.intAbs)).congrFun (by
      intro z
      cases z <;> simp)

end ContinuumCoulomb.EncodingPrograms

end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_BitStackRationals
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram

namespace Procedure

noncomputable def ratNeg : Procedure ratCode ratCode Neg.neg :=
  (makeRat.comp ((intNeg.comp ratNum).pair ratDen)).congrFun (by
    intro q
    change mkRat (-q.num) q.den = -q
    rw [Rat.mkRat_eq_div,Int.cast_neg,neg_div,Rat.num_div_den])

noncomputable def ratAdd : Procedure (prodCode ratCode ratCode) ratCode
    (fun x=>x.1+x.2) := by
  let a:=first ratCode ratCode
  let b:=second ratCode ratCode
  let an:=ratNum.comp a
  let bn:=ratNum.comp b
  let ad:=ratDen.comp a
  let bd:=ratDen.comp b
  let num:=intAdd.comp ((intMul.comp (an.pair (natToInt.comp bd))).pair
    (intMul.comp (bn.pair (natToInt.comp ad))))
  let den:=binaryMul.comp (ad.pair bd)
  exact (makeRat.comp (num.pair den)).congrFun (by
    intro x
    change mkRat (x.1.num * (x.2.den : ℤ) + x.2.num * (x.1.den : ℤ))
      (x.1.den*x.2.den) = x.1+x.2
    rw [←Rat.mkRat_add_mkRat _ _ x.1.den_nz x.2.den_nz]
    simp)

noncomputable def ratMul : Procedure (prodCode ratCode ratCode) ratCode
    (fun x=>x.1*x.2) := by
  let a:=first ratCode ratCode
  let b:=second ratCode ratCode
  let num:=intMul.comp ((ratNum.comp a).pair (ratNum.comp b))
  let den:=binaryMul.comp ((ratDen.comp a).pair (ratDen.comp b))
  exact (makeRat.comp (num.pair den)).congrFun (by
    intro x
    change mkRat (x.1.num*x.2.num) (x.1.den*x.2.den)=x.1*x.2
    rw [←Rat.mkRat_mul_mkRat];simp)

noncomputable def ratSub : Procedure (prodCode ratCode ratCode) ratCode
    (fun x=>x.1-x.2) :=
  (ratAdd.comp ((first ratCode ratCode).pair (ratNeg.comp (second ratCode ratCode)))).congrFun
    (by intro x;exact (sub_eq_add_neg _ _).symm)
end Procedure
end ExactQuantumFactoring.BitStackProgram

end


end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_BitStackRationalDivision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
namespace Procedure
noncomputable def ratDiv : Procedure (prodCode ratCode ratCode) ratCode (fun x=>x.1/x.2):=
  (ratMul.comp ((first ratCode ratCode).pair (ratInv.comp (second ratCode ratCode)))).congrFun
    (by intro x;exact (div_eq_mul_inv _ _).symm)
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_BitStackRationalFloor
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram.Procedure
noncomputable def ratFloor : Procedure ratCode intCode (fun q=>⌊q⌋):=by
  let num:=ratNum
  let den:=ratDen
  let mag:=intAbs.comp num
  let negmag:=binaryAdd.comp ((binaryDiv.comp
    ((binarySub.comp (mag.pair (constant ratCode Nat.bits 1))).pair den)).pair
    (constant ratCode Nat.bits 1))
  let pos:=natToInt.comp (binaryDiv.comp (mag.pair den))
  let neg:=intNeg.comp (natToInt.comp negmag)
  exact (conditional (intSign.comp num) neg pos).congrFun (by
    intro q
    change (if decide (q.num<0) then -((((q.num.natAbs-1)/q.den+1):ℕ):ℤ)
      else ((q.num.natAbs/q.den):ℤ))=⌊q⌋
    rw [Rat.floor_def']
    obtain ⟨d,hd⟩:=Nat.exists_eq_succ_of_ne_zero q.den_nz
    rw [hd]
    cases q.num with
    | ofNat a=>simp
    | negSucc a=>
      simp only [Int.negSucc_lt_zero, decide_true, ite_true, if_true, Int.natAbs_negSucc,
        Int.negSucc_ediv_ofNat_succ]
      change -((((a+1-1)/(d+1)+1):ℕ):ℤ)=Int.negSucc (a/(d+1))
      simp only [Nat.add_sub_cancel]
      rfl)
end ExactQuantumFactoring.BitStackProgram.Procedure

end



end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_ChargePrograms
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual polynomial-time stack programs for the two rounded binary-well
charges. The geometric scale is unary and the number of sites is binary.
The output is the pair of binary natural-number codes. -/

namespace ContinuumCoulomb
namespace ChargePrograms
open ExactQuantumFactoring.BitStackProgram

/-- Clamp a signed binary integer to a natural number. -/
noncomputable def intToNatProgram : Procedure intCode Nat.bits Int.toNat :=
  (Procedure.conditional Procedure.intSign
    (Procedure.constant intCode Nat.bits 0) Procedure.intAbs).congrFun (by
      intro z
      cases z <;> simp)

/-- Ties round upward, exactly as the manuscript's rational charge function. -/
noncomputable def rationalRoundProgram : Procedure ratCode intCode (fun q => round q) :=
  (Procedure.ratFloor.comp (Procedure.ratAdd.comp
    ((Procedure.identity ratCode).pair (Procedure.constant ratCode ratCode (1 / 2))))).congrFun
      (by intro q; exact (round_eq q).symm)

end ChargePrograms
end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_BitStackListCode
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {α β : Type}

lemma listCode_length_rev (ea : α→List Bool) (xs : List α) :
    (listCode ea xs.reverse).length=(listCode ea xs).length := by
  induction xs with
  | nil=>rfl
  | cons a as ih=>
    rw [List.reverse_cons]
    have hh:=listCode_length_append ea as.reverse [a]
    simp only [listCode_length_cons,ih] at hh ⊢
    have hz : (listCode ea []).length=1:=rfl
    omega

lemma code_le_of_mem (ea : α→List Bool) {a : α} {xs : List α} (h : a∈xs) :
    (ea a).length≤(listCode ea xs).length := by
  induction xs with
  | nil=>simp at h
  | cons b bs ih=>
    rw [List.mem_cons] at h
    rw [listCode_length_cons]
    rcases h with h|h
    · subst b;omega
    · have hh:=ih h;omega

namespace Procedure
variable (ea : α→List Bool)

noncomputable def listCons : Procedure (prodCode ea (listCode ea)) (listCode ea)
    (fun x=>x.1::x.2) :=
  (prepend (prodCode ea (listCode ea)) [true]).result (by intro x;rfl)

end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_BitStackListFold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {α β : Type}

lemma listCode_length_take_le (ea : α→List Bool) (i : ℕ) (xs : List α) :
    (listCode ea (xs.take i)).length≤(listCode ea xs).length := by
  have hh:=listCode_length_append ea (xs.take i) (xs.drop i)
  rw [List.take_append_drop] at hh
  have hp:=listCode_length_pos ea (xs.drop i)
  omega

end ExactQuantumFactoring.BitStackProgram

end


end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_BitStackListOps
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {α β : Type}

lemma listCode_length_map_bound (eb : β→List Bool) (f : α→β) (xs : List α) (B : ℕ)
    (h : ∀ a∈xs,(eb (f a)).length≤B) :
    (listCode eb (xs.map f)).length≤xs.length*(2*B+2)+1 := by
  induction xs with
  | nil=>simp [listCode]
  | cons a as ih=>
    have ha:=h a (by simp)
    have hb:=ih (by intro b hb;exact h b (by simp [hb]))
    simp only [List.map_cons,listCode_length_cons,List.length_cons]
    nlinarith

namespace Procedure
variable (ea : α→List Bool)
noncomputable def listRevAppend (d : α) : Procedure (prodCode (listCode ea) (listCode ea))
    (listCode ea) (fun x=>x.1.reverse++x.2) :=
  (foldList d (listCons ea) Polynomial.X (by
    intro xs ys i
    rw [fold_cons_append]
    have hh:=listCode_length_append ea (xs.take i).reverse ys
    rw [listCode_length_rev] at hh
    have ht:=listCode_length_take_le ea i xs
    simp only [Polynomial.eval_X]
    omega)).congrFun (by intro x;exact fold_cons_append x.1 x.2)

noncomputable def listReverse (d : α) : Procedure (listCode ea) (listCode ea) List.reverse :=
  ((listRevAppend ea d).comp ((identity (listCode ea)).pair
    (constant (listCode ea) (listCode ea) []))).congrFun (by intro xs;exact List.append_nil _)

noncomputable def listAppend (d : α) : Procedure (prodCode (listCode ea) (listCode ea))
    (listCode ea) (fun x=>x.1++x.2) :=
  ((listRevAppend ea d).comp (((listReverse ea d).comp (first (listCode ea) (listCode ea))).pair
    (second (listCode ea) (listCode ea)))).congrFun (by intro x;exact congrArg (fun xs=>xs++x.2) (List.reverse_reverse x.1))

variable {ea} {eb : β→List Bool} {f : α→β}
noncomputable def listMap (d : α) (e : β) (p : Procedure ea eb f) :
    Procedure (listCode ea) (listCode eb) (List.map f) := by
  let step:=(listCons eb).comp ((p.comp (first ea (listCode eb))).pair (second ea (listCode eb)))
  let q:=Polynomial.X*(Polynomial.C 2*(Polynomial.X+p.bound)+Polynomial.C 2)+1+Polynomial.X
  let fold:=foldList d step q (by
    intro xs ys i
    change (listCode eb ((xs.take i).foldl (fun ys a=>f a::ys) ys)).length≤_
    rw [fold_map_cons_append]
    let L:=(listCode ea xs).length+(listCode eb ys).length
    have hh:=listCode_length_append eb ((xs.take i).map f).reverse ys
    rw [listCode_length_rev] at hh
    have hm:(listCode eb ((xs.take i).map f)).length≤(xs.take i).length*(2*(L+p.bound.eval L)+2)+1:=by
      apply listCode_length_map_bound
      intro a ha
      have hc:=(code_le_of_mem ea (List.mem_of_mem_take ha)).trans (Nat.le_add_right _ (listCode eb ys).length)
      have ho:=p.output_length_le a
      have hp:=eval_nat_mono p.bound hc
      dsimp only [L] at *
      omega
    have ht : (xs.take i).length≤L:=by
      have h1:=list_length_le_code ea xs
      simp only [List.length_take]
      dsimp [L];omega
    have hm':=(Nat.mul_le_mul_right (2*(L+p.bound.eval L)+2) ht)
    simp only [q,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_X,Polynomial.eval_one]
    change (listCode eb (((xs.take i).map f).reverse++ys)).length≤L*(2*(L+p.bound.eval L)+2)+1+L
    dsimp only [L] at *
    omega)
  let start:=(identity (listCode ea)).pair (constant (listCode ea) (listCode eb) [])
  exact ((listReverse eb e).comp (fold.comp start)).congrFun (by
    intro xs
    change (xs.foldl (fun ys a=>f a::ys) []).reverse=xs.map f
    rw [fold_map_cons_append,List.append_nil,List.reverse_reverse])
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_BitStackTabulate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {α β : Type}
def tabCode (ea : α→List Bool) (eb : β→List Bool) := prodCode unaryCode (prodCode ea (listCode eb))
namespace Procedure
variable {ea : α→List Bool} {eb : β→List Bool} {f : α→ℕ→β}
noncomputable def tabStepP (p : Procedure (prodCode unaryCode ea) eb (fun x=>f x.2 x.1)) :
    Procedure (tabCode ea eb) (tabCode ea eb) (tabStep f) := by
  let i:=first unaryCode (prodCode ea (listCode eb))
  let rest:=second unaryCode (prodCode ea (listCode eb))
  let a:=(first ea (listCode eb)).comp rest
  let ys:=(second ea (listCode eb)).comp rest
  exact ((unarySuccessor.comp i).pair
    (a.pair ((listCons eb).comp ((p.comp (i.pair a)).pair ys)))).congrFun (by intro s;rfl)
noncomputable def tabulate (d : β)
    (p : Procedure (prodCode unaryCode ea) eb (fun x=>f x.2 x.1)) :
    Procedure (prodCode unaryCode ea) (listCode eb)
      (fun x=>(List.range x.1).map (f x.2)) := by
  let q:=(Polynomial.X+p.bound).comp (Polynomial.C 2*Polynomial.X+1)
  have hval (a : α) (i : ℕ) : (eb (f a i)).length≤q.eval (i+(ea a).length) := by
    have ho:=p.output_length_le (i,a)
    have hm:=eval_nat_mono (Polynomial.X+p.bound)
      (show (prodCode unaryCode ea (i,a)).length≤2*(i+(ea a).length)+1 by
        simp only [prodCode,pairBits_length,unaryCode,List.length_replicate];omega)
    simp only [Polynomial.eval_add,Polynomial.eval_X] at hm
    simpa only [q,Polynomial.eval_comp,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_X,Polynomial.eval_one] using ho.trans hm
  let rep:=(tabStepP p).iterate (Polynomial.X*(Polynomial.C 2*q+Polynomial.C 5)) (by
    rintro n ⟨i,a,ys⟩ j hj
    rw [tabStep_iterate]
    have len0 : (tabCode ea eb (i,a,ys)).length=2*i+2*(ea a).length+(listCode eb ys).length+2 := by
      simp only [tabCode,prodCode,pairBits_length,unaryCode,List.length_replicate];omega
    have hv : ∀ k∈List.range' i j,(eb (f a k)).length≤q.eval (n+(tabCode ea eb (i,a,ys)).length) := by
      intro k hk
      have hk':=List.mem_range'.mp hk
      exact (hval a k).trans (eval_nat_mono q (by rw [len0];omega))
    have hmap:=listCode_length_map_bound eb (f a) (List.range' i j) _ hv
    have happ:=listCode_length_append eb (((List.range' i j).map (f a)).reverse) ys
    rw [listCode_length_rev] at happ
    simp only [List.length_range'] at hmap
    simp only [tabCode,prodCode,pairBits_length,unaryCode,List.length_replicate,
      Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_X] at *
    nlinarith)
  let inputN:=first unaryCode ea
  let inputA:=second unaryCode ea
  let start:=(constant (prodCode unaryCode ea) unaryCode 0).pair
    (inputA.pair (constant (prodCode unaryCode ea) (listCode eb) []))
  let result:=((second ea (listCode eb)).comp
    (second unaryCode (prodCode ea (listCode eb)))).comp (rep.comp (inputN.pair start))
  exact ((listReverse eb d).comp result).congrFun (by
    rintro ⟨n,a⟩
    change (((tabStep f)^[n] (0,a,[])).2.2).reverse=(List.range n).map (f a)
    rw [tabStep_iterate,List.append_nil,List.reverse_reverse,List.range_eq_range'])
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_BitStackListIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {α : Type}

namespace Procedure
variable (ea : α→List Bool)
noncomputable def listDrop : Procedure (prodCode Nat.bits (listCode ea)) (listCode ea)
    (fun x=>x.2.drop x.1) := by
  let en:=prodCode Nat.bits (listCode ea)
  let n:=first Nat.bits (listCode ea)
  let xs:=second Nat.bits (listCode ea)
  let pred:=binarySub.comp (n.pair (constant en Nat.bits 1))
  let step:=(conditional (binaryZero.comp n) (identity en)
    (pred.pair ((listTail ea).comp xs))).congrFun (by intro x;rfl)
  have stepType : Procedure en en (dropStep (α:=α)):=
    step.congrFun (by intro x;simp only [Function.comp_apply,decide_eq_true_eq,id_eq,dropStep])
  let rep:=stepType.iterate Polynomial.X (by
    intro k x i _
    rw [dropStep_iterate]
    simp only [en,prodCode,pairBits_length,Polynomial.eval_X]
    have hn:=bits_length_mono (Nat.sub_le x.1 i)
    have hl:=listCode_length_drop_le ea (min i x.1) x.2
    omega)
  let times:=(length.precompose (listCode ea)).comp xs
  exact (xs.comp (rep.comp (times.pair (identity en)))).congrFun (by
    intro x
    change (dropStep^[(listCode ea x.2).length] x).2=x.2.drop x.1
    rw [dropStep_iterate]
    by_cases h:x.1≤(listCode ea x.2).length
    · rw [Nat.min_eq_right h]
    · have hlen:=list_length_le_code ea x.2
      rw [Nat.min_eq_left (by omega),List.drop_eq_nil_of_le (by omega),List.drop_eq_nil_of_le (by omega)])
noncomputable def listGet (d : α) : Procedure (prodCode Nat.bits (listCode ea)) ea
    (fun x=>(x.2.drop x.1).headD d) := (listHead ea d).comp (listDrop ea)
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_BitStackListMapWith
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {α β γ : Type}
namespace Procedure
variable {ea : α→List Bool} {eb : β→List Bool} {ec : γ→List Bool} {f : α→β→γ}
noncomputable def listMapWith (d : β) (e : γ)
    (p : Procedure (prodCode ea eb) ec (fun x=>f x.1 x.2)) :
    Procedure (prodCode ea (listCode eb)) (listCode ec) (fun x=>x.2.map (f x.1)) := by
  let i:=unaryToBits.comp (first unaryCode (prodCode ea (listCode eb)))
  let env:=second unaryCode (prodCode ea (listCode eb))
  let a:=(first ea (listCode eb)).comp env
  let xs:=(second ea (listCode eb)).comp env
  let get:=(listGet eb d).comp (i.pair xs)
  let step:=p.comp (a.pair get)
  let len:=(NativeAIG.Emission.listUnaryLength eb d).comp (second ea (listCode eb))
  exact ((tabulate (f:=fun (env : α×List β) i=>f env.1 ((env.2.drop i).headD d)) e step).comp (len.pair (identity (prodCode ea (listCode eb))))).congrFun (by
    intro x;exact map_range_getD x.2 d (f x.1))
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_BitStackPowers
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
namespace Procedure
noncomputable def binaryPow : Procedure (prodCode unaryCode Nat.bits) Nat.bits (fun x=>x.2^x.1):=by
  let a:=first Nat.bits Nat.bits
  let b:=second Nat.bits Nat.bits
  let step : Procedure (prodCode Nat.bits Nat.bits) (prodCode Nat.bits Nat.bits) powerStep:=
    a.pair (binaryMul.comp (b.pair a))
  let rep:=step.iterate (Polynomial.X^2+Polynomial.C 3*Polynomial.X+1) (by
    intro n s i hi
    rw [powerStep_iterate]
    have hm:=bits_length_mul s.2 (s.1^i)
    have hp:=bits_length_pow s.1 i
    simp only [prodCode,pairBits_length,Polynomial.eval_add,Polynomial.eval_pow,Polynomial.eval_X,
      Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_one]
    nlinarith)
  let e:=first unaryCode Nat.bits
  let x:=second unaryCode Nat.bits
  exact ((second Nat.bits Nat.bits).comp (rep.comp (e.pair (x.pair (constant _ Nat.bits 1))))).congrFun (by
    intro x;change ((powerStep^[x.1]) (x.2,1)).2=x.2^x.1
    rw [powerStep_iterate];simp)
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_SquareRootProgram
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bitwise integer square-root search and its actual polynomial-time
Boolean-stack implementation. This supplies arithmetic for finite-precision
geometric constants and mediator amplitudes without a real square-root oracle. -/

namespace ContinuumCoulomb.SquareRootProgram
open ExactQuantumFactoring.BitStackProgram

def code : State → List Bool := prodCode Nat.bits (prodCode Nat.bits Nat.bits)

theorem iterate_power (m k g : ℕ) :
    (step^[k]) (m, 2 ^ k, g) =
      (m, 1, ExactQuantumFactoring.Primality.rootSearch m 2 k g) := by
  induction k generalizing g with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    have hhalf : 2 ^ (k + 1) / 2 = 2 ^ k := by simp [pow_succ]
    simp only [step, hhalf, ← pow_two, ExactQuantumFactoring.Primality.rootSearch]
    exact ih _

theorem code_length (s : State) :
    (code s).length = 2 * s.1.bits.length + 2 * s.2.1.bits.length + s.2.2.bits.length + 2 := by
  simp only [code, prodCode, pairBits_length]
  omega

theorem measure_le_code (s : State) : measure s ≤ (code s).length := by
  rw [code_length]
  unfold measure
  omega

theorem code_le_measure (s : State) : (code s).length ≤ 2 * measure s + 2 := by
  rw [code_length]
  unfold measure
  omega

theorem step_measure (s : State) : measure (step s) ≤ measure s + s.2.1.bits.length + 1 := by
  have hhalf : (s.2.1 / 2).bits.length ≤ s.2.1.bits.length :=
    bits_length_mono (Nat.div_le_self _ _)
  have hc := bits_length_add s.2.2 (s.2.1 / 2)
  dsimp only [measure, step]
  split_ifs <;> omega

theorem iterate_half_bits (s : State) (i : ℕ) :
    ((step^[i]) s).2.1.bits.length ≤ s.2.1.bits.length := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    exact (bits_length_mono (Nat.div_le_self _ _)).trans ih

theorem iterate_measure (s : State) (i : ℕ) :
    measure ((step^[i]) s) ≤ measure s + i * (measure s + 1) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    have h := step_measure ((step^[i]) s)
    have hp := iterate_half_bits s i
    have hp0 : s.2.1.bits.length ≤ measure s := by unfold measure; omega
    nlinarith

theorem iterate_code_bound (n : ℕ) (s : State) (i : ℕ) (hi : i ≤ n) :
    (code ((step^[i]) s)).length ≤
      (8 * (Polynomial.X + 1) ^ 2 + 8 : Polynomial ℕ).eval (n + (code s).length) := by
  have hc := code_le_measure ((step^[i]) s)
  have hm := iterate_measure s i
  have hs := measure_le_code s
  have him := Nat.mul_le_mul hi hs
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
  nlinarith

noncomputable def stepProgram : Procedure code code step := by
  let m := Procedure.first Nat.bits (prodCode Nat.bits Nat.bits)
  let rest := Procedure.second Nat.bits (prodCode Nat.bits Nat.bits)
  let p := (Procedure.first Nat.bits Nat.bits).comp rest
  let g := (Procedure.second Nat.bits Nat.bits).comp rest
  let half := Procedure.binaryDiv.comp (p.pair (Procedure.constant code Nat.bits 2))
  let candidate := Procedure.binaryAdd.comp (g.pair half)
  let square := Procedure.binaryMul.comp (candidate.pair candidate)
  let test := Procedure.binaryLe.comp (square.pair m)
  let newGuess := Procedure.conditional test candidate g
  exact (m.pair (half.pair newGuess)).congrFun (by
    intro s
    simp only [step, Function.comp_apply, decide_eq_true_eq])

noncomputable def repeatProgram : Procedure (prodCode unaryCode code) code
    (fun x => (step^[x.1]) x.2) :=
  stepProgram.iterate (8 * (Polynomial.X + 1) ^ 2 + 8) iterate_code_bound

noncomputable def rawProgram : Procedure Nat.bits Nat.bits root := by
  let m := Procedure.identity Nat.bits
  let n := Procedure.length.precompose Nat.bits
  let power := Procedure.binaryPow.comp (n.pair (Procedure.constant Nat.bits Nat.bits 2))
  let state := m.pair (power.pair (Procedure.constant Nat.bits Nat.bits 0))
  let run := repeatProgram.comp (n.pair state)
  let guess := (Procedure.second Nat.bits Nat.bits).comp
    (Procedure.second Nat.bits (prodCode Nat.bits Nat.bits))
  exact (guess.comp run).congrFun (by
    intro m
    change ((step^[m.bits.length]) (m, 2 ^ m.bits.length, 0)).2.2 = root m
    rw [iterate_power]
    rfl)

end ContinuumCoulomb.SquareRootProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_DyadicRootProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A computed dyadic square root of a nonnegative rational, with strict
error below one unit in the requested binary precision. Precision is unary;
numerator, denominator, and result are binary. -/

namespace ContinuumCoulomb.DyadicRootProgram
open ExactQuantumFactoring.BitStackProgram

def rawCode : Input → List Bool := prodCode unaryCode (prodCode Nat.bits Nat.bits)

noncomputable def precisionProgram : Procedure rawCode unaryCode Prod.fst :=
  Procedure.first unaryCode (prodCode Nat.bits Nat.bits)

noncomputable def numeratorProgram : Procedure rawCode Nat.bits (fun x => x.2.1) :=
  (Procedure.first Nat.bits Nat.bits).comp
    (Procedure.second unaryCode (prodCode Nat.bits Nat.bits))

noncomputable def denominatorProgram : Procedure rawCode Nat.bits (fun x => x.2.2) :=
  (Procedure.second Nat.bits Nat.bits).comp
    (Procedure.second unaryCode (prodCode Nat.bits Nat.bits))

noncomputable def powerProgram : Procedure rawCode Nat.bits (fun x => 2 ^ x.1) :=
  (Procedure.binaryPow.comp (precisionProgram.pair
    (Procedure.constant rawCode Nat.bits 2))).congrFun (by intro x; rfl)

noncomputable def squareProgram : Procedure rawCode Nat.bits (fun x => (2 ^ x.1) ^ 2) :=
  (Procedure.binaryMul.comp (powerProgram.pair powerProgram)).congrFun (by intro x; exact (pow_two _).symm)

noncomputable def quotientProgram : Procedure rawCode Nat.bits
    (fun x => x.2.1 * (2 ^ x.1) ^ 2 / x.2.2) :=
  (Procedure.binaryDiv.comp ((Procedure.binaryMul.comp
    (numeratorProgram.pair squareProgram)).pair denominatorProgram)).congrFun (by intro x; rfl)

noncomputable def rootNumeratorProgram : Procedure rawCode Nat.bits
    (fun x => SquareRootProgram.root (x.2.1 * (2 ^ x.1) ^ 2 / x.2.2)) :=
  SquareRootProgram.rawProgram.comp quotientProgram

noncomputable def rawProgram : Procedure rawCode ratCode
    (fun x => value x.1 x.2.1 x.2.2) :=
  (Procedure.ratDiv.comp ((Procedure.natToRat.comp rootNumeratorProgram).pair
    (Procedure.natToRat.comp powerProgram))).congrFun (by
      intro x
      simp only [Function.comp_apply, value, Nat.cast_pow, Nat.cast_ofNat])

end ContinuumCoulomb.DyadicRootProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_MediatorParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit polynomial scales and rational positive spokes for one actual
simultaneous singlet-mediator stage. The norm hypothesis concerns the
unchanged low-block terms; no spectral conclusion is assumed. -/

namespace ContinuumCoulomb.MediatorParameters
open scoped BigOperators Kronecker InnerProductSpace

def spoke (r W G : ℕ) (J : ℚ) : ℚ :=
  let q := radicand r W G J
  DyadicRootProgram.value (precision r G) q.num.toNat q.den

end ContinuumCoulomb.MediatorParameters

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_MediatorIteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The three actual mediator stages. Only the original central bonds
survive the last subdivision; each original spoke becomes a nine-link
path, giving eighteen new spins and nineteen positive bonds per edge. -/

namespace ContinuumCoulomb.MediatorIteration
open Matrix MediatorGraph
open scoped BigOperators Kronecker InnerProductSpace

def firstSpokes {n r : ℕ} (F : Bonds n r) (W G : ℕ) : Bonds (n + r * 2) (r * 2) :=
  spokes F (fun e => member (F.weight e))
    (fun e => MediatorParameters.spoke r W G (F.weight e))

def secondSpokes {n r : ℕ} (F : Bonds n r) (W G : ℕ) :
    Bonds (n + r * 2 + r * 2 * 2) (r * 2 * 2) :=
  spokes (firstSpokes F W G) (fun e => member ((firstSpokes F W G).weight e))
    (fun e => MediatorParameters.spoke (r * 2) (secondBound r W G) G ((firstSpokes F W G).weight e))

def secondPaths {n r : ℕ} (F : Bonds n r) (W G : ℕ) :
    Bonds (n + r * 2 + r * 2 * 2) (r * 2 + r * 2 * 2) :=
  join (secondCentral F W G) (secondSpokes F W G)

def thirdSpokes {n r : ℕ} (F : Bonds n r) (W G : ℕ) :
    Bonds (n + r * 2 + r * 2 * 2 + (r * 2 + r * 2 * 2) * 2) ((r * 2 + r * 2 * 2) * 2) :=
  spokes (secondPaths F W G) (fun e => member ((secondPaths F W G).weight e))
    (fun e => MediatorParameters.spoke (r * 2 + r * 2 * 2) (thirdBound r W G) G
      ((secondPaths F W G).weight e))

def finalGraph {n r : ℕ} (F : Bonds n r) (W G : ℕ) :
    Bonds (n + r * 2 + r * 2 * 2 + (r * 2 + r * 2 * 2) * 2)
      (r + ((r * 2 + r * 2 * 2) + (r * 2 + r * 2 * 2) * 2)) :=
  join (lift (r * 2 + r * 2 * 2) (retainedCentral F W G))
    (join (thirdCentral F W G) (thirdSpokes F W G))

end ContinuumCoulomb.MediatorIteration

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_Variational_Axis
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
namespace NeutralAtom

def axis (a : Fin 3) : Position := EuclideanSpace.single a 1

def coordinateLaplacian (f : Position → ℝ) (x : Position) : ℝ :=
  ∑ a : Fin 3, deriv (deriv (fun t : ℝ => f (x+t • axis a))) 0

theorem deriv_affine_line {f : Position → ℝ} {x v : Position} {t : ℝ}
    (hf : DifferentiableAt ℝ f (x+t • v)) :
    deriv (fun u : ℝ => f (x+u • v)) t = fderiv ℝ f (x+t • v) v := by
  have hl : HasDerivAt (fun u : ℝ => x+u • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  exact (hf.hasFDerivAt.comp_hasDerivAt t hl).deriv

theorem second_deriv_affine_line {f : Position → ℝ} {x v : Position}
    (hf : ContDiffAt ℝ 2 f x) :
    deriv (deriv (fun u : ℝ => f (x+u • v))) 0 =
      fderiv ℝ (fun y => fderiv ℝ f y v) x v := by
  have hl : Tendsto (fun u : ℝ => x+u • v) (𝓝 0) (𝓝 x) := by
    simpa using (show ContinuousAt (fun u : ℝ => x+u • v) 0 by fun_prop).tendsto
  have he : deriv (fun u : ℝ => f (x+u • v)) =ᶠ[𝓝 0]
      fun u => fderiv ℝ f (x+u • v) v := by
    filter_upwards [hl.eventually (hf.eventually (by norm_num))] with u hu
    exact deriv_affine_line (hu.differentiableAt (by norm_num))
  rw [he.deriv_eq]
  have hd : DifferentiableAt ℝ (fun y => fderiv ℝ f y v) x :=
    ((hf.fderiv_right (show (1 : WithTop ℕ∞)+1 ≤ 2 by norm_num)).clm_apply contDiffAt_const).differentiableAt_one
  simpa using deriv_affine_line (x := x) (v := v) (t := 0) (by simpa using hd)

open scoped Convolution
open ContinuousLinearMap

def dirPartial (f : Position → ℝ) (v : Position) : Position → ℝ :=
  fun x => fderiv ℝ f x v

theorem coordinateLaplacian_eq_partials {f : Position → ℝ} {x : Position}
    (hf : ContDiffAt ℝ 2 f x) :
    coordinateLaplacian f x = ∑ a : Fin 3, dirPartial (dirPartial f (axis a)) (axis a) x := by
  apply Finset.sum_congr rfl
  intro a _
  exact second_deriv_affine_line hf

theorem coordinateLaplacian_congr_nhds {f g : Position → ℝ} {x : Position}
    (h : f =ᶠ[𝓝 x] g) : coordinateLaplacian f x = coordinateLaplacian g x := by
  apply Finset.sum_congr rfl
  intro a _
  have ht : Tendsto (fun t : ℝ => x+t • axis a) (𝓝 0) (𝓝 x) := by
    simpa using (show ContinuousAt (fun t : ℝ => x+t • axis a) 0 by fun_prop).tendsto
  have he : (fun t : ℝ => f (x+t • axis a)) =ᶠ[𝓝 0]
      (fun t : ℝ => g (x+t • axis a)) := ht.eventually h
  exact he.deriv.deriv_eq

theorem coordinateLaplacian_zero (x : Position) :
    coordinateLaplacian (fun _ => (0 : ℝ)) x = 0 := by
  simp [coordinateLaplacian]

theorem coordinateLaplacian_eq_zero_of_notMem_tsupport {f : Position → ℝ} {x : Position}
    (h : x ∉ tsupport f) : coordinateLaplacian f x = 0 := by
  rw [coordinateLaplacian_congr_nhds (notMem_tsupport_iff_eventuallyEq.mp h)]
  exact coordinateLaplacian_zero x

end NeutralAtom
end
end
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_Variational_WeakLaplacian
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
namespace NeutralAtom
open scoped Convolution
open ContinuousLinearMap

theorem continuousAt_coordinateLaplacian {f : Position → ℝ} {x : Position}
    (hf : ContDiffAt ℝ 2 f x) : ContinuousAt (coordinateLaplacian f) x := by
  have hp (v : Position) : ContDiffAt ℝ 1 (dirPartial f v) x :=
    (hf.fderiv_right (show (1 : WithTop ℕ∞)+1 ≤ 2 by norm_num)).clm_apply contDiffAt_const
  have hpp (v : Position) : ContinuousAt (dirPartial (dirPartial f v) v) x :=
    (((hp v).fderiv_right (show (0 : WithTop ℕ∞)+1 ≤ 1 by norm_num)).clm_apply
      contDiffAt_const).continuousAt
  have he : coordinateLaplacian f =ᶠ[𝓝 x]
      fun y => ∑ a : Fin 3, dirPartial (dirPartial f (axis a)) (axis a) y := by
    filter_upwards [hf.eventually (by norm_num)] with y hy
    exact coordinateLaplacian_eq_partials hy
  have hsum : ContinuousAt (fun y => ∑ a : Fin 3,
      dirPartial (dirPartial f (axis a)) (axis a) y) x :=
    tendsto_finsetSum _ (fun a _ => hpp (axis a))
  exact hsum.congr_of_eventuallyEq he

theorem continuous_coordinateLaplacian {f : Position → ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous (coordinateLaplacian f) :=
  continuous_iff_continuousAt.mpr fun _ => continuousAt_coordinateLaplacian hf.contDiffAt

end NeutralAtom
end
end
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_Packets_CoulombKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
namespace NeutralAtom
open scoped Convolution
open ContinuousLinearMap

def potentialOf (ρ : Position → ℝ) (x : Position) : ℝ :=
  ∫ y, coulombKernel (x-y)*ρ y

def kernelBallMass (r : ℝ) : ℝ := ∫ y in Metric.ball (0 : Position) r, coulombKernel y

theorem coulombKernel_nonneg (x : Position) : 0 ≤ coulombKernel x :=
  inv_nonneg.mpr (norm_nonneg x)

end NeutralAtom
end
end
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_RationalSumProgram
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual polynomial rational-list summation. Unreduced numerator and
positive denominator registers are accumulated with ordinary integer
arithmetic, then reduced once. Their bit lengths grow cubically at most. -/

namespace ContinuumCoulomb.RationalSumProgram
open ExactQuantumFactoring.BitStackProgram
open scoped BigOperators

def stateCode : State → List Bool := prodCode intCode Nat.bits

theorem integer_bits_add (a b : ℤ) :
    (a + b).natAbs.bits.length ≤ a.natAbs.bits.length + b.natAbs.bits.length + 1 :=
  (bits_length_mono (Int.natAbs_add_le a b)).trans (bits_length_add _ _)

theorem step_bits (s : State) (q : ℚ) :
    (step s q).2.bits.length ≤ s.2.bits.length + q.den.bits.length ∧
    (step s q).1.natAbs.bits.length ≤ s.1.natAbs.bits.length + q.den.bits.length +
      q.num.natAbs.bits.length + s.2.bits.length + 1 := by
  constructor
  · exact bits_length_mul _ _
  · have h := integer_bits_add (s.1 * q.den) (q.num * s.2)
    simp only [Int.natAbs_mul, Int.natAbs_natCast] at h
    have h1 := bits_length_mul s.1.natAbs q.den
    have h2 := bits_length_mul q.num.natAbs s.2
    exact h.trans (by omega)

theorem fold_bits (xs : List ℚ) (s : State) (B : ℕ)
    (hB : ∀ q ∈ xs, q.num.natAbs.bits.length + q.den.bits.length ≤ B) :
    (xs.foldl step s).2.bits.length ≤ s.2.bits.length + xs.length * B ∧
    (xs.foldl step s).1.natAbs.bits.length ≤ s.1.natAbs.bits.length +
      xs.length * (B + s.2.bits.length + xs.length * B + 1) := by
  induction xs generalizing s with
  | nil => simp
  | cons q xs ih =>
    have hq := hB q (by simp)
    have hi := ih (step s q) (by intro a ha; exact hB a (by simp [ha]))
    have hs := step_bits s q
    simp only [List.foldl_cons, List.length_cons]
    constructor
    · nlinarith [hi.1]
    · nlinarith [hi.2]

theorem state_length (s : State) :
    (stateCode s).length = 2 * s.1.natAbs.bits.length + s.2.bits.length + 7 := by
  simp only [stateCode, prodCode, intCode, intData, pairBits_length, Procedure.boolCode,
    List.length_singleton]
  omega

theorem rational_length (q : ℚ) :
    (ratCode q).length = 2 * q.num.natAbs.bits.length + q.den.bits.length + 7 :=
  state_length (q.num, q.den)

noncomputable def stepProgram : Procedure (prodCode ratCode stateCode) stateCode
    (fun x => step x.2 x.1) := by
  let q := Procedure.first ratCode stateCode
  let s := Procedure.second ratCode stateCode
  let qn := Procedure.ratNum.comp q
  let qd := Procedure.ratDen.comp q
  let sn := (Procedure.first intCode Nat.bits).comp s
  let sd := (Procedure.second intCode Nat.bits).comp s
  let first := Procedure.intMul.comp (sn.pair (Procedure.natToInt.comp qd))
  let second := Procedure.intMul.comp (qn.pair (Procedure.natToInt.comp sd))
  exact ((Procedure.intAdd.comp (first.pair second)).pair
    (Procedure.binaryMul.comp (sd.pair qd))).congrFun (by intro x; rfl)

noncomputable def foldProgram : Procedure (prodCode (listCode ratCode) stateCode) stateCode
    (fun x => x.1.foldl step x.2) :=
  Procedure.foldList 0 stepProgram (Polynomial.C 20 * (Polynomial.X + 1) ^ 3) (by
    intro xs s i
    let L := (listCode ratCode xs).length + (stateCode s).length
    have hq : ∀ q ∈ xs.take i, q.num.natAbs.bits.length + q.den.bits.length ≤ L := by
      intro q hq
      have h := code_le_of_mem ratCode (List.mem_of_mem_take hq)
      rw [rational_length] at h
      dsimp only [L]
      omega
    have h := fold_bits (xs.take i) s L hq
    have hs := state_length s
    have hi : (xs.take i).length ≤ L :=
      (show (xs.take i).length ≤ xs.length by simp only [List.length_take]; omega).trans
        ((list_length_le_code ratCode xs).trans (Nat.le_add_right _ _))
    rw [state_length]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_one]
    change _ ≤ 20 * (L + 1) ^ 3
    have hs1 : s.1.natAbs.bits.length ≤ L := by dsimp only [L]; omega
    have hs2 : s.2.bits.length ≤ L := by dsimp only [L]; omega
    have hmul : (xs.take i).length * L ≤ L * L := Nat.mul_le_mul_right L hi
    have hn : (xs.take i).length * (L + s.2.bits.length + (xs.take i).length * L + 1) ≤
        L * (2 * L + L * L + 1) :=
      Nat.mul_le_mul hi (by omega)
    nlinarith [h.1, h.2])

noncomputable def sumProgram : Procedure (listCode ratCode) ratCode List.sum := by
  let start := (Procedure.identity (listCode ratCode)).pair
    (Procedure.constant (listCode ratCode) stateCode (0, 1))
  exact (Procedure.makeRat.comp (foldProgram.comp start)).congrFun (by
    intro xs
    change mkRat (xs.foldl step (0, 1)).1 (xs.foldl step (0, 1)).2 = xs.sum
    rw [Rat.mkRat_eq_div]
    have h := fold_value xs (0, 1) (by norm_num)
    simpa only [value, Int.cast_zero, Nat.cast_one, zero_div, zero_add] using h)

end ContinuumCoulomb.RationalSumProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_RationalQuadratureProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal tabulation and summation of rational quadrature samples.
The sample count is unary; bounds, spacing and evaluator data are encoded
as ordinary inputs to the machine. -/

namespace ContinuumCoulomb.RationalQuadratureProgram
open ExactQuantumFactoring.BitStackProgram
open scoped BigOperators

variable {E : Type}

noncomputable def sampleProgram (ce : E → List Bool) (evaluate : E → ℚ → ℚ)
    (p : Procedure (prodCode ce ratCode) ratCode (fun x => evaluate x.1 x.2)) :
    Procedure (inputCode ce) ratCode (fun x => sample evaluate x.2 x.1) := by
  let i := Procedure.first unaryCode (environmentCode ce)
  let env := Procedure.second unaryCode (environmentCode ce)
  let e := (Procedure.first ce (prodCode ratCode ratCode)).comp env
  let ah := (Procedure.second ce (prodCode ratCode ratCode)).comp env
  let a := (Procedure.first ratCode ratCode).comp ah
  let h := (Procedure.second ratCode ratCode).comp ah
  let ir := Procedure.natToRat.comp (Procedure.unaryToBits.comp i)
  let t := Procedure.ratAdd.comp (a.pair (Procedure.ratMul.comp (ir.pair h)))
  exact (p.comp (e.pair t)).congrFun (by intro x; rfl)

noncomputable def program (ce : E → List Bool) (evaluate : E → ℚ → ℚ)
    (p : Procedure (prodCode ce ratCode) ratCode (fun x => evaluate x.1 x.2)) :
    Procedure (inputCode ce) ratCode (value evaluate) := by
  let samples := Procedure.tabulate (0 : ℚ) (sampleProgram ce evaluate p)
  let sum := RationalSumProgram.sumProgram.comp samples
  let env := Procedure.second unaryCode (environmentCode ce)
  let ah := (Procedure.second ce (prodCode ratCode ratCode)).comp env
  let h := (Procedure.second ratCode ratCode).comp ah
  exact (Procedure.ratMul.comp (h.pair sum)).congrFun (by
    intro x
    change x.2.2.2 * ((List.range x.1).map (sample evaluate x.2)).sum = value evaluate x
    rw [range_sum]
    rfl)

end ContinuumCoulomb.RationalQuadratureProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_PiProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A rational polynomial-time approximation to π from the integral of
`4 / (1+x²)` on `[0,1]`. The unary sample count gives absolute error `8/N`.
This supplies the normalizing constant in the heat-kernel evaluator. -/

namespace ContinuumCoulomb.PiProgram
open ExactQuantumFactoring.BitStackProgram
open RationalQuadratureProgram

noncomputable def evaluateProgram :
    Procedure (prodCode ratCode ratCode) ratCode (fun x => evaluate x.1 x.2) := by
  let q := Procedure.second ratCode ratCode
  let square := Procedure.ratMul.comp (q.pair q)
  let one := Procedure.constant (prodCode ratCode ratCode) ratCode (1 : ℚ)
  exact (Procedure.ratInv.comp (Procedure.ratAdd.comp (one.pair square))).congrFun
    (by intro x; simp only [evaluate, pow_two]; rfl)

noncomputable def inputProgram : Procedure unaryCode (inputCode ratCode) input := by
  let n := Procedure.identity unaryCode
  let zero := Procedure.constant unaryCode ratCode (0 : ℚ)
  let reciprocal := Procedure.ratInv.comp (Procedure.natToRat.comp Procedure.unaryToBits)
  exact (n.pair (zero.pair (zero.pair reciprocal))).congrFun (by intro N; rfl)

noncomputable def program : Procedure unaryCode ratCode approximate := by
  let q := (RationalQuadratureProgram.program ratCode evaluate evaluateProgram).comp inputProgram
  let four := Procedure.constant unaryCode ratCode (4 : ℚ)
  exact (Procedure.ratMul.comp (four.pair q)).congrFun (by intro N; rfl)

end ContinuumCoulomb.PiProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_RationalBoxRound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded integer numerator registers for rounded Euler iteration.
Clipping to a fixed box prevents malformed evaluator outputs from causing
unbounded register growth. On valid trajectories clipping never increases
the distance to the exact coordinate. -/

namespace ContinuumCoulomb.RationalBoxRound
open ExactQuantumFactoring.BitStackProgram

theorem numerator_bits (D B : ℕ) (q : ℚ) :
    (numerator D B q).natAbs.bits.length ≤ B.bits.length :=
  bits_length_mono (clip_natAbs _ _)

def inputCode : Input → List Bool := prodCode (prodCode Nat.bits Nat.bits) ratCode

noncomputable opaque clipProgram : Procedure (prodCode Nat.bits intCode) intCode
    (fun x => clip x.1 x.2) := by
  let B := Procedure.natToInt.comp (Procedure.first Nat.bits intCode)
  let z := Procedure.second Nat.bits intCode
  let low := Procedure.intNeg.comp B
  let tooLow := Procedure.intSign.comp (Procedure.intSub.comp (z.pair low))
  let tooHigh := Procedure.intSign.comp (Procedure.intSub.comp (B.pair z))
  exact (Procedure.conditional tooLow low (Procedure.conditional tooHigh B z)).congrFun (by
    intro x
    simp only [Function.comp_apply,decide_eq_true_eq]
    unfold clip
    split_ifs with hlo hhi
    · rw [min_eq_right (by linarith),max_eq_left (by linarith)]
    · rw [min_eq_left (by linarith),max_eq_right (by omega)]
    · rw [min_eq_right (by linarith),max_eq_right (by linarith)])

noncomputable opaque numeratorProgram : Procedure inputCode intCode
    (fun x => numerator x.1.1 x.1.2 x.2) := by
  let db := Procedure.first (prodCode Nat.bits Nat.bits) ratCode
  let d := (Procedure.first Nat.bits Nat.bits).comp db
  let b := (Procedure.second Nat.bits Nat.bits).comp db
  let q := Procedure.second (prodCode Nat.bits Nat.bits) ratCode
  let scaled := Procedure.ratMul.comp ((Procedure.natToRat.comp d).pair q)
  exact (clipProgram.comp (b.pair (Procedure.ratFloor.comp scaled))).congrFun (by intro x; rfl)

end ContinuumCoulomb.RationalBoxRound

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarGroundTransform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The planar manufactured well's ground-state transform. Integration by
parts establishes positivity on actual compact C¹ test functions. Existence,
decay and the excitation gap of the specific resolvent-generated mode remain
separate analytic steps. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def planarAxis (a : Fin 2) : PlanarPosition := EuclideanSpace.single a 1

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarForcing
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.planarHeatResolventPrimitive_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The manuscript's explicit planar forcing `(1-|r|²)₊¹⁶`, including finite
smoothness at its support boundary. The positive-part power is represented
by a polynomial plus a fractional power of a square, avoiding a nonsmooth
positive-part differentiation rule. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem positivePartSixteen_formula (x : ℝ) :
    positivePartSixteen x = (x ^ 16 + x * (x ^ 2 : ℝ) ^ (15 / 2 : ℝ)) / 2 := by
  have hp : (x ^ 2 : ℝ) ^ (15 / 2 : ℝ) = |x| ^ 15 := by
    rw [Real.rpow_div_two_eq_sqrt (15 : ℝ) (sq_nonneg x), Real.sqrt_sq_eq_abs]
    norm_cast
  rw [hp]
  rcases le_total 0 x with hx | hx
  · rw [positivePartSixteen, max_eq_left hx, abs_of_nonneg hx]
    ring
  · rw [positivePartSixteen, max_eq_right hx, abs_of_nonpos hx]
    norm_num
    ring

theorem positivePartSixteen_C7 : ContDiff ℝ 7 positivePartSixteen := by
  have hs : ContDiff ℝ 7 (fun x : ℝ => x ^ 2) := contDiff_id.pow 2
  have hp : ContDiff ℝ 7 (fun x : ℝ => (x ^ 2 : ℝ) ^ (15 / 2 : ℝ)) :=
    hs.rpow_const_of_le (by norm_num : (7 : ℝ) ≤ 15 / 2)
  have heq : positivePartSixteen =
      fun x : ℝ => (x ^ 16 + x * (x ^ 2 : ℝ) ^ (15 / 2 : ℝ)) / 2 :=
    funext positivePartSixteen_formula
  rw [heq]
  exact ((contDiff_id.pow 16).add (contDiff_id.mul hp)).div_const 2

theorem planarForcing_C7 : ContDiff ℝ 7 planarForcing :=
  positivePartSixteen_C7.comp (contDiff_const.sub (contDiff_norm_sq ℝ))

theorem planarForcing_nonnegative (r : PlanarPosition) : 0 ≤ planarForcing r :=
  pow_nonneg (le_max_right _ _) _

theorem planarForcing_le_one (r : PlanarPosition) : planarForcing r ≤ 1 := by
  have hm : max (1 - ‖r‖ ^ 2) 0 ≤ 1 := max_le (by nlinarith [sq_nonneg ‖r‖]) zero_le_one
  change max (1 - ‖r‖ ^ 2) 0 ^ 16 ≤ 1
  simpa only [one_pow] using pow_le_pow_left₀ (le_max_right _ _) hm 16

theorem planarForcing_zero_of_norm_ge_one {r : PlanarPosition} (hr : 1 ≤ ‖r‖) :
    planarForcing r = 0 := by
  have hsq : 1 ≤ ‖r‖ ^ 2 := by nlinarith
  rw [planarForcing, positivePartSixteen, max_eq_right (by linarith)]
  norm_num

theorem planarForcing_support : tsupport planarForcing ⊆ Metric.closedBall 0 1 := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro r hr
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hn
  exact hr (planarForcing_zero_of_norm_ge_one (by linarith))

theorem planarForcing_hasCompactSupport : HasCompactSupport planarForcing :=
  (isCompact_closedBall (0 : PlanarPosition) 1).of_isClosed_subset
    (isClosed_tsupport _) planarForcing_support

theorem planarForcing_zero : planarForcing 0 = 1 := by
  norm_num [planarForcing, positivePartSixteen]

theorem planarForcing_integrable : Integrable planarForcing :=
  planarForcing_C7.continuous.integrable_of_hasCompactSupport planarForcing_hasCompactSupport

theorem planarForcing_integral_positive : 0 < ∫ r, planarForcing r :=
  integral_pos_of_integrable_nonneg_nonzero planarForcing_C7.continuous
    planarForcing_integrable planarForcing_nonnegative (by rw [planarForcing_zero]; norm_num)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarHeatKernel
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.planarHeatResolventPrimitive_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual normalized two-dimensional Gaussian heat kernel and its
convolution with the paper's explicit forcing. These prepare the positive
resolvent mode, rather than assuming the manufactured well exists. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem planarHeatKernel_positive {t : ℝ} (ht : 0 < t) (r : PlanarPosition) :
    0 < planarHeatKernel t r := by
  exact mul_pos (inv_pos.mpr (by positivity)) (Real.exp_pos _)

theorem planarHeatKernel_continuous (t : ℝ) : Continuous (planarHeatKernel t) := by
  unfold planarHeatKernel
  fun_prop

theorem planar_gaussian_integrable {b : ℝ} (hb : 0 < b) :
    Integrable (fun r : PlanarPosition => Real.exp (-b * ‖r‖ ^ 2)) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := PlanarPosition) (b := (b : ℂ)) (by simpa using hb) 0 0
  have hc : Integrable (fun r : PlanarPosition => Complex.exp ((-b * ‖r‖ ^ 2 : ℝ) : ℂ)) := by
    simpa only [zero_mul, add_zero, Complex.ofReal_mul, Complex.ofReal_neg,
      Complex.ofReal_pow] using h
  simpa only [Complex.norm_exp, Complex.ofReal_re] using hc.norm

theorem planarHeatKernel_integrable {t : ℝ} (ht : 0 < t) :
    Integrable (planarHeatKernel t) := by
  unfold planarHeatKernel
  have h := (planar_gaussian_integrable (b := (4 * t)⁻¹) (by positivity)).const_mul
    ((4 * Real.pi * t)⁻¹)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext r
  congr 2
  ring

theorem planarHeatKernel_integral {t : ℝ} (ht : 0 < t) :
    (∫ r, planarHeatKernel t r) = 1 := by
  have heq : (fun r : PlanarPosition => Real.exp (-‖r‖ ^ 2 / (4 * t))) =
      (fun r : PlanarPosition => Real.exp (-(4 * t)⁻¹ * ‖r‖ ^ 2)) := by
    funext r
    congr 1
    ring
  unfold planarHeatKernel
  rw [integral_const_mul, heq,
    GaussianFourier.integral_rexp_neg_mul_sq_norm (by positivity : 0 < (4 * t)⁻¹)]
  norm_num [finrank_euclideanSpace_fin]
  field_simp [ht.ne', Real.pi_ne_zero]

theorem planarHeatAverage_integrand_integrable {t : ℝ} (ht : 0 < t) (r : PlanarPosition) :
    Integrable (fun b => planarHeatKernel t b * planarForcing (r - b)) := by
  apply (planarHeatKernel_integrable ht).mul_bdd
    ((planarForcing_C7.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun b => by
    change ‖planarForcing (r - b)‖ ≤ (1 : ℝ)
    rw [Real.norm_eq_abs, abs_of_nonneg (planarForcing_nonnegative _)]
    exact planarForcing_le_one _)

theorem planarHeatAverage_positive {t : ℝ} (ht : 0 < t) (r : PlanarPosition) :
    0 < planarHeatAverage t r := by
  apply integral_pos_of_integrable_nonneg_nonzero
    ((planarHeatKernel_continuous t).mul
      (planarForcing_C7.continuous.comp (continuous_const.sub continuous_id)))
    (planarHeatAverage_integrand_integrable ht r)
    (fun b => mul_nonneg (planarHeatKernel_positive ht b).le (planarForcing_nonnegative _))
  change planarHeatKernel t r * planarForcing (r - r) ≠ 0
  simpa only [sub_self, planarForcing_zero, mul_one] using (planarHeatKernel_positive ht r).ne'

theorem planarHeatAverage_le_one {t : ℝ} (ht : 0 < t) (r : PlanarPosition) :
    planarHeatAverage t r ≤ 1 := by
  rw [← planarHeatKernel_integral ht]
  apply integral_mono (planarHeatAverage_integrand_integrable ht r) (planarHeatKernel_integrable ht)
  intro b
  exact mul_le_of_le_one_right (planarHeatKernel_positive ht b).le (planarForcing_le_one _)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarResolvent
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.planarHeatResolventPrimitive_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Construction of the actual positive finite-smooth planar resolvent mode.
Tonelli/Fubini give an L¹ resolvent kernel of mass one, so convolution with
the manuscript's compact forcing has C⁷ regularity. The resolvent differential
equation, quantitative tails and excitation gap are subsequent steps. -/

noncomputable section
open MeasureTheory Function
open scoped Convolution
namespace ContinuumCoulomb

theorem planarResolventIntegrand_measurable : Measurable planarResolventIntegrand := by
  unfold planarResolventIntegrand planarHeatKernel
  fun_prop

theorem planarResolventIntegrand_integrable :
    Integrable planarResolventIntegrand
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod (volume : Measure PlanarPosition)) := by
  apply (integrable_prod_iff planarResolventIntegrand_measurable.aestronglyMeasurable).mpr
  have hE : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Set.Ioi (0 : ℝ)) := by
    simpa only [neg_mul, one_mul] using exp_neg_integrableOn_Ioi 0 (by norm_num : (0 : ℝ) < 1)
  refine ⟨?_, hE.congr ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (planarHeatKernel_integrable ht).const_mul (Real.exp (-t))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hn (r : PlanarPosition) : ‖planarResolventIntegrand (t, r)‖ =
        Real.exp (-t) * planarHeatKernel t r := by
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · rfl
      · exact mul_nonneg (Real.exp_pos _).le (planarHeatKernel_positive ht r).le
    simp_rw [hn]
    rw [integral_const_mul, planarHeatKernel_integral ht, mul_one]

theorem planarResolventKernel_integrable : Integrable planarResolventKernel :=
  planarResolventIntegrand_integrable.integral_prod_right

theorem planarResolvent_forcing_integrable (r : PlanarPosition) :
    Integrable (fun p : ℝ × PlanarPosition => planarResolventIntegrand p * planarForcing (r - p.2))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod (volume : Measure PlanarPosition)) := by
  apply planarResolventIntegrand_integrable.mul_bdd
    ((planarForcing_C7.continuous.comp (continuous_const.sub continuous_snd)).aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun p => by
    change ‖planarForcing (r - p.2)‖ ≤ (1 : ℝ)
    rw [Real.norm_eq_abs, abs_of_nonneg (planarForcing_nonnegative _)]
    exact planarForcing_le_one _)

theorem planarResolventMode_C7 : ContDiff ℝ 7 planarResolventMode :=
  planarForcing_hasCompactSupport.contDiff_convolution_right
    (ContinuousLinearMap.mul ℝ ℝ) planarResolventKernel_integrable.locallyIntegrable planarForcing_C7

/-- This is exactly the Gaussian heat representation in the manuscript. -/
theorem planarResolventMode_heat_representation (r : PlanarPosition) :
    planarResolventMode r = ∫ t in Set.Ioi (0 : ℝ), Real.exp (-t) * planarHeatAverage t r := by
  unfold planarResolventMode planarResolventKernel
  simp_rw [← integral_mul_const]
  rw [← integral_integral_swap (planarResolvent_forcing_integrable r)]
  simp_rw [planarResolventIntegrand, mul_assoc, integral_const_mul]
  rfl

theorem planarResolventMode_heat_integrable (r : PlanarPosition) :
    IntegrableOn (fun t => Real.exp (-t) * planarHeatAverage t r) (Set.Ioi (0 : ℝ)) := by
  have h := (planarResolvent_forcing_integrable r).integral_prod_left
  change Integrable _ _
  simpa only [planarResolventIntegrand, mul_assoc, integral_const_mul, planarHeatAverage] using h

theorem planarResolventMode_positive (r : PlanarPosition) : 0 < planarResolventMode r := by
  rw [planarResolventMode_heat_representation]
  have hpos (t : ℝ) (ht : t ∈ Set.Ioi (0 : ℝ)) :
      0 < Real.exp (-t) * planarHeatAverage t r :=
    mul_pos (Real.exp_pos _) (planarHeatAverage_positive ht r)
  have hae : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
      (fun t => Real.exp (-t) * planarHeatAverage t r) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht using (hpos t ht).le
  apply (integral_pos_iff_support_of_nonneg_ae hae (planarResolventMode_heat_integrable r)).mpr
  have hs : Set.Ioi (0 : ℝ) ⊆ support (fun t => Real.exp (-t) * planarHeatAverage t r) :=
    fun t ht => (hpos t ht).ne'
  have hm : 0 < (volume.restrict (Set.Ioi (0 : ℝ))) (Set.Ioi (0 : ℝ)) := by simp
  exact hm.trans_le (measure_mono hs)

theorem planarResolventMode_le_one (r : PlanarPosition) : planarResolventMode r ≤ 1 := by
  rw [planarResolventMode_heat_representation, ← integral_exp_neg_Ioi_zero]
  apply integral_mono_ae (planarResolventMode_heat_integrable r)
    (by simpa only [IntegrableOn, neg_mul, one_mul] using
      exp_neg_integrableOn_Ioi 0 (by norm_num : (0 : ℝ) < 1))
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact mul_le_of_le_one_right (Real.exp_pos _).le (planarHeatAverage_le_one ht r)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarModeProperties
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.planarHeatResolventPrimitive_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positivity, finite L² normalization and compact support of the actual
manufactured planar potential. The differential eigen-equation and gap are
not assumed by these declarations. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem planarResolventMode_integrable : Integrable planarResolventMode :=
  planarResolventKernel_integrable.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ)
    planarForcing_integrable

theorem planarResolventMode_square_integrable : Integrable (fun r => planarResolventMode r ^ 2) := by
  apply planarResolventMode_integrable.mono'
    (planarResolventMode_C7.continuous.pow 2).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun r => by
    change ‖planarResolventMode r ^ 2‖ ≤ planarResolventMode r
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hp := planarResolventMode_positive r
    have hb := planarResolventMode_le_one r
    nlinarith)

theorem planarResolventMode_square_integral_positive :
    0 < ∫ r, planarResolventMode r ^ 2 :=
  integral_pos_of_integrable_nonneg_nonzero (planarResolventMode_C7.continuous.pow 2)
    planarResolventMode_square_integrable (fun _ => sq_nonneg _)
    (sq_pos_of_pos (planarResolventMode_positive 0)).ne'

def manufacturedPlanarWell (r : PlanarPosition) : ℝ :=
  -planarForcing r / (2 * planarResolventMode r)

theorem manufacturedPlanarWell_C7 : ContDiff ℝ 7 manufacturedPlanarWell :=
  planarForcing_C7.neg.div (contDiff_const.mul planarResolventMode_C7)
    (fun r => mul_ne_zero (by norm_num) (planarResolventMode_positive r).ne')

theorem manufacturedPlanarWell_support : tsupport manufacturedPlanarWell ⊆ tsupport planarForcing := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro r hr
  by_contra hn
  apply hr
  change -planarForcing r / (2 * planarResolventMode r) = 0
  rw [image_eq_zero_of_notMem_tsupport hn, neg_zero, zero_div]

theorem manufacturedPlanarWell_hasCompactSupport : HasCompactSupport manufacturedPlanarWell :=
  planarForcing_hasCompactSupport.of_isClosed_subset (isClosed_tsupport _)
    manufacturedPlanarWell_support

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedCoulomb
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite actual Coulomb interactions of the localized densities. Bounded
probability densities permit the existing elementary near/far Coulomb bound;
no interaction coefficient is introduced as a spectral input. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def localizedPotentialBound (freq : ℝ) : ℝ :=
  localizedAmplitudeBound freq ^ 2 * NeutralAtom.kernelBallMass 1 + 1

def localizedCoulombCoeff (freq : ℝ) (u v : PlanarPosition) : ℝ :=
  ∫ x, localizedDensity freq u x * NeutralAtom.potentialOf (localizedDensity freq v) x

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_RationalSquareRoot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certified evaluation of square roots of nonnegative rational samples.
The same finite dyadic procedure serves the fixed Gaussian constants and
softened Coulomb distances. -/

namespace ContinuumCoulomb.RationalSquareRoot
open ExactQuantumFactoring.BitStackProgram

def inputCode : (ℕ × ℚ) → List Bool := prodCode unaryCode ratCode

noncomputable opaque argumentProgram : Procedure inputCode DyadicRootProgram.rawCode
    (fun x => (x.1, x.2.num.toNat, x.2.den)) := by
  let p := Procedure.first unaryCode ratCode
  let q := Procedure.second unaryCode ratCode
  let num := ChargePrograms.intToNatProgram.comp (Procedure.ratNum.comp q)
  let den := Procedure.ratDen.comp q
  exact p.pair (num.pair den)

noncomputable opaque program : Procedure inputCode ratCode value :=
  (DyadicRootProgram.rawProgram.comp argumentProgram).congrFun (by intro x; rfl)

end ContinuumCoulomb.RationalSquareRoot

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_BisectionRegisters
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Common-denominator registers for approximate bisection.  Each update
doubles the denominator and uses only addition and doubling of numerators;
therefore every register gains at most one bit per iteration. -/

namespace ContinuumCoulomb.BisectionRegisters
open ExactQuantumFactoring.BitStackProgram

def code : Registers → List Bool :=
  prodCode intCode (prodCode intCode (prodCode Nat.bits Procedure.boolCode))

theorem code_length (r : Registers) : (code r).length =
    2 * r.1.natAbs.bits.length + 2 * r.2.1.natAbs.bits.length +
      2 * r.2.2.1.bits.length + 16 := by
  simp only [code, prodCode, intCode, intData, pairBits_length,
    Procedure.boolCode, List.length_singleton]
  omega

theorem bits_le_code (r : Registers) : bits r ≤ (code r).length := by
  rw [code_length]
  unfold bits
  omega

theorem code_le_bits (r : Registers) : (code r).length ≤ 6 * bits r + 16 := by
  rw [code_length]
  unfold bits
  omega

theorem add_bits_le_max (a b : ℤ) :
    (a + b).natAbs.bits.length ≤ max a.natAbs.bits.length b.natAbs.bits.length + 1 := by
  have hab : (a + b).natAbs ≤ 2 * max a.natAbs b.natAbs :=
    (Int.natAbs_add_le a b).trans (by omega)
  have h := (bits_length_mono hab).trans (double_bits_length (max a.natAbs b.natAbs))
  by_cases hm : a.natAbs ≤ b.natAbs
  · rw [max_eq_right hm] at h
    exact h.trans (Nat.add_le_add_right (le_max_right _ _) _)
  · rw [max_eq_left (le_of_not_ge hm)] at h
    exact h.trans (Nat.add_le_add_right (le_max_left _ _) _)

theorem double_int_bits (a : ℤ) :
    (2 * a).natAbs.bits.length ≤ a.natAbs.bits.length + 1 := by
  rw [Int.natAbs_mul]
  exact double_bits_length a.natAbs

theorem step_bits (δ : ℚ) (evaluate : ℚ → ℚ) (r : Registers) :
    bits (step δ evaluate r) ≤ bits r + 1 := by
  have ha := add_bits_le_max r.1 r.2.1
  have hl := double_int_bits r.1
  have hh := double_int_bits r.2.1
  have hd := double_bits_length r.2.2.1
  unfold step
  split_ifs <;> dsimp only [bits] <;> omega

theorem iterate_bits (δ : ℚ) (evaluate : ℚ → ℚ) (r : Registers) (n : ℕ) :
    bits ((step δ evaluate)^[n] r) ≤ bits r + n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (step_bits δ evaluate _).trans (by omega)

end ContinuumCoulomb.BisectionRegisters

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_BisectionProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal polynomial-time bisection with a supplied polynomial-time
rational evaluator.  The evaluator environment and tolerance remain in
the input registers; they are not fixed nonuniform advice. -/

namespace ContinuumCoulomb.BisectionProgram
open ExactQuantumFactoring.BitStackProgram
open BisectionRegisters

def configCode {E : Type} (ce : E → List Bool) : Config E → List Bool :=
  prodCode ce (prodCode ratCode code)

theorem config_length {E : Type} (ce : E → List Bool) (s : Config E) :
    (configCode ce s).length =
      2 * (ce s.1).length + 2 * (ratCode s.2.1).length + (code s.2.2).length + 2 := by
  simp only [configCode, prodCode, pairBits_length]
  omega

theorem iterate_code_bound {E : Type} (ce : E → List Bool) (evaluate : E → ℚ → ℚ)
    (n : ℕ) (s : Config E) (i : ℕ) (hi : i ≤ n) :
    (configCode ce ((advance evaluate)^[i] s)).length ≤
      (8 * (Polynomial.X + 1) ^ 2 + 20 : Polynomial ℕ).eval
        (n + (configCode ce s).length) := by
  rw [iterate_config, config_length]
  have hb := iterate_bits s.2.1 (evaluate s.1) s.2.2 i
  have hc := code_le_bits ((step s.2.1 (evaluate s.1))^[i] s.2.2)
  have hs := bits_le_code s.2.2
  have hlen := config_length ce s
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
  nlinarith

noncomputable def rationalLess : Procedure (prodCode ratCode ratCode)
    Procedure.boolCode (fun q => decide (q.1 < q.2)) := by
  -- `q₁ < q₂` is the negative sign of `q₁-q₂`.
  let sub' := Procedure.ratSub
  exact (Procedure.intSign.comp (Procedure.ratNum.comp sub')).congrFun (by
    intro q
    simp only [Function.comp_apply, Rat.num_neg, sub_neg])

noncomputable def middleProgram : Procedure code ratCode middle := by
  let lo := Procedure.first intCode (prodCode intCode (prodCode Nat.bits Procedure.boolCode))
  let tail := Procedure.second intCode (prodCode intCode (prodCode Nat.bits Procedure.boolCode))
  let hi := (Procedure.first intCode (prodCode Nat.bits Procedure.boolCode)).comp tail
  let db := (Procedure.second intCode (prodCode Nat.bits Procedure.boolCode)).comp tail
  let den := (Procedure.first Nat.bits Procedure.boolCode).comp db
  exact (Procedure.makeRat.comp ((Procedure.intAdd.comp (lo.pair hi)).pair
    (Procedure.double.comp den))).congrFun (by intro s; rfl)

noncomputable def advanceProgram {E : Type} {ce : E → List Bool}
    {evaluate : E → ℚ → ℚ}
    (evalProgram : Procedure (prodCode ce ratCode) ratCode (fun x => evaluate x.1 x.2)) :
    Procedure (configCode ce) (configCode ce) (advance evaluate) := by
  let env := Procedure.first ce (prodCode ratCode code)
  let tail := Procedure.second ce (prodCode ratCode code)
  let tolerance := (Procedure.first ratCode code).comp tail
  let regs := (Procedure.second ratCode code).comp tail
  let lo := (Procedure.first intCode (prodCode intCode (prodCode Nat.bits Procedure.boolCode))).comp regs
  let rest := (Procedure.second intCode (prodCode intCode (prodCode Nat.bits Procedure.boolCode))).comp regs
  let hi := (Procedure.first intCode (prodCode Nat.bits Procedure.boolCode)).comp rest
  let db := (Procedure.second intCode (prodCode Nat.bits Procedure.boolCode)).comp rest
  let den := (Procedure.first Nat.bits Procedure.boolCode).comp db
  let settled := (Procedure.second Nat.bits Procedure.boolCode).comp db
  let sum := Procedure.intAdd.comp (lo.pair hi)
  let two := Procedure.constant (configCode ce) intCode (2 : ℤ)
  let twiceLo := Procedure.intMul.comp (two.pair lo)
  let twiceHi := Procedure.intMul.comp (two.pair hi)
  let twiceDen := Procedure.double.comp den
  let no := Procedure.constant (configCode ce) Procedure.boolCode false
  let yes := Procedure.constant (configCode ce) Procedure.boolCode true
  let leftRegs := sum.pair (twiceHi.pair (twiceDen.pair no))
  let rightRegs := twiceLo.pair (sum.pair (twiceDen.pair no))
  let stoppedRegs := sum.pair (sum.pair (twiceDen.pair yes))
  let middle := middleProgram.comp regs
  let value := evalProgram.comp (env.pair middle)
  let positive := rationalLess.comp (tolerance.pair value)
  let negative := rationalLess.comp (value.pair (Procedure.ratNeg.comp tolerance))
  let moved := Procedure.conditional positive leftRegs
    (Procedure.conditional negative rightRegs stoppedRegs)
  let result := Procedure.conditional settled regs moved
  exact (env.pair (tolerance.pair result)).congrFun (by
    intro s
    simp only [advance, step, Function.comp_apply, decide_eq_true_eq])

noncomputable def repeatProgram {E : Type} {ce : E → List Bool}
    {evaluate : E → ℚ → ℚ}
    (evalProgram : Procedure (prodCode ce ratCode) ratCode (fun x => evaluate x.1 x.2)) :
    Procedure (prodCode (fun n => List.replicate n true) (configCode ce)) (configCode ce)
      (fun x => (advance evaluate)^[x.1] x.2) :=
  (advanceProgram evalProgram).iterate (8 * (Polynomial.X + 1) ^ 2 + 20)
    (iterate_code_bound ce evaluate)

noncomputable def initialProgram : Procedure (prodCode ratCode ratCode) code
    (fun p => initial p.1 p.2) := by
  let a := Procedure.first ratCode ratCode
  let b := Procedure.second ratCode ratCode
  let an := Procedure.ratNum.comp a
  let bn := Procedure.ratNum.comp b
  let ad := Procedure.ratDen.comp a
  let bd := Procedure.ratDen.comp b
  let lo := Procedure.intMul.comp (an.pair (Procedure.natToInt.comp bd))
  let hi := Procedure.intMul.comp (bn.pair (Procedure.natToInt.comp ad))
  let den := Procedure.binaryMul.comp (ad.pair bd)
  exact (lo.pair (hi.pair (den.pair
    (Procedure.constant (prodCode ratCode ratCode) Procedure.boolCode false)))).congrFun
      (by intro p; rfl)

def inputCode {E : Type} (ce : E → List Bool) : Input E → List Bool :=
  prodCode (fun n => List.replicate n true)
    (prodCode ce (prodCode ratCode (prodCode ratCode ratCode)))

noncomputable def program {E : Type} {ce : E → List Bool}
    {evaluate : E → ℚ → ℚ}
    (evalProgram : Procedure (prodCode ce ratCode) ratCode (fun x => evaluate x.1 x.2)) :
    Procedure (inputCode ce) ratCode (approximate evaluate) := by
  let n := Procedure.first (fun n => List.replicate n true)
    (prodCode ce (prodCode ratCode (prodCode ratCode ratCode)))
  let tail := Procedure.second (fun n => List.replicate n true)
    (prodCode ce (prodCode ratCode (prodCode ratCode ratCode)))
  let env := (Procedure.first ce (prodCode ratCode (prodCode ratCode ratCode))).comp tail
  let rest := (Procedure.second ce (prodCode ratCode (prodCode ratCode ratCode))).comp tail
  let tolerance := (Procedure.first ratCode (prodCode ratCode ratCode)).comp rest
  let endpoints := (Procedure.second ratCode (prodCode ratCode ratCode)).comp rest
  let config := env.pair (tolerance.pair (initialProgram.comp endpoints))
  let run := (repeatProgram evalProgram).comp (n.pair config)
  let extract := (Procedure.second ratCode code).comp (Procedure.second ce (prodCode ratCode code))
  exact (middleProgram.comp (extract.comp run)).congrFun (by
    intro x
    simp only [Function.comp_apply, iterate_config, approximate])

end ContinuumCoulomb.BisectionProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_CappedKernelProgram
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal rational approximation of the bounded three-dimensional
Coulomb kernel. Only a dyadic square root and rational arithmetic occur. -/

noncomputable section
namespace ContinuumCoulomb.CappedKernelProgram
open ExactQuantumFactoring.BitStackProgram

def position (q : Triple) : Position := WithLp.toLp 2 ![(q.1 : ℝ), (q.2.1 : ℝ), (q.2.2 : ℝ)]
def inputCode : Input → List Bool := prodCode (prodCode unaryCode ratCode) tripleCode

noncomputable opaque maximumProgram : Procedure (prodCode ratCode ratCode) ratCode
    (fun q => max q.1 q.2) := by
  exact (Procedure.conditional BisectionProgram.rationalLess
    (Procedure.second ratCode ratCode) (Procedure.first ratCode ratCode)).congrFun (by
      intro q
      simp only [decide_eq_true_eq]
      split_ifs with h
      · exact (max_eq_right h.le).symm
      · exact (max_eq_left (le_of_not_gt h)).symm)

noncomputable opaque normSquareProgram : Procedure tripleCode ratCode normSquare := by
  let x := Procedure.first ratCode (prodCode ratCode ratCode)
  let yz := Procedure.second ratCode (prodCode ratCode ratCode)
  let y := (Procedure.first ratCode ratCode).comp yz
  let z := (Procedure.second ratCode ratCode).comp yz
  let sx := Procedure.ratMul.comp (x.pair x)
  let sy := Procedure.ratMul.comp (y.pair y)
  let sz := Procedure.ratMul.comp (z.pair z)
  exact (Procedure.ratAdd.comp ((Procedure.ratAdd.comp (sx.pair sy)).pair sz)).congrFun
    (by intro q; simp only [normSquare, Function.comp_apply, pow_two])

noncomputable opaque program : Procedure inputCode ratCode approximate := by
  let params := Procedure.first (prodCode unaryCode ratCode) tripleCode
  let precision := (Procedure.first unaryCode ratCode).comp params
  let epsilon := (Procedure.second unaryCode ratCode).comp params
  let coords := Procedure.second (prodCode unaryCode ratCode) tripleCode
  let square := normSquareProgram.comp coords
  let root := RationalSquareRoot.program.comp (precision.pair square)
  let den := maximumProgram.comp (epsilon.pair root)
  exact (Procedure.ratDiv.comp ((Procedure.constant inputCode ratCode (1 : ℚ)).pair den)).congrFun
    (by intro x; simp only [approximate, Function.comp_apply, one_div])

end ContinuumCoulomb.CappedKernelProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_EulerRegisters
attribute [-simp] _root_.OAI.ContinuumCoulomb.CenteredGaussLabels.decode_index _root_.OAI.ContinuumCoulomb.CenteredGaussLabels.index_decode _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Three bounded integer numerator registers suffice for a rounded Euler
trajectory. The size invariant is unconditional on the supplied sampler;
it therefore supports polynomial-time iteration on every encoded input. -/

namespace ContinuumCoulomb.EulerRegisters
open ExactQuantumFactoring.BitStackProgram
open CappedKernelProgram (Triple)

def registersCode : Registers → List Bool := prodCode intCode (prodCode intCode intCode)
def parametersCode {E : Type} (ce : E → List Bool) : Parameters E → List Bool :=
  prodCode ce (prodCode Nat.bits (prodCode Nat.bits ratCode))
def configCode {E : Type} (ce : E → List Bool) : Config E → List Bool :=
  prodCode (parametersCode ce) (prodCode Nat.bits registersCode)

def point (D : ℕ) (r : Registers) : Triple :=
  ((r.1:ℚ)/D,((r.2.1:ℚ)/D,(r.2.2:ℚ)/D))

def round (D B : ℕ) (q : Triple) : Registers :=
  (RationalBoxRound.numerator D B q.1,
    (RationalBoxRound.numerator D B q.2.1,RationalBoxRound.numerator D B q.2.2))

def proposal (h : ℚ) (q v : Triple) : Triple :=
  (q.1+h*v.1,(q.2.1+h*v.2.1,q.2.2+h*v.2.2))

def advance {E : Type} (evaluate : E → ℚ → Triple → Triple) (c : Config E) : Config E :=
  let q := point c.1.2.1 c.2.2
  let h := c.1.2.2.2
  let v := evaluate c.1.1 ((c.2.1:ℚ)*h) q
  (c.1,(c.2.1+1,round c.1.2.1 c.1.2.2.1 (proposal h q v)))

theorem parameters_length {E : Type} (ce : E → List Bool) (p : Parameters E) :
    (parametersCode ce p).length = 2*(ce p.1).length+2*p.2.1.bits.length+
      2*p.2.2.1.bits.length+(ratCode p.2.2.2).length+3 := by
  simp only [parametersCode,prodCode,pairBits_length]
  omega

theorem config_length {E : Type} (ce : E → List Bool) (c : Config E) :
    (configCode ce c).length = 2*(parametersCode ce c.1).length+2*c.2.1.bits.length+
      2*c.2.2.1.natAbs.bits.length+2*c.2.2.2.1.natAbs.bits.length+
      c.2.2.2.2.natAbs.bits.length+19 := by
  simp only [configCode,registersCode,prodCode,pairBits_length,intCode,intData,
    Procedure.boolCode,List.length_singleton]
  omega

theorem iterate_parameters {E : Type} (evaluate : E → ℚ → Triple → Triple)
    (c : Config E) (n : ℕ) : ((advance evaluate)^[n] c).1 = c.1 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [Function.iterate_succ_apply',advance] using ih

theorem iterate_counter {E : Type} (evaluate : E → ℚ → Triple → Triple)
    (c : Config E) (n : ℕ) : ((advance evaluate)^[n] c).2.1 = c.2.1+n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    change ((advance evaluate)^[n] c).2.1+1 = c.2.1+(n+1)
    rw [ih]
    omega

theorem iterate_register_bounds {E : Type} (evaluate : E → ℚ → Triple → Triple)
    (c : Config E) {n : ℕ} (hn : 0 < n) :
    let r := ((advance evaluate)^[n] c).2.2
    r.1.natAbs.bits.length ≤ c.1.2.2.1.bits.length ∧
      r.2.1.natAbs.bits.length ≤ c.1.2.2.1.bits.length ∧
      r.2.2.natAbs.bits.length ≤ c.1.2.2.1.bits.length := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rw [Function.iterate_succ_apply']
  simp only [advance,round]
  rw [iterate_parameters]
  exact ⟨RationalBoxRound.numerator_bits _ _ _,RationalBoxRound.numerator_bits _ _ _,
    RationalBoxRound.numerator_bits _ _ _⟩

theorem iterate_code_bound {E : Type} (ce : E → List Bool)
    (evaluate : E → ℚ → Triple → Triple) (n : ℕ) (c : Config E) (i : ℕ) (hi : i ≤ n) :
    (configCode ce ((advance evaluate)^[i] c)).length ≤
      (32*(Polynomial.X+1)^2 : Polynomial ℕ).eval (n+(configCode ce c).length) := by
  let L := (configCode ce c).length
  have hlen := config_length ce c
  have hp := parameters_length ce c.1
  have hB : c.1.2.2.1.bits.length ≤ L := by dsimp [L]; omega
  have hk : c.2.1.bits.length ≤ L := by dsimp [L]; omega
  have hpar : (parametersCode ce c.1).length ≤ L := by dsimp [L]; omega
  have hsize : (configCode ce ((advance evaluate)^[i] c)).length ≤ 9*L+2*n+24 := by
    by_cases hz : i=0
    · subst i
      simp only [Function.iterate_zero_apply]
      dsimp [L]
      omega
    · have hr := iterate_register_bounds evaluate c (Nat.pos_of_ne_zero hz)
      have hc := bits_length_add c.2.1 i
      have hiBits := ExactQuantumFactoring.NativeAIG.nat_bits_length_bound i
      rw [config_length,iterate_parameters,iterate_counter]
      omega
  apply hsize.trans
  simp only [Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_pow,Polynomial.eval_add,
    Polynomial.eval_X,Polynomial.eval_one]
  change 9*L+2*n+24 ≤ 32*(n+L+1)^2
  nlinarith

end ContinuumCoulomb.EulerRegisters

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_EulerTrajectory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual clipped-register iteration obeys the proved Euler error
estimate. All numerical values here are the rational register values;
the hypotheses concern the usual velocity error, speed and Lipschitz bounds. -/

noncomputable section
namespace ContinuumCoulomb.EulerRegisters
open CappedKernelProgram (Triple position)

variable {E : Type}

def trajectory (evaluate : E → ℚ → Triple → Triple) (e : E) (N D B : ℕ)
    (r : Registers) (n : ℕ) : Triple :=
  point D (((advance evaluate)^[n] (initial e N D B r)).2.2)

end ContinuumCoulomb.EulerRegisters

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_EulerInitialBox
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A binary-encoded box radius computed directly from the three input
rational numerators encloses the true bounded-speed trajectory. -/

noncomputable section
namespace ContinuumCoulomb.EulerRegisters
open CappedKernelProgram (Triple position)

def inputRadius (q : Triple) : ℕ := q.1.num.natAbs+q.2.1.num.natAbs+q.2.2.num.natAbs

def boxNumerator (C D : ℕ) (q : Triple) : ℕ := D*(inputRadius q+C+1)

end ContinuumCoulomb.EulerRegisters

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_FieldAnalysis_CoulombTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology ContDiff
noncomputable section
namespace Coulomb

variable {Ω : Set Space} (hΩ : MeasurableSet Ω) [IsFiniteMeasure (volume.restrict Ω)]

def testCharge (χ : Space → ℝ) : Space → ℝ :=
  fun x => -(NeutralAtom.coordinateLaplacian χ x)/(4*Real.pi)

omit hΩ [IsFiniteMeasure (volume.restrict Ω)] in
lemma testCharge_continuous {χ : Space → ℝ} (hχ : ContDiff ℝ ∞ χ) :
    Continuous (testCharge χ) :=
  (NeutralAtom.continuous_coordinateLaplacian (hχ.of_le (by exact WithTop.coe_le_coe.mpr le_top))).neg.div_const _

omit hΩ [IsFiniteMeasure (volume.restrict Ω)] in
lemma testCharge_compact {χ : Space → ℝ} (hc : HasCompactSupport χ) :
    HasCompactSupport (testCharge χ) := by
  apply hc.mono'
  intro x hx
  by_contra hn
  exact hx (by simp only [testCharge,NeutralAtom.coordinateLaplacian_eq_zero_of_notMem_tsupport hn,neg_zero,zero_div])

end Coulomb

end

end
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedFourIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four-index Coulomb integrals of the actual localized orbitals. Each
unequal-index pair gives exponentially small Coulomb coefficients, uniformly
in the other pair. Diagonal pairs recover the actual direct interaction. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem localizedPotentialBound_nonnegative (freq : ℝ) : 0 ≤ localizedPotentialBound freq := by
  unfold localizedPotentialBound NeutralAtom.kernelBallMass
  exact add_nonneg (mul_nonneg (sq_nonneg _) (integral_nonneg (fun _ =>
    NeutralAtom.coulombKernel_nonneg _))) zero_le_one

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarHopping
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.planarHeatResolventPrimitive_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual positive contact hopping integral. Its Lipschitz control is
inherited from the compact forcing through the mass-one resolvent kernel. -/

noncomputable section
open MeasureTheory
open scoped NNReal
namespace ContinuumCoulomb

theorem forcing_lipschitz_exists : ∃ C : ℝ≥0, LipschitzWith C planarForcing :=
  ContDiff.lipschitzWith_of_hasCompactSupport planarForcing_hasCompactSupport
    planarForcing_C7 (by norm_num)

def planarForcingLipschitzConstant : ℝ≥0 := Classical.choose forcing_lipschitz_exists

def planarHoppingIntegrand (d : ℝ) (r : PlanarPosition) : ℝ :=
  planarForcing r * planarResolventMode (r - d • planarAxis 0)

theorem planarHoppingIntegrand_continuous (d : ℝ) : Continuous (planarHoppingIntegrand d) :=
  planarForcing_C7.continuous.mul
    (planarResolventMode_C7.continuous.comp (continuous_id.sub continuous_const))

theorem planarHoppingIntegrand_integrable (d : ℝ) : Integrable (planarHoppingIntegrand d) :=
  (planarHoppingIntegrand_continuous d).integrable_of_hasCompactSupport
    planarForcing_hasCompactSupport.mul_right

theorem planarHoppingIntegrand_nonnegative (d : ℝ) (r : PlanarPosition) :
    0 ≤ planarHoppingIntegrand d r :=
  mul_nonneg (planarForcing_nonnegative r) (planarResolventMode_positive _).le

def planarHopping (d : ℝ) : ℝ :=
  (∫ r, planarHoppingIntegrand d r) / (2 * ∫ r, planarResolventMode r ^ 2)

theorem planarHopping_positive (d : ℝ) : 0 < planarHopping d := by
  apply div_pos _ (mul_pos (by norm_num) planarResolventMode_square_integral_positive)
  apply integral_pos_of_integrable_nonneg_nonzero
    (planarHoppingIntegrand_continuous d) (planarHoppingIntegrand_integrable d)
    (planarHoppingIntegrand_nonnegative d)
  change planarForcing 0 * planarResolventMode (0 - d • planarAxis 0) ≠ 0
  rw [planarForcing_zero, one_mul]
  exact (planarResolventMode_positive _).ne'

def planarHoppingLipschitzConstant : ℝ≥0 :=
  ⟨planarForcingLipschitzConstant * (∫ r, planarForcing r) /
      (2 * ∫ r, planarResolventMode r ^ 2), by
    exact div_nonneg (mul_nonneg (NNReal.coe_nonneg _) planarForcing_integral_positive.le)
      (mul_nonneg (by norm_num) planarResolventMode_square_integral_positive.le)⟩

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CoulombPacketTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite packet combinations and the exact global Poisson duality for
smooth compact tests. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace ContinuumCoulomb.CoulombPacket

def test (χ : Position → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) : CoulombPacket :=
  ofCompact (Coulomb.testCharge χ) (Coulomb.testCharge_continuous hχ) (Coulomb.testCharge_compact hc)

end ContinuumCoulomb.CoulombPacket

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedCoulombTranslation
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Direct Coulomb coefficients as actual translated-density profiles. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def planarCenter (u : PlanarPosition) : Position := positionSplitCoordinates.symm (u, 0)

def localizedCoulombProfileAt (freq : ℝ) (u : PlanarPosition) : ℝ :=
  ∫ x, localizedDensity freq 0 x *
    NeutralAtom.potentialOf (localizedDensity freq 0) (x - planarCenter u)

def localizedCoulombProfile (freq d : ℝ) : ℝ :=
  localizedCoulombProfileAt freq (d • planarAxis 0)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedDualMatrix
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete compact bumps supply local duality for the actual mode densities. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace ContinuumCoulomb

def localDualMass (freq : ℝ) : ℝ :=
  ∫ x, localizedDensity freq 0 x * localDualBump x

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedGram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coercivity of the actual full Coulomb Gram matrix of the localized
resolvent--Gaussian modes. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace ContinuumCoulomb

def localDualEnergyBound : ℝ := |∫ x : Position, Coulomb.testCharge localDualBump x * localDualBump x| + 1

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedGramConstants
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed positive coercivity constant once the total off-site leakage is
at most half the common diagonal dual mass. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def localizedGramConstant (freq : ℝ) : ℝ :=
  localDualMass freq ^ 2 / (4 * localDualEnergyBound)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CoulombCalibration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform contact calibration for the actual Coulomb profile, with a
single polynomial scale also enforcing the many-site Gram bound. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

def coulombHoppingTarget (freq τ K d : ℝ) : ℝ :=
  τ * Real.sqrt (K * (localizedCoulombProfile freq 0 - localizedCoulombProfile freq d))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarFieldBounds
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual planar counterterm field has uniform derivative bounds,
independent of the number of sites. Separated unit supports leave at most
one nonzero summand at every point. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

theorem planarWell_derivatives_bounded :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, k ≤ 6 → ∀ r : PlanarPosition,
      ‖iteratedFDeriv ℝ k manufacturedPlanarWell r‖ ≤ C := by
  have hb (k : Fin 7) : ∃ C : ℝ, ∀ r : PlanarPosition,
      ‖iteratedFDeriv ℝ k.val manufacturedPlanarWell r‖ ≤ C :=
    (manufacturedPlanarWell_C7.continuous_iteratedFDeriv (by exact_mod_cast k.isLt.le)).bounded_above_of_compact_support
      (manufacturedPlanarWell_hasCompactSupport.iteratedFDeriv k.val)
  choose B hB using hb
  let C : ℝ := 1+∑ k : Fin 7, max (B k) 0
  have hn : 0 ≤ ∑ k : Fin 7, max (B k) 0 :=
    Finset.sum_nonneg (fun _ _ => le_max_right _ _)
  refine ⟨C, by dsimp [C]; linarith, ?_⟩
  intro k hk r
  let j : Fin 7 := ⟨k, by omega⟩
  have hs : max (B j) 0 ≤ ∑ k : Fin 7, max (B k) 0 :=
    Finset.single_le_sum (fun _ _ => le_max_right _ _) (Finset.mem_univ j)
  exact (hB j r).trans ((le_max_left _ _).trans (by dsimp [C]; linarith))

def planarWellDerivativeConstant : ℝ := Classical.choose planarWell_derivatives_bounded

theorem planarWellDerivativeConstant_positive : 0 < planarWellDerivativeConstant :=
  (Classical.choose_spec planarWell_derivatives_bounded).1

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ManufacturedFieldBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform derivatives through order six of the actual three-dimensional
manufactured field. Constants do not grow with the number of wells or slab width. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

def wellPlanarProjection : Position →L[ℝ] PlanarPosition :=
  (ContinuousLinearMap.fst ℝ PlanarPosition ℝ).comp positionSplitCoordinates.toContinuousLinearMap

def wellVerticalProjection : Position →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ PlanarPosition ℝ).comp positionSplitCoordinates.toContinuousLinearMap

def wellPlanarDerivativeBound : ℝ :=
  (2*planarWellDerivativeConstant)*(max 1 ‖wellPlanarProjection‖)^6

theorem cutoff_derivative_bound_exists : ∃ C : ℝ, 0 < C ∧
    ∀ k ≤ 6, ∀ z : ℝ, ‖iteratedFDeriv ℝ k (verticalCutoffBump : ℝ → ℝ) z‖ ≤ C := by
  obtain ⟨B,hB,hb⟩ := verticalCutoffBump.hasCompactSupport.exists_bound_iteratedFDeriv
    (𝕜 := ℝ) verticalCutoffBump.contDiff 6
  exact ⟨B+1, by linarith, fun k hk z => (hb k hk z).trans (by linarith)⟩

def wellCutoffDerivativeConstant : ℝ := Classical.choose cutoff_derivative_bound_exists

def wellCutoffDerivativeBound : ℝ :=
  wellCutoffDerivativeConstant*(max 1 (2*‖wellVerticalProjection‖))^6

def manufacturedFieldDerivativeConstant : ℝ :=
  64*wellCutoffDerivativeBound*wellPlanarDerivativeBound

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_RationalFieldDifferences
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate differences of a rational scalar sampler approximate the
actual gradient and Laplacian. The real extension below is only a proof
device; the numerical expressions evaluate the sampler at rational points. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb.RationalFieldDifferences
open CappedKernelProgram (Triple position)
open NeutralAtom (axis dirPartial coordinateLaplacian)

def shift (q : Triple) (h : ℚ) (a : Fin 3) : Triple :=
  (q.1+(if a=0 then h else 0),
    (q.2.1+(if a=1 then h else 0),q.2.2+(if a=2 then h else 0)))

def first (sample : Triple → ℚ) (h : ℚ) (q : Triple) (a : Fin 3) : ℚ :=
  (sample (shift q h a)-sample q)/h

def second (sample : Triple → ℚ) (h : ℚ) (q : Triple) (a : Fin 3) : ℚ :=
  (sample (shift q h a)+sample (shift q (-h) a)-2*sample q)/h^2

def laplacian (sample : Triple → ℚ) (h : ℚ) (q : Triple) : ℚ := ∑ a, second sample h q a

end ContinuumCoulomb.RationalFieldDifferences

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_MoserDifferenceBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed polynomial precision parameters for coordinate differences of
the manufactured field. Both the spatial step and scalar accuracy are
chosen from its already proved uniform six-derivative bound. -/

noncomputable section
namespace ContinuumCoulomb.MoserDifferenceBudget

def guard : ℕ := ⌈manufacturedFieldDerivativeConstant⌉₊+1

def step (P : ℕ) : ℚ := (16*(guard:ℚ)*(P+1))⁻¹
def precision (P : ℕ) : ℕ := 16384*guard^2*(P+1)^3

end ContinuumCoulomb.MoserDifferenceBudget

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_PlanarForcingProgram
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact rational evaluation of the actual compact planar forcing.
Only rational arithmetic and a sign test occur. -/

namespace ContinuumCoulomb.PlanarForcingProgram
open ExactQuantumFactoring.BitStackProgram

def position (q : ℚ × ℚ) : PlanarPosition := WithLp.toLp 2 ![(q.1 : ℝ), (q.2 : ℝ)]

noncomputable def program : Procedure (prodCode ratCode ratCode) ratCode value := by
  let x := Procedure.first ratCode ratCode
  let y := Procedure.second ratCode ratCode
  let xsq := Procedure.ratMul.comp (x.pair x)
  let ysq := Procedure.ratMul.comp (y.pair y)
  let squareSum := Procedure.ratAdd.comp (xsq.pair ysq)
  let one := Procedure.constant (prodCode ratCode ratCode) ratCode (1 : ℚ)
  let zero := Procedure.constant (prodCode ratCode ratCode) ratCode (0 : ℚ)
  let z := Procedure.ratSub.comp (one.pair squareSum)
  let negative := Procedure.intSign.comp (Procedure.ratNum.comp z)
  let positive := Procedure.conditional negative zero z
  let second := Procedure.ratMul.comp (positive.pair positive)
  let fourth := Procedure.ratMul.comp (second.pair second)
  let eighth := Procedure.ratMul.comp (fourth.pair fourth)
  let sixteenth := Procedure.ratMul.comp (eighth.pair eighth)
  exact sixteenth.congrFun (by
    intro q
    simp only [Function.comp_apply, Rat.num_neg, decide_eq_true_eq]
    unfold value
    simp only [pow_two]
    split_ifs with h
    · rw [max_eq_right (le_of_lt h)]
      norm_num
    · rw [max_eq_left (le_of_not_gt h)]
      ring)

end ContinuumCoulomb.PlanarForcingProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_RationalTaylorRegisters
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A shared-denominator Taylor recurrence for arbitrary rational inputs.
The numerator may be signed. Register size grows polynomially in the
iteration count and the encoded numerator and denominator lengths. -/

namespace ContinuumCoulomb.RationalTaylorRegisters
open ExactQuantumFactoring.BitStackProgram
open scoped BigOperators

def code : State → List Bool := prodCode intCode
  (prodCode Nat.bits (prodCode Nat.bits (prodCode intCode (prodCode Nat.bits intCode))))

theorem iterate_initial (q : ℚ) (n : ℕ) :
    ((step^[n]) (initial q)).1 = q.num ∧
    ((step^[n]) (initial q)).2.1 = q.den ∧
    ((step^[n]) (initial q)).2.2.1 = n ∧
    (((step^[n]) (initial q)).2.2.2.1 : ℚ) =
      (n.factorial * q.den ^ n : ℕ) * RationalExponential.taylorSum q n ∧
    ((step^[n]) (initial q)).2.2.2.2.1 = n.factorial * q.den ^ n ∧
    ((step^[n]) (initial q)).2.2.2.2.2 = q.num ^ n := by
  induction n with
  | zero => simp [initial, RationalExponential.taylorSum]
  | succ n ih =>
    rcases ih with ⟨ha, hb, hj, hA, hF, hP⟩
    rw [Function.iterate_succ_apply']
    refine ⟨ha, hb, ?_, ?_, ?_, ?_⟩
    · change ((step^[n]) (initial q)).2.2.1 + 1 = n + 1
      rw [hj]
    · change (((((((step^[n]) (initial q)).2.2.1 + 1) *
        ((step^[n]) (initial q)).2.1 : ℕ) : ℤ) *
        (((step^[n]) (initial q)).2.2.2.1 +
          ((step^[n]) (initial q)).2.2.2.2.2) : ℤ) : ℚ) = _
      push_cast
      rw [hj, hb, hA, hP]
      have hden : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
      have hnum : (q.num : ℚ) = q * q.den := by
        calc
          (q.num : ℚ) = ((q.num : ℚ) / q.den) * q.den := by field_simp
          _ = q * q.den := by rw [Rat.num_div_den]
      simp only [Nat.cast_mul, Nat.cast_pow, RationalExponential.taylorSum,
        Finset.sum_range_succ, Nat.factorial_succ, Nat.cast_add, Nat.cast_one,
        hnum, mul_pow, Int.cast_pow, pow_succ]
      have hfac : (n.factorial : ℚ) ≠ 0 := by positivity
      field_simp
    · change (((step^[n]) (initial q)).2.2.1 + 1) *
        ((step^[n]) (initial q)).2.1 * ((step^[n]) (initial q)).2.2.2.2.1 = _
      rw [hj, hb, hF, Nat.factorial_succ, pow_succ]
      ring
    · change ((step^[n]) (initial q)).1 * ((step^[n]) (initial q)).2.2.2.2.2 = _
      rw [ha, hP, pow_succ, mul_comm]

theorem result_correct (q : ℚ) (n : ℕ) :
    result ((step^[n]) (initial q)) = RationalExponential.taylorSum q n := by
  obtain ⟨_, _, _, hA, hF, _⟩ := iterate_initial q n
  have hpos : 0 < q.den := q.pos
  have hden : (n.factorial * q.den ^ n : ℚ) ≠ 0 := by positivity
  unfold result
  rw [Rat.mkRat_eq_div, hA, hF]
  push_cast
  field_simp

theorem code_length (s : State) : (code s).length =
    2 * s.1.natAbs.bits.length + 2 * s.2.1.bits.length + 2 * s.2.2.1.bits.length +
      2 * s.2.2.2.1.natAbs.bits.length + 2 * s.2.2.2.2.1.bits.length +
        s.2.2.2.2.2.natAbs.bits.length + 20 := by
  simp only [code, prodCode, intCode, intData, pairBits_length,
    Procedure.boolCode, List.length_singleton]
  omega

theorem measure_le_code (s : State) : measure s ≤ (code s).length := by
  rw [code_length]
  unfold measure
  omega

theorem code_le_measure (s : State) : (code s).length ≤ 3 * measure s + 20 := by
  rw [code_length]
  unfold measure
  omega

theorem int_add_bits (a b : ℤ) :
    (a + b).natAbs.bits.length ≤ max a.natAbs.bits.length b.natAbs.bits.length + 1 :=
  (bits_length_mono (Int.natAbs_add_le a b)).trans (AmplificationProgram.bits_add_max _ _)

theorem step_measure (s : State) : measure (step s) ≤
    measure s + s.1.natAbs.bits.length + 2 * s.2.1.bits.length + 2 * s.2.2.1.bits.length + 4 := by
  have hj := AmplificationProgram.bits_succ s.2.2.1
  have hf := bits_length_mul (s.2.2.1 + 1) s.2.1
  have hA := bits_length_mul ((s.2.2.1 + 1) * s.2.1)
    (s.2.2.2.1 + s.2.2.2.2.2).natAbs
  have ha := int_add_bits s.2.2.2.1 s.2.2.2.2.2
  have hF := bits_length_mul ((s.2.2.1 + 1) * s.2.1) s.2.2.2.2.1
  have hP := bits_length_mul s.1.natAbs s.2.2.2.2.2.natAbs
  have hm : max
      (((((s.2.2.1 + 1) * s.2.1 : ℕ) : ℤ) *
        (s.2.2.2.1 + s.2.2.2.2.2)).natAbs.bits.length)
      ((s.1 * s.2.2.2.2.2).natAbs.bits.length) ≤
      max s.2.2.2.1.natAbs.bits.length s.2.2.2.2.2.natAbs.bits.length +
        s.1.natAbs.bits.length + s.2.1.bits.length + s.2.2.1.bits.length + 2 := by
    simp only [Int.natAbs_mul, Int.natAbs_natCast]
    apply max_le <;> omega
  dsimp only [measure, step]
  omega

theorem iterate_measure (s : State) (n : ℕ) :
    measure ((step^[n]) s) ≤ measure s + n * (5 * measure s + 2 * n + 4) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have hstep := step_measure ((step^[n]) s)
    obtain ⟨ha, hb, hj⟩ := iterate_parameters s n
    rw [ha, hb] at hstep
    have h1 : s.1.natAbs.bits.length ≤ measure s := by unfold measure; omega
    have h2 : s.2.1.bits.length ≤ measure s := by unfold measure; omega
    have h3 : s.2.2.1.bits.length ≤ measure s := by unfold measure; omega
    nlinarith

theorem iterate_code_bound (n : ℕ) (s : State) (i : ℕ) (hi : i ≤ n) :
    (code ((step^[i]) s)).length ≤
      (64 * (Polynomial.X + 1) ^ 2 + 100 : Polynomial ℕ).eval (n + (code s).length) := by
  have hc := code_le_measure ((step^[i]) s)
  have hm := iterate_measure s i
  have hs := measure_le_code s
  have hp := Nat.pow_le_pow_left hi 2
  have hmul := Nat.mul_le_mul hi hs
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
  nlinarith

end ContinuumCoulomb.RationalTaylorRegisters

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_RationalExponentialProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A polynomial-time rational exponential evaluator. Magnitude and
precision bounds are supplied in unary; the rational argument and result
are encoded in binary. Every arithmetic operation is an actual stack
program, including the shared-denominator Taylor recurrence. -/

namespace ContinuumCoulomb.RationalExponentialProgram
open ExactQuantumFactoring.BitStackProgram
open RationalTaylorRegisters

noncomputable def stepProgram : Procedure code code step := by
  let a := Procedure.first intCode
    (prodCode Nat.bits (prodCode Nat.bits (prodCode intCode (prodCode Nat.bits intCode))))
  let s₁ := Procedure.second intCode
    (prodCode Nat.bits (prodCode Nat.bits (prodCode intCode (prodCode Nat.bits intCode))))
  let b := (Procedure.first Nat.bits (prodCode Nat.bits (prodCode intCode (prodCode Nat.bits intCode)))).comp s₁
  let s₂ := (Procedure.second Nat.bits (prodCode Nat.bits (prodCode intCode (prodCode Nat.bits intCode)))).comp s₁
  let j := (Procedure.first Nat.bits (prodCode intCode (prodCode Nat.bits intCode))).comp s₂
  let s₃ := (Procedure.second Nat.bits (prodCode intCode (prodCode Nat.bits intCode))).comp s₂
  let A := (Procedure.first intCode (prodCode Nat.bits intCode)).comp s₃
  let s₄ := (Procedure.second intCode (prodCode Nat.bits intCode)).comp s₃
  let F := (Procedure.first Nat.bits intCode).comp s₄
  let P := (Procedure.second Nat.bits intCode).comp s₄
  let next := Procedure.successor.comp j
  let factor := Procedure.binaryMul.comp (next.pair b)
  let nextA := Procedure.intMul.comp ((Procedure.natToInt.comp factor).pair
    (Procedure.intAdd.comp (A.pair P)))
  let nextF := Procedure.binaryMul.comp (factor.pair F)
  let nextP := Procedure.intMul.comp (a.pair P)
  exact (a.pair (b.pair (next.pair (nextA.pair (nextF.pair nextP))))).congrFun
    (by intro s; rfl)

noncomputable def repeatProgram : Procedure (prodCode unaryCode code) code
    (fun x => (step^[x.1]) x.2) :=
  stepProgram.iterate (64 * (Polynomial.X + 1) ^ 2 + 100) iterate_code_bound

noncomputable def initialProgram : Procedure ratCode code initial := by
  let a := Procedure.ratNum
  let b := Procedure.ratDen
  let zero := Procedure.constant ratCode Nat.bits 0
  let zeroInt := Procedure.constant ratCode intCode (0 : ℤ)
  let one := Procedure.constant ratCode Nat.bits 1
  let oneInt := Procedure.constant ratCode intCode (1 : ℤ)
  exact (a.pair (b.pair (zero.pair (zeroInt.pair (one.pair oneInt))))).congrFun
    (by intro q; rfl)

noncomputable def resultProgram : Procedure code ratCode result := by
  let s₁ := Procedure.second intCode
    (prodCode Nat.bits (prodCode Nat.bits (prodCode intCode (prodCode Nat.bits intCode))))
  let s₂ := (Procedure.second Nat.bits (prodCode Nat.bits (prodCode intCode (prodCode Nat.bits intCode)))).comp s₁
  let s₃ := (Procedure.second Nat.bits (prodCode intCode (prodCode Nat.bits intCode))).comp s₂
  let A := (Procedure.first intCode (prodCode Nat.bits intCode)).comp s₃
  let s₄ := (Procedure.second intCode (prodCode Nat.bits intCode)).comp s₃
  let F := (Procedure.first Nat.bits intCode).comp s₄
  exact (Procedure.makeRat.comp (A.pair F)).congrFun (by intro s; rfl)

noncomputable def partialProgram : Procedure (prodCode unaryCode ratCode) ratCode
    (fun x => RationalExponential.taylorSum x.2 x.1) := by
  let n := Procedure.first unaryCode ratCode
  let q := Procedure.second unaryCode ratCode
  let run := repeatProgram.comp (n.pair (initialProgram.comp q))
  exact (resultProgram.comp run).congrFun (by intro x; exact result_correct x.2 x.1)

noncomputable def orderProgram : Procedure (prodCode unaryCode unaryCode) unaryCode
    (fun x => RationalExponential.order x.1 x.2) := by
  let m := Procedure.first unaryCode unaryCode
  let p := Procedure.second unaryCode unaryCode
  let two := Procedure.constant (prodCode unaryCode unaryCode) unaryCode 2
  let square := Procedure.unaryMul.comp (m.pair m)
  let twiceSquare := Procedure.unaryMul.comp (two.pair square)
  let sum := Procedure.unaryAdd.comp
    ((Procedure.unaryAdd.comp (twiceSquare.pair p)).pair two)
  exact (Procedure.unaryMul.comp (two.pair sum)).congrFun (by
    intro x
    change 2 * (2 * (x.1 * x.1) + x.2 + 2) = RationalExponential.order x.1 x.2
    unfold RationalExponential.order
    ring)

def inputCode : Input → List Bool := prodCode unaryCode (prodCode unaryCode ratCode)

noncomputable def program : Procedure inputCode ratCode approximate := by
  let m := Procedure.first unaryCode (prodCode unaryCode ratCode)
  let tail := Procedure.second unaryCode (prodCode unaryCode ratCode)
  let p := (Procedure.first unaryCode ratCode).comp tail
  let q := (Procedure.second unaryCode ratCode).comp tail
  let order := orderProgram.comp (m.pair p)
  exact (partialProgram.comp (order.pair q)).congrFun (by intro x; rfl)

end ContinuumCoulomb.RationalExponentialProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_RationalHeatSample
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual rational evaluation of the heat-resolvent integrand. Both π and
the exponential are computed by rational approximation programs.
Clamping the computed π below by one keeps every denominator quantitative. -/

namespace ContinuumCoulomb.RationalHeatSample
open ExactQuantumFactoring.BitStackProgram

noncomputable def safePiProgram : Procedure unaryCode ratCode safePi := by
  let q := PiProgram.program
  let one := Procedure.constant unaryCode ratCode (1 : ℚ)
  let difference := Procedure.ratSub.comp (q.pair one)
  let negative := Procedure.intSign.comp (Procedure.ratNum.comp difference)
  exact (Procedure.conditional negative one q).congrFun (by
    intro N
    simp only [Function.comp_apply, Rat.num_neg, decide_eq_true_eq]
    unfold safePi
    split_ifs with h
    · rw [max_eq_left (by linarith)]
    · rw [max_eq_right (by linarith)])

def pointCode : Point → List Bool := prodCode ratCode ratCode
def argumentsCode : Arguments → List Bool := prodCode ratCode (prodCode pointCode pointCode)
def settingsCode : Settings → List Bool := prodCode unaryCode (prodCode unaryCode unaryCode)
def inputCode : Input → List Bool := prodCode settingsCode argumentsCode

noncomputable def exponentProgram : Procedure argumentsCode ratCode exponent := by
  let t := Procedure.first ratCode (prodCode pointCode pointCode)
  let xy := Procedure.second ratCode (prodCode pointCode pointCode)
  let x := (Procedure.first pointCode pointCode).comp xy
  let y := (Procedure.second pointCode pointCode).comp xy
  let dx := Procedure.ratSub.comp
    (((Procedure.first ratCode ratCode).comp x).pair ((Procedure.first ratCode ratCode).comp y))
  let dy := Procedure.ratSub.comp
    (((Procedure.second ratCode ratCode).comp x).pair ((Procedure.second ratCode ratCode).comp y))
  let normSq := Procedure.ratAdd.comp
    ((Procedure.ratMul.comp (dx.pair dx)).pair (Procedure.ratMul.comp (dy.pair dy)))
  let four := Procedure.constant argumentsCode ratCode (4 : ℚ)
  let denom := Procedure.ratMul.comp (four.pair t)
  let gaussian := Procedure.ratDiv.comp (normSq.pair denom)
  exact (Procedure.ratSub.comp ((Procedure.ratNeg.comp t).pair gaussian)).congrFun
    (by intro a; simp only [exponent, pow_two]; rfl)

noncomputable def program : Procedure inputCode ratCode value := by
  let settings := Procedure.first settingsCode argumentsCode
  let args := Procedure.second settingsCode argumentsCode
  let M := (Procedure.first unaryCode (prodCode unaryCode unaryCode)).comp settings
  let pn := (Procedure.second unaryCode (prodCode unaryCode unaryCode)).comp settings
  let p := (Procedure.first unaryCode unaryCode).comp pn
  let N := (Procedure.second unaryCode unaryCode).comp pn
  let expArg := M.pair (p.pair (exponentProgram.comp args))
  let exponential := RationalExponentialProgram.program.comp expArg
  let xy := (Procedure.second ratCode (prodCode pointCode pointCode)).comp args
  let y := (Procedure.second pointCode pointCode).comp xy
  let forcing := PlanarForcingProgram.program.comp y
  let numerator := Procedure.ratMul.comp (exponential.pair forcing)
  let t := (Procedure.first ratCode (prodCode pointCode pointCode)).comp args
  let pi := safePiProgram.comp N
  let four := Procedure.constant inputCode ratCode (4 : ℚ)
  let denominator := Procedure.ratMul.comp ((Procedure.ratMul.comp (four.pair pi)).pair t)
  exact (Procedure.ratDiv.comp (numerator.pair denominator)).congrFun (by intro x; rfl)

end ContinuumCoulomb.RationalHeatSample

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_RationalHeatBox
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Three literal nested quadratures for the heat representation of the
planar resolvent. The two spatial integrals run over `[-1,1]`, which
contains the support of the forcing. All sample counts are unary. -/

namespace ContinuumCoulomb.RationalHeatBox
open ExactQuantumFactoring.BitStackProgram
open RationalHeatSample

def settingsCode : Settings → List Bool :=
  prodCode RationalHeatSample.settingsCode (prodCode pointCode unaryCode)

def planeCode : PlaneEnvironment → List Bool := prodCode settingsCode ratCode
def lineCode : LineEnvironment → List Bool := prodCode planeCode ratCode

def inputCode : Input → List Bool := RationalQuadratureProgram.inputCode settingsCode

noncomputable def sampleProgram :
    Procedure (prodCode lineCode ratCode) ratCode (fun x => sample x.1 x.2) := by
  let lineEnv := Procedure.first lineCode ratCode
  let y₂ := Procedure.second lineCode ratCode
  let planeEnv := (Procedure.first planeCode ratCode).comp lineEnv
  let y₁ := (Procedure.second planeCode ratCode).comp lineEnv
  let setting := (Procedure.first settingsCode ratCode).comp planeEnv
  let t := (Procedure.second settingsCode ratCode).comp planeEnv
  let constants := (Procedure.first RationalHeatSample.settingsCode
    (prodCode pointCode unaryCode)).comp setting
  let pointAndCount := (Procedure.second RationalHeatSample.settingsCode
    (prodCode pointCode unaryCode)).comp setting
  let point := (Procedure.first pointCode unaryCode).comp pointAndCount
  let args := constants.pair (t.pair (point.pair (y₁.pair y₂)))
  exact (RationalHeatSample.program.comp args).congrFun (by intro x; rfl)

noncomputable def lineInputProgram :
    Procedure (prodCode planeCode ratCode) (RationalQuadratureProgram.inputCode lineCode)
      (fun x => lineInput x.1 x.2) := by
  let e := Procedure.first planeCode ratCode
  let y := Procedure.second planeCode ratCode
  let setting := (Procedure.first settingsCode ratCode).comp e
  let pointAndCount := (Procedure.second RationalHeatSample.settingsCode
    (prodCode pointCode unaryCode)).comp setting
  let N := (Procedure.second pointCode unaryCode).comp pointAndCount
  let count := Procedure.natToRat.comp (Procedure.unaryToBits.comp N)
  let two := Procedure.constant (prodCode planeCode ratCode) ratCode (2 : ℚ)
  let h := Procedure.ratDiv.comp (two.pair count)
  let a := Procedure.constant (prodCode planeCode ratCode) ratCode (-1 : ℚ)
  exact (N.pair ((e.pair y).pair (a.pair h))).congrFun (by intro x; rfl)

noncomputable def lineProgram :
    Procedure (prodCode planeCode ratCode) ratCode (fun x => line x.1 x.2) :=
  ((RationalQuadratureProgram.program lineCode sample sampleProgram).comp lineInputProgram).congrFun
    (by intro x; rfl)

noncomputable def planeInputProgram :
    Procedure (prodCode settingsCode ratCode) (RationalQuadratureProgram.inputCode planeCode)
      (fun x => planeInput x.1 x.2) := by
  let e := Procedure.first settingsCode ratCode
  let t := Procedure.second settingsCode ratCode
  let pointAndCount := (Procedure.second RationalHeatSample.settingsCode
    (prodCode pointCode unaryCode)).comp e
  let N := (Procedure.second pointCode unaryCode).comp pointAndCount
  let count := Procedure.natToRat.comp (Procedure.unaryToBits.comp N)
  let two := Procedure.constant (prodCode settingsCode ratCode) ratCode (2 : ℚ)
  let h := Procedure.ratDiv.comp (two.pair count)
  let a := Procedure.constant (prodCode settingsCode ratCode) ratCode (-1 : ℚ)
  exact (N.pair ((e.pair t).pair (a.pair h))).congrFun (by intro x; rfl)

noncomputable def planeProgram :
    Procedure (prodCode settingsCode ratCode) ratCode (fun x => plane x.1 x.2) :=
  ((RationalQuadratureProgram.program planeCode line lineProgram).comp planeInputProgram).congrFun
    (by intro x; rfl)

noncomputable def program : Procedure inputCode ratCode value :=
  (RationalQuadratureProgram.program settingsCode plane planeProgram).congrFun
    (by intro x; rfl)

end ContinuumCoulomb.RationalHeatBox

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ResolventSchedule
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal polynomial-sized mesh and precision choices for the resolvent
quadrature. The radius and requested inverse accuracy are unary inputs. -/

namespace ContinuumCoulomb.ResolventSchedule
open ExactQuantumFactoring.BitStackProgram

def inputCode : Input → List Bool :=
  prodCode (prodCode unaryCode unaryCode) RationalHeatSample.pointCode

noncomputable opaque scaleProgram : Procedure unaryCode unaryCode scale := by
  let sixteen := Procedure.constant unaryCode unaryCode 16
  exact (mulProgram.comp (sixteen.pair Procedure.unarySuccessor)).congrFun
    (by intro P; rfl)

noncomputable opaque fourthProgram : Procedure unaryCode unaryCode (fun n => n ^ 4) :=
  (squareProgram.comp squareProgram).congrFun (by intro n; dsimp; ring)

noncomputable opaque eighthProgram : Procedure unaryCode unaryCode (fun n => n ^ 8) :=
  (squareProgram.comp fourthProgram).congrFun (by intro n; dsimp; ring)

noncomputable opaque constant4096Program :
    Procedure (prodCode unaryCode unaryCode) unaryCode (fun _ => 4096) :=
  (fourthProgram.comp (Procedure.constant (prodCode unaryCode unaryCode) unaryCode 8)).congrFun
    (by intro x; norm_num)

noncomputable opaque radiusOffsetProgram : Procedure (prodCode unaryCode unaryCode) unaryCode
    (fun x : ℕ × ℕ => x.1 + 3) :=
  (addProgram.comp ((Procedure.first unaryCode unaryCode).pair
    (Procedure.constant (prodCode unaryCode unaryCode) unaryCode 3))).congrFun
      (by intro x; rfl)

noncomputable opaque radiusFourthProgram : Procedure (prodCode unaryCode unaryCode) unaryCode
    (fun x : ℕ × ℕ => (x.1 + 3) ^ 4) :=
  fourthProgram.comp radiusOffsetProgram

noncomputable opaque scaleEighthProgram : Procedure (prodCode unaryCode unaryCode) unaryCode
    (fun x : ℕ × ℕ => scale x.2 ^ 8) :=
  eighthProgram.comp (scaleProgram.comp (Procedure.second unaryCode unaryCode))

noncomputable opaque countPrefixProgram : Procedure (prodCode unaryCode unaryCode) unaryCode
    (fun x : ℕ × ℕ => countPrefix x.1) :=
  (mulProgram.comp (constant4096Program.pair radiusFourthProgram)).congrFun
    (by intro x; rfl)

noncomputable opaque countFactorsProgram :
    Procedure (prodCode unaryCode unaryCode) (prodCode unaryCode unaryCode)
      (fun x : ℕ × ℕ => (countPrefix x.1, scale x.2 ^ 8)) :=
  countPrefixProgram.pair scaleEighthProgram

noncomputable opaque countRawProgram : Procedure (prodCode unaryCode unaryCode) unaryCode
    (fun x : ℕ × ℕ => countPrefix x.1 * scale x.2 ^ 8) :=
  mulProgram.comp countFactorsProgram

theorem count_value (x : ℕ × ℕ) : countPrefix x.1 * scale x.2 ^ 8 = count x.1 x.2 := by
  unfold count
  rfl

noncomputable opaque countProgram : Procedure (prodCode unaryCode unaryCode) unaryCode
    (fun x => count x.1 x.2) := countRawProgram.congrFun count_value

noncomputable opaque magnitudeProgram : Procedure (prodCode unaryCode unaryCode) unaryCode
    (fun x => magnitude x.1 x.2) := by
  let R := Procedure.first unaryCode unaryCode
  let Q := scaleProgram.comp (Procedure.second unaryCode unaryCode)
  let three := Procedure.constant (prodCode unaryCode unaryCode) unaryCode 3
  let R3 := addProgram.comp (R.pair three)
  let square := squareProgram.comp R3
  exact (mulProgram.comp (square.pair Q)).congrFun (by
    intro x
    rfl)

noncomputable opaque precisionProgram : Procedure unaryCode unaryCode precision := by
  let four := Procedure.constant unaryCode unaryCode 4
  exact (mulProgram.comp (four.pair scaleProgram)).congrFun (by intro P; rfl)

noncomputable opaque argumentProgram :
    Procedure inputCode RationalHeatBox.inputCode argument := by
  let rp := Procedure.first (prodCode unaryCode unaryCode) RationalHeatSample.pointCode
  let point := Procedure.second (prodCode unaryCode unaryCode) RationalHeatSample.pointCode
  let P := (Procedure.second unaryCode unaryCode).comp rp
  let Q := scaleProgram.comp P
  let N := countProgram.comp rp
  let M := magnitudeProgram.comp rp
  let p := precisionProgram.comp P
  let Qrat := Procedure.natToRat.comp (Procedure.unaryToBits.comp Q)
  let Nrat := Procedure.natToRat.comp (Procedure.unaryToBits.comp N)
  let eta := Procedure.ratInv.comp Qrat
  let width := Procedure.ratSub.comp (Qrat.pair eta)
  let step := Procedure.ratDiv.comp (width.pair Nrat)
  let settings := (M.pair (p.pair N)).pair (point.pair N)
  exact (N.pair (settings.pair (eta.pair step))).congrFun (by intro x; rfl)

noncomputable opaque program : Procedure inputCode ExactQuantumFactoring.BitStackProgram.ratCode approximate :=
  (RationalHeatBox.program.comp argumentProgram).congrFun (by intro x; rfl)

end ContinuumCoulomb.ResolventSchedule

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_RationalGaussNodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational initial nodes for the tensor Gauss rule on mesh `1/N`.
The only irrational constant is evaluated by the existing dyadic square-root
program; the error bound is uniform over the entire integer lattice. -/

noncomputable section
open scoped NNReal
namespace ContinuumCoulomb.RationalGaussNodes
open CappedKernelProgram (Triple position)
open EulerRegisters (Registers)

def abscissa (P : ℕ) : ℚ := RationalSquareRoot.value (2*(P+1),(1/3:ℚ))
def signed (P : ℕ) (b : Bool) : ℚ := if b then abscissa P else -abscissa P
def value (P N : ℕ) (k : Registers) (b : Signs) : Triple :=
  (((k.1:ℚ)+signed P b.1/2)/N,
    (((k.2.1:ℚ)+signed P b.2.1/2)/N,((k.2.2:ℚ)+signed P b.2.2/2)/N))

end ContinuumCoulomb.RationalGaussNodes

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_EulerVectorPrograms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational vector arithmetic and bounded rounding for the three Euler
registers. These are literal finite compositions of integer and rational
stack programs. -/

namespace ContinuumCoulomb.EulerRegisters
open ExactQuantumFactoring.BitStackProgram
open CappedKernelProgram (Triple tripleCode)

def pointInputCode : (ℕ×Registers) → List Bool := prodCode Nat.bits registersCode
def proposalCode : (ℚ×(Triple×Triple)) → List Bool := prodCode ratCode (prodCode tripleCode tripleCode)
def roundInputCode : ((ℕ×ℕ)×Triple) → List Bool := prodCode (prodCode Nat.bits Nat.bits) tripleCode

noncomputable opaque pointDenominatorProgram : Procedure pointInputCode ratCode
    (fun x => (x.1:ℚ)) := Procedure.natToRat.comp (Procedure.first Nat.bits registersCode)
noncomputable opaque pointRegistersProgram : Procedure pointInputCode registersCode Prod.snd :=
  Procedure.second Nat.bits registersCode
noncomputable opaque firstRegisterProgram : Procedure registersCode intCode Prod.fst :=
  Procedure.first intCode (prodCode intCode intCode)
noncomputable opaque tailRegisterProgram : Procedure registersCode (prodCode intCode intCode) Prod.snd :=
  Procedure.second intCode (prodCode intCode intCode)
noncomputable opaque secondRegisterProgram : Procedure registersCode intCode (fun r => r.2.1) :=
  (Procedure.first intCode intCode).comp tailRegisterProgram
noncomputable opaque thirdRegisterProgram : Procedure registersCode intCode (fun r => r.2.2) :=
  (Procedure.second intCode intCode).comp tailRegisterProgram

noncomputable opaque pointFirstProgram : Procedure pointInputCode ratCode (fun x => (x.2.1:ℚ)/x.1) :=
  Procedure.ratDiv.comp ((Procedure.intToRat.comp (firstRegisterProgram.comp pointRegistersProgram)).pair
    pointDenominatorProgram)
noncomputable opaque pointSecondProgram : Procedure pointInputCode ratCode (fun x => (x.2.2.1:ℚ)/x.1) :=
  Procedure.ratDiv.comp ((Procedure.intToRat.comp (secondRegisterProgram.comp pointRegistersProgram)).pair
    pointDenominatorProgram)
noncomputable opaque pointThirdProgram : Procedure pointInputCode ratCode (fun x => (x.2.2.2:ℚ)/x.1) :=
  Procedure.ratDiv.comp ((Procedure.intToRat.comp (thirdRegisterProgram.comp pointRegistersProgram)).pair
    pointDenominatorProgram)

noncomputable opaque pointProgram : Procedure pointInputCode tripleCode (fun x => point x.1 x.2) :=
  pointFirstProgram.pair (pointSecondProgram.pair pointThirdProgram)

noncomputable opaque tripleFirstProgram : Procedure tripleCode ratCode Prod.fst :=
  Procedure.first ratCode (prodCode ratCode ratCode)
noncomputable opaque tripleTailProgram : Procedure tripleCode (prodCode ratCode ratCode) Prod.snd :=
  Procedure.second ratCode (prodCode ratCode ratCode)
noncomputable opaque tripleSecondProgram : Procedure tripleCode ratCode (fun q => q.2.1) :=
  (Procedure.first ratCode ratCode).comp tripleTailProgram
noncomputable opaque tripleThirdProgram : Procedure tripleCode ratCode (fun q => q.2.2) :=
  (Procedure.second ratCode ratCode).comp tripleTailProgram

noncomputable opaque proposalStepProgram : Procedure proposalCode ratCode Prod.fst :=
  Procedure.first ratCode (prodCode tripleCode tripleCode)
noncomputable opaque proposalPairProgram : Procedure proposalCode (prodCode tripleCode tripleCode) Prod.snd :=
  Procedure.second ratCode (prodCode tripleCode tripleCode)
noncomputable opaque proposalPointProgram : Procedure proposalCode tripleCode (fun x => x.2.1) :=
  (Procedure.first tripleCode tripleCode).comp proposalPairProgram
noncomputable opaque proposalVelocityProgram : Procedure proposalCode tripleCode (fun x => x.2.2) :=
  (Procedure.second tripleCode tripleCode).comp proposalPairProgram

noncomputable opaque proposalCoordinateProgram {f : Triple → ℚ} (p : Procedure tripleCode ratCode f) :
    Procedure proposalCode ratCode (fun x => f x.2.1+x.1*f x.2.2) := by
  let a := p.comp proposalPointProgram
  let b := p.comp proposalVelocityProgram
  exact Procedure.ratAdd.comp (a.pair (Procedure.ratMul.comp (proposalStepProgram.pair b)))

noncomputable opaque proposalProgram : Procedure proposalCode tripleCode
    (fun x => proposal x.1 x.2.1 x.2.2) :=
  (proposalCoordinateProgram tripleFirstProgram).pair
    ((proposalCoordinateProgram tripleSecondProgram).pair (proposalCoordinateProgram tripleThirdProgram))

noncomputable opaque roundParametersProgram : Procedure roundInputCode (prodCode Nat.bits Nat.bits) Prod.fst :=
  Procedure.first (prodCode Nat.bits Nat.bits) tripleCode
noncomputable opaque roundPointProgram : Procedure roundInputCode tripleCode Prod.snd :=
  Procedure.second (prodCode Nat.bits Nat.bits) tripleCode

noncomputable opaque roundCoordinateProgram {f : Triple → ℚ} (p : Procedure tripleCode ratCode f) :
    Procedure roundInputCode intCode (fun x => RationalBoxRound.numerator x.1.1 x.1.2 (f x.2)) :=
  RationalBoxRound.numeratorProgram.comp (roundParametersProgram.pair (p.comp roundPointProgram))

noncomputable opaque roundProgram : Procedure roundInputCode registersCode
    (fun x => round x.1.1 x.1.2 x.2) :=
  (roundCoordinateProgram tripleFirstProgram).pair
    ((roundCoordinateProgram tripleSecondProgram).pair (roundCoordinateProgram tripleThirdProgram))

end ContinuumCoulomb.EulerRegisters

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_GaussNodeProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal polynomial-time generation of an initial rational tensor-Gauss
node. Integer lattice coordinates and the reciprocal mesh denominator are
binary; the approximation precision is unary. -/

namespace ContinuumCoulomb.RationalGaussNodes
open ExactQuantumFactoring.BitStackProgram
open CappedKernelProgram (Triple tripleCode)
open EulerRegisters (registersCode)

def signsCode : Signs → List Bool := prodCode Procedure.boolCode
  (prodCode Procedure.boolCode Procedure.boolCode)
def inputCode : Input → List Bool := prodCode unaryCode (prodCode Nat.bits (prodCode registersCode signsCode))

noncomputable opaque precisionProgram : Procedure unaryCode unaryCode (fun P => 2*(P+1)) :=
  Procedure.unaryMul.comp ((Procedure.constant unaryCode unaryCode 2).pair Procedure.unarySuccessor)
noncomputable opaque abscissaProgram : Procedure unaryCode ratCode abscissa := by
  let p := RationalSquareRoot.program.comp (precisionProgram.pair
    (Procedure.constant unaryCode ratCode (1/3:ℚ)))
  exact p.congrFun (by intro P; rfl)
noncomputable opaque signedProgram : Procedure (prodCode unaryCode Procedure.boolCode) ratCode
    (fun x => signed x.1 x.2) := by
  let p := abscissaProgram.comp (Procedure.first unaryCode Procedure.boolCode)
  let b := Procedure.second unaryCode Procedure.boolCode
  exact (Procedure.conditional b p (Procedure.ratNeg.comp p)).congrFun (by
    intro x
    cases h : x.2 <;> simp only [Function.comp_apply,Bool.false_eq_true,ite_false, if_false,ite_true, if_true,signed])

def coordinateCode : CoordinateInput → List Bool := prodCode (prodCode unaryCode Nat.bits)
  (prodCode intCode Procedure.boolCode)
noncomputable opaque coordinateParametersProgram : Procedure coordinateCode (prodCode unaryCode Nat.bits) Prod.fst :=
  Procedure.first _ _
noncomputable opaque coordinateDataProgram : Procedure coordinateCode (prodCode intCode Procedure.boolCode) Prod.snd :=
  Procedure.second _ _
noncomputable opaque coordinatePrecisionProgram : Procedure coordinateCode unaryCode (fun x => x.1.1) :=
  (Procedure.first unaryCode Nat.bits).comp coordinateParametersProgram
noncomputable opaque coordinateDenominatorProgram : Procedure coordinateCode ratCode (fun x => (x.1.2:ℚ)) :=
  Procedure.natToRat.comp ((Procedure.second unaryCode Nat.bits).comp coordinateParametersProgram)
noncomputable opaque coordinateIntegerProgram : Procedure coordinateCode ratCode (fun x => (x.2.1:ℚ)) :=
  Procedure.intToRat.comp ((Procedure.first intCode Procedure.boolCode).comp coordinateDataProgram)
noncomputable opaque coordinateSignProgram : Procedure coordinateCode Procedure.boolCode (fun x => x.2.2) :=
  (Procedure.second intCode Procedure.boolCode).comp coordinateDataProgram
noncomputable opaque coordinateHalfProgram : Procedure coordinateCode ratCode
    (fun x => signed x.1.1 x.2.2/2) :=
  Procedure.ratDiv.comp ((signedProgram.comp (coordinatePrecisionProgram.pair coordinateSignProgram)).pair
    (Procedure.constant coordinateCode ratCode (2:ℚ)))
noncomputable opaque coordinateProgram : Procedure coordinateCode ratCode
    (fun x => ((x.2.1:ℚ)+signed x.1.1 x.2.2/2)/x.1.2) :=
  Procedure.ratDiv.comp ((Procedure.ratAdd.comp (coordinateIntegerProgram.pair coordinateHalfProgram)).pair
    coordinateDenominatorProgram)

noncomputable opaque dataProgram : Procedure inputCode (prodCode Nat.bits (prodCode registersCode signsCode)) Prod.snd :=
  Procedure.second unaryCode _
noncomputable opaque parametersProgram : Procedure inputCode (prodCode unaryCode Nat.bits)
    (fun x => (x.1,x.2.1)) :=
  (Procedure.first unaryCode _).pair ((Procedure.first Nat.bits _).comp dataProgram)
noncomputable opaque nodeDataProgram : Procedure inputCode (prodCode registersCode signsCode)
    (fun x => x.2.2) := (Procedure.second Nat.bits _).comp dataProgram
noncomputable opaque registersProgram : Procedure inputCode registersCode (fun x => x.2.2.1) :=
  (Procedure.first registersCode signsCode).comp nodeDataProgram
noncomputable opaque signsProgram : Procedure inputCode signsCode (fun x => x.2.2.2) :=
  (Procedure.second registersCode signsCode).comp nodeDataProgram
noncomputable opaque signFirstProgram : Procedure signsCode Procedure.boolCode Prod.fst := Procedure.first _ _
noncomputable opaque signTailProgram : Procedure signsCode (prodCode Procedure.boolCode Procedure.boolCode) Prod.snd :=
  Procedure.second _ _
noncomputable opaque signSecondProgram : Procedure signsCode Procedure.boolCode (fun x => x.2.1) :=
  (Procedure.first _ _).comp signTailProgram
noncomputable opaque signThirdProgram : Procedure signsCode Procedure.boolCode (fun x => x.2.2) :=
  (Procedure.second _ _).comp signTailProgram

noncomputable opaque program : Procedure inputCode tripleCode
    (fun x => value x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  let a := coordinateProgram.comp (parametersProgram.pair
    ((EulerRegisters.firstRegisterProgram.comp registersProgram).pair (signFirstProgram.comp signsProgram)))
  let b := coordinateProgram.comp (parametersProgram.pair
    ((EulerRegisters.secondRegisterProgram.comp registersProgram).pair (signSecondProgram.comp signsProgram)))
  let c := coordinateProgram.comp (parametersProgram.pair
    ((EulerRegisters.thirdRegisterProgram.comp registersProgram).pair (signThirdProgram.comp signsProgram)))
  exact a.pair (b.pair c)

end ContinuumCoulomb.RationalGaussNodes

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CoulombTargetLipschitz
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A quantitative modulus for the actual calibrated hopping residual.
The Coulomb gap keeps the square root away from zero, so ordinary dyadic
bisection needs no lower derivative bound. -/

noncomputable section
namespace ContinuumCoulomb

def coulombTargetLipschitzConstant (freq τ K : ℝ) : ℝ :=
  τ*Real.sqrt K*localizedCoulombLipschitzConstant freq/(2*Real.sqrt (localizedGramConstant freq))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_RationalRectangleProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal two-coordinate rational quadrature. The same mesh in both
coordinates is enough for the normalization and compact contact integrals. -/

namespace ContinuumCoulomb.RationalRectangleProgram
open ExactQuantumFactoring.BitStackProgram

variable {E : Type}

noncomputable opaque lineInputProgram (ce : E → List Bool) :
    Procedure (prodCode (inputCode ce) ratCode)
      (RationalQuadratureProgram.inputCode (prodCode ce ratCode)) lineInput := by
  let e := Procedure.first (inputCode ce) ratCode
  let x := Procedure.second (inputCode ce) ratCode
  let n := (Procedure.first unaryCode (RationalQuadratureProgram.environmentCode ce)).comp e
  let env := (Procedure.second unaryCode (RationalQuadratureProgram.environmentCode ce)).comp e
  let data := (Procedure.first ce (prodCode ratCode ratCode)).comp env
  let mesh := (Procedure.second ce (prodCode ratCode ratCode)).comp env
  exact (n.pair ((data.pair x).pair mesh)).congrFun (by intro q; rfl)

noncomputable opaque outerInputProgram (ce : E → List Bool) :
    Procedure (inputCode ce) (RationalQuadratureProgram.inputCode (inputCode ce)) outerInput := by
  let n := Procedure.first unaryCode (RationalQuadratureProgram.environmentCode ce)
  let env := Procedure.second unaryCode (RationalQuadratureProgram.environmentCode ce)
  let mesh := (Procedure.second ce (prodCode ratCode ratCode)).comp env
  exact (n.pair ((Procedure.identity (inputCode ce)).pair mesh)).congrFun (by intro q; rfl)

noncomputable opaque program (ce : E → List Bool) (evaluate : E → ℚ → ℚ → ℚ)
    (p : Procedure (prodCode (prodCode ce ratCode) ratCode) ratCode
      (fun q => evaluate q.1.1 q.1.2 q.2)) :
    Procedure (inputCode ce) ratCode (value evaluate) := by
  let inner := (RationalQuadratureProgram.program (prodCode ce ratCode)
    (fun q y => evaluate q.1 q.2 y) p).comp (lineInputProgram ce)
  exact ((RationalQuadratureProgram.program (inputCode ce) (line evaluate)
    inner).comp (outerInputProgram ce)).congrFun (by intro q; rfl)

end ContinuumCoulomb.RationalRectangleProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_RationalSixQuadrature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Six-coordinate rational cubature, as three literal rectangle programs.
The same finite mesh is retained in each register environment. -/

namespace ContinuumCoulomb.RationalSixQuadrature
open ExactQuantumFactoring.BitStackProgram

variable {E : Type}

noncomputable opaque augmentProgram (ce : E → List Bool) :
    Procedure (prodCode (prodCode (RationalRectangleProgram.inputCode ce) ratCode) ratCode)
      (RationalRectangleProgram.inputCode (prodCode ce pairCode))
      (fun x => augment x.1.1 x.1.2 x.2) := by
  let xa := Procedure.first (prodCode (RationalRectangleProgram.inputCode ce) ratCode) ratCode
  let x := (Procedure.first (RationalRectangleProgram.inputCode ce) ratCode).comp xa
  let a := (Procedure.second (RationalRectangleProgram.inputCode ce) ratCode).comp xa
  let b := Procedure.second (prodCode (RationalRectangleProgram.inputCode ce) ratCode) ratCode
  let n := (Procedure.first unaryCode (RationalQuadratureProgram.environmentCode ce)).comp x
  let env := (Procedure.second unaryCode (RationalQuadratureProgram.environmentCode ce)).comp x
  let data := (Procedure.first ce pairCode).comp env
  let mesh := (Procedure.second ce pairCode).comp env
  exact (n.pair ((data.pair (a.pair b)).pair mesh)).congrFun (by intro q; rfl)

noncomputable opaque middleProgram (ce : E → List Bool) (f : Evaluator E)
    (p : Procedure (prodCode (prodCode (prodCode (prodCode ce pairCode) pairCode) ratCode) ratCode)
      ratCode (fun x => inner f x.1.1 x.1.2 x.2)) :
    Procedure (prodCode (prodCode (RationalRectangleProgram.inputCode (prodCode ce pairCode)) ratCode) ratCode)
      ratCode (fun x => middle f x.1.1 x.1.2 x.2) :=
  ((RationalRectangleProgram.program (prodCode (prodCode ce pairCode) pairCode) (inner f) p).comp
    (augmentProgram (prodCode ce pairCode))).congrFun (by intro q; rfl)

noncomputable opaque outerProgram (ce : E → List Bool) (f : Evaluator E)
    (p : Procedure (prodCode (prodCode (prodCode (prodCode ce pairCode) pairCode) ratCode) ratCode)
      ratCode (fun x => inner f x.1.1 x.1.2 x.2)) :
    Procedure (prodCode (prodCode (RationalRectangleProgram.inputCode ce) ratCode) ratCode)
      ratCode (fun x => outer f x.1.1 x.1.2 x.2) := by
  let rectangle := RationalRectangleProgram.program
    (RationalRectangleProgram.inputCode (prodCode ce pairCode)) (middle f) (middleProgram ce f p)
  exact (rectangle.comp ((rememberProgram (prodCode ce pairCode)).comp (augmentProgram ce))).congrFun
    (by intro q; rfl)

noncomputable opaque program (ce : E → List Bool) (f : Evaluator E)
    (p : Procedure (prodCode (prodCode (prodCode (prodCode ce pairCode) pairCode) ratCode) ratCode)
      ratCode (fun x => inner f x.1.1 x.1.2 x.2)) :
    Procedure (RationalRectangleProgram.inputCode ce) ratCode (value f) :=
  ((RationalRectangleProgram.program (RationalRectangleProgram.inputCode ce) (outer f)
    (outerProgram ce f p)).comp (rememberProgram ce)).congrFun (by intro q; rfl)

end ContinuumCoulomb.RationalSixQuadrature

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_RationalClamp
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal rational clamp preserves approximation error to values in
[0,1]. It keeps numerical density samples nonnegative and bounded. -/

namespace ContinuumCoulomb
open ExactQuantumFactoring.BitStackProgram

noncomputable opaque rationalUnitClampProgram : Procedure ratCode ratCode rationalUnitClamp := by
  let q := Procedure.identity ratCode
  let zero := Procedure.constant ratCode ratCode (0 : ℚ)
  let one := Procedure.constant ratCode ratCode (1 : ℚ)
  let below := BisectionProgram.rationalLess.comp (q.pair zero)
  let above := BisectionProgram.rationalLess.comp (one.pair q)
  exact (Procedure.conditional below zero (Procedure.conditional above one q)).congrFun (by
    intro q
    simp only [Function.comp_apply, id_eq, decide_eq_true_eq]
    split_ifs with h0 h1
    · simp [rationalUnitClamp, min_eq_right (by linarith : q ≤ 1), max_eq_left h0.le]
    · simp [rationalUnitClamp, min_eq_left h1.le]
    · simp [rationalUnitClamp, min_eq_right (le_of_not_gt h1), max_eq_right (le_of_not_gt h0)])

end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_GaussianFrequencyProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal arithmetic for the fixed-density Gaussian frequency evaluator. -/

namespace ContinuumCoulomb.GaussianFrequency
open ExactQuantumFactoring.BitStackProgram

noncomputable opaque countProgram (rho : ℕ) : Procedure unaryCode unaryCode (count rho) := by
  let sq := ResolventSchedule.squareProgram.comp Procedure.unarySuccessor
  let c := Procedure.constant unaryCode unaryCode (512 * (rho + 1))
  exact (ResolventSchedule.mulProgram.comp (c.pair sq)).congrFun (by intro P; rfl)

noncomputable opaque precisionProgram : Procedure unaryCode unaryCode precision :=
  (ResolventSchedule.mulProgram.comp
    ((Procedure.constant unaryCode unaryCode 8).pair Procedure.unarySuccessor)).congrFun
      (by intro P; rfl)

noncomputable opaque radicandProgram (rho : ℕ) : Procedure unaryCode ratCode (radicand rho) := by
  let p := PiProgram.program.comp (countProgram rho)
  let c := Procedure.constant unaryCode ratCode (4 * (rho : ℚ))
  exact (Procedure.ratMul.comp (c.pair p)).congrFun (by intro P; rfl)

noncomputable opaque program (rho : ℕ) : Procedure unaryCode ratCode (approximate rho) :=
  (RationalSquareRoot.program.comp (precisionProgram.pair (radicandProgram rho))).congrFun
    (by intro P; rfl)

end ContinuumCoulomb.GaussianFrequency

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_GaussianPacketProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed-frequency Gaussian sample has an actual polynomial-time
Turing program. Both its frequency computation and its exponential
computation use explicit polynomial unary precision schedules. -/

namespace ContinuumCoulomb.GaussianPacket
open ExactQuantumFactoring.BitStackProgram

def inputCode : Input → List Bool := prodCode (prodCode unaryCode unaryCode) ratCode

noncomputable opaque radiusProgram : Procedure inputCode unaryCode (fun x => x.1.1) :=
  (Procedure.first unaryCode unaryCode).comp
    (Procedure.first (prodCode unaryCode unaryCode) ratCode)

noncomputable opaque precisionProgram : Procedure inputCode unaryCode (fun x => x.1.2) :=
  (Procedure.second unaryCode unaryCode).comp
    (Procedure.first (prodCode unaryCode unaryCode) ratCode)

noncomputable opaque pointProgram : Procedure inputCode ratCode Prod.snd :=
  Procedure.second (prodCode unaryCode unaryCode) ratCode

noncomputable opaque radiusSquareProgram : Procedure inputCode unaryCode (fun x => (x.1.1 + 1) ^ 2) :=
  ResolventSchedule.squareProgram.comp (Procedure.unarySuccessor.comp radiusProgram)

noncomputable opaque frequencyPrecisionProgram : Procedure inputCode unaryCode
    (fun x => frequencyPrecision x.1.1 x.1.2) := by
  let scaled := ResolventSchedule.mulProgram.comp
    ((Procedure.constant inputCode unaryCode 16).pair radiusSquareProgram)
  exact (ResolventSchedule.mulProgram.comp
    (scaled.pair (Procedure.unarySuccessor.comp precisionProgram))).congrFun
      (by intro x; rfl)

noncomputable opaque frequencyProgram (rho : ℕ) : Procedure inputCode ratCode
    (fun x => GaussianFrequency.approximate rho (frequencyPrecision x.1.1 x.1.2)) :=
  (GaussianFrequency.program rho).comp frequencyPrecisionProgram

noncomputable opaque exponentProgram (rho : ℕ) : Procedure inputCode ratCode (exponent rho) := by
  let neg := Procedure.ratNeg.comp (frequencyProgram rho)
  let square := Procedure.ratMul.comp (pointProgram.pair pointProgram)
  exact (Procedure.ratMul.comp (neg.pair square)).congrFun
    (by intro x; simp only [exponent, Function.comp_apply, pow_two])

noncomputable opaque magnitudeProgram (rho : ℕ) : Procedure inputCode unaryCode
    (fun x => magnitude rho x.1.1) :=
  (ResolventSchedule.mulProgram.comp
    ((Procedure.constant inputCode unaryCode (4 * rho + 4)).pair radiusSquareProgram)).congrFun
      (by intro x; rfl)

noncomputable opaque exponentialPrecisionProgram : Procedure inputCode unaryCode
    (fun x => exponentialPrecision x.1.2) :=
  (ResolventSchedule.mulProgram.comp
    ((Procedure.constant inputCode unaryCode 8).pair
      (Procedure.unarySuccessor.comp precisionProgram))).congrFun (by intro x; rfl)

noncomputable opaque argumentProgram (rho : ℕ) :
    Procedure inputCode RationalExponentialProgram.inputCode (argument rho) :=
  (magnitudeProgram rho).pair (exponentialPrecisionProgram.pair (exponentProgram rho))

noncomputable opaque program (rho : ℕ) : Procedure inputCode ratCode (approximate rho) :=
  (rationalUnitClampProgram.comp
    (RationalExponentialProgram.program.comp (argumentProgram rho))).congrFun (by intro x; rfl)

end ContinuumCoulomb.GaussianPacket

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_RawDensitySampleProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal arithmetic and TM2 compilation of the raw localized density
sampler. The coordinate radius and requested accuracy are encoded unary. -/

namespace ContinuumCoulomb.RawDensitySample
open ExactQuantumFactoring.BitStackProgram

def inputCode : Input → List Bool := prodCode (prodCode unaryCode unaryCode)
  CappedKernelProgram.tripleCode

noncomputable opaque paramsProgram : Procedure inputCode (prodCode unaryCode unaryCode) Prod.fst :=
  Procedure.first (prodCode unaryCode unaryCode) CappedKernelProgram.tripleCode

noncomputable opaque radiusProgram : Procedure inputCode unaryCode (fun x => x.1.1) :=
  (Procedure.first unaryCode unaryCode).comp paramsProgram

noncomputable opaque precisionProgram : Procedure inputCode unaryCode (fun x => x.1.2) :=
  (Procedure.second unaryCode unaryCode).comp paramsProgram

noncomputable opaque coordinatesProgram : Procedure inputCode CappedKernelProgram.tripleCode Prod.snd :=
  Procedure.second (prodCode unaryCode unaryCode) CappedKernelProgram.tripleCode

noncomputable opaque firstCoordinateProgram : Procedure inputCode ratCode (fun x => x.2.1) :=
  (Procedure.first ratCode (prodCode ratCode ratCode)).comp coordinatesProgram

noncomputable opaque remainingCoordinatesProgram :
    Procedure inputCode (prodCode ratCode ratCode) (fun x => x.2.2) :=
  (Procedure.second ratCode (prodCode ratCode ratCode)).comp coordinatesProgram

noncomputable opaque secondCoordinateProgram : Procedure inputCode ratCode (fun x => x.2.2.1) :=
  (Procedure.first ratCode ratCode).comp remainingCoordinatesProgram

noncomputable opaque thirdCoordinateProgram : Procedure inputCode ratCode (fun x => x.2.2.2) :=
  (Procedure.second ratCode ratCode).comp remainingCoordinatesProgram

noncomputable opaque planarArgumentProgram :
    Procedure inputCode ResolventSchedule.inputCode planarArgument := by
  let r := ResolventSchedule.mulProgram.comp
    ((Procedure.constant inputCode unaryCode 2).pair radiusProgram)
  exact (r.pair precisionProgram).pair (firstCoordinateProgram.pair secondCoordinateProgram)

noncomputable opaque verticalArgumentProgram :
    Procedure inputCode GaussianPacket.inputCode verticalArgument :=
  paramsProgram.pair thirdCoordinateProgram

noncomputable opaque program (rho : ℕ) : Procedure inputCode ratCode (value rho) := by
  let p := rationalUnitClampProgram.comp (ResolventSchedule.program.comp planarArgumentProgram)
  let p2 := Procedure.ratMul.comp (p.pair p)
  let z := (GaussianPacket.program rho).comp verticalArgumentProgram
  exact (Procedure.ratMul.comp (p2.pair z)).congrFun (by intro x; simp only [value, pow_two]; rfl)

end ContinuumCoulomb.RawDensitySample

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_RawCoulombSampleProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal polynomial programs for the Coulomb samples and their
six-coordinate summation. -/

namespace ContinuumCoulomb.RawCoulombSample
open ExactQuantumFactoring.BitStackProgram CappedKernelProgram

noncomputable opaque firstCoordinate : Procedure tripleCode ratCode Prod.fst :=
  Procedure.first ratCode (prodCode ratCode ratCode)
noncomputable opaque secondCoordinate : Procedure tripleCode ratCode (fun x => x.2.1) :=
  (Procedure.first ratCode ratCode).comp (Procedure.second ratCode (prodCode ratCode ratCode))
noncomputable opaque thirdCoordinate : Procedure tripleCode ratCode (fun x => x.2.2) :=
  (Procedure.second ratCode ratCode).comp (Procedure.second ratCode (prodCode ratCode ratCode))

noncomputable opaque differenceProgram : Procedure differenceCode tripleCode
    (fun z => difference z.1.1 z.1.2 z.2) := by
  let xy := Procedure.first (prodCode tripleCode tripleCode) tripleCode
  let x := (Procedure.first tripleCode tripleCode).comp xy
  let y := (Procedure.second tripleCode tripleCode).comp xy
  let s := Procedure.second (prodCode tripleCode tripleCode) tripleCode
  let d0 := Procedure.ratSub.comp
    ((Procedure.ratSub.comp ((firstCoordinate.comp x).pair (firstCoordinate.comp y))).pair
      (firstCoordinate.comp s))
  let d1 := Procedure.ratSub.comp
    ((Procedure.ratSub.comp ((secondCoordinate.comp x).pair (secondCoordinate.comp y))).pair
      (secondCoordinate.comp s))
  let d2 := Procedure.ratSub.comp
    ((Procedure.ratSub.comp ((thirdCoordinate.comp x).pair (thirdCoordinate.comp y))).pair
      (thirdCoordinate.comp s))
  exact (d0.pair (d1.pair d2)).congrFun (by intro z; rfl)

noncomputable opaque sampleProgram (rho : ℕ) : Procedure inputCode ratCode (evaluate rho) := by
  let e := Procedure.first settingsCode (prodCode tripleCode tripleCode)
  let xy := Procedure.second settingsCode (prodCode tripleCode tripleCode)
  let x := (Procedure.first tripleCode tripleCode).comp xy
  let y := (Procedure.second tripleCode tripleCode).comp xy
  let rp := (Procedure.first (prodCode unaryCode unaryCode)
    (prodCode (prodCode unaryCode ratCode) tripleCode)).comp e
  let ks := (Procedure.second (prodCode unaryCode unaryCode)
    (prodCode (prodCode unaryCode ratCode) tripleCode)).comp e
  let kp := (Procedure.first (prodCode unaryCode ratCode) tripleCode).comp ks
  let s := (Procedure.second (prodCode unaryCode ratCode) tripleCode).comp ks
  let dx := (RawDensitySample.program rho).comp (rp.pair x)
  let dy := (RawDensitySample.program rho).comp (rp.pair y)
  let diff := differenceProgram.comp (xy.pair s)
  let kernel := CappedKernelProgram.program.comp (kp.pair diff)
  exact (Procedure.ratMul.comp ((Procedure.ratMul.comp (dx.pair dy)).pair kernel)).congrFun
    (by intro z; rfl)

def sixInputCode : SixInput → List Bool :=
  prodCode (prodCode (prodCode (prodCode settingsCode RationalSixQuadrature.pairCode)
    RationalSixQuadrature.pairCode) ratCode) ratCode

def sixInput (z : SixInput) : Input :=
  (z.1.1.1.1, ((z.1.1.1.2.1, z.1.1.1.2.2, z.1.1.2.1), (z.1.1.2.2, z.1.2, z.2)))

noncomputable opaque sixInputProgram : Procedure sixInputCode inputCode sixInput := by
  let top := Procedure.first
    (prodCode (prodCode (prodCode settingsCode RationalSixQuadrature.pairCode)
      RationalSixQuadrature.pairCode) ratCode) ratCode
  let four := (Procedure.first (prodCode (prodCode settingsCode RationalSixQuadrature.pairCode)
    RationalSixQuadrature.pairCode) ratCode).comp top
  let two := (Procedure.first (prodCode settingsCode RationalSixQuadrature.pairCode)
    RationalSixQuadrature.pairCode).comp four
  let e := (Procedure.first settingsCode RationalSixQuadrature.pairCode).comp two
  let ab := (Procedure.second settingsCode RationalSixQuadrature.pairCode).comp two
  let cd := (Procedure.second (prodCode settingsCode RationalSixQuadrature.pairCode)
    RationalSixQuadrature.pairCode).comp four
  let a := (Procedure.first ratCode ratCode).comp ab
  let b := (Procedure.second ratCode ratCode).comp ab
  let c := (Procedure.first ratCode ratCode).comp cd
  let d := (Procedure.second ratCode ratCode).comp cd
  let f := (Procedure.second (prodCode (prodCode settingsCode RationalSixQuadrature.pairCode)
    RationalSixQuadrature.pairCode) ratCode).comp top
  let g := Procedure.second
    (prodCode (prodCode (prodCode settingsCode RationalSixQuadrature.pairCode)
      RationalSixQuadrature.pairCode) ratCode) ratCode
  exact (e.pair ((a.pair (b.pair c)).pair (d.pair (f.pair g)))).congrFun (by intro z; rfl)

noncomputable opaque sixSampleProgram (rho : ℕ) : Procedure sixInputCode ratCode
    (fun z => RationalSixQuadrature.inner (sixEvaluator rho) z.1.1 z.1.2 z.2) :=
  ((sampleProgram rho).comp sixInputProgram).congrFun (by intro z; rfl)

noncomputable opaque quadratureProgram (rho : ℕ) :
    Procedure (RationalRectangleProgram.inputCode settingsCode)
      ratCode (RationalSixQuadrature.value (sixEvaluator rho)) :=
  RationalSixQuadrature.program settingsCode (sixEvaluator rho) (sixSampleProgram rho)

end ContinuumCoulomb.RawCoulombSample

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CoulombTruncationSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit polynomial cap and box schedules. The single natural guard
is fixed by the fixed one-well density; it is not an input or an oracle. -/

noncomputable section
namespace ContinuumCoulomb.CoulombTruncationSchedule

def epsilon (freq : ℝ) (P : ℕ) : ℚ := 1 / ((guard freq : ℚ) * (scale P : ℚ))

end ContinuumCoulomb.CoulombTruncationSchedule

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_NormalizationQuadrature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal quadrature of the actual squared resolvent. Each sample is
computed by the fixed Taylor/heat program, with its proved error. -/

namespace ContinuumCoulomb.NormalizationQuadrature
open ExactQuantumFactoring.BitStackProgram

def settingsCode : Settings → List Bool := prodCode unaryCode unaryCode

noncomputable opaque sampleProgram :
    Procedure (prodCode (prodCode settingsCode ratCode) ratCode) ratCode
      (fun x => sample x.1.1 x.1.2 x.2) := by
  let ax := Procedure.first (prodCode settingsCode ratCode) ratCode
  let e := (Procedure.first settingsCode ratCode).comp ax
  let a := (Procedure.second settingsCode ratCode).comp ax
  let b := Procedure.second (prodCode settingsCode ratCode) ratCode
  let point := a.pair b
  let q := ResolventSchedule.program.comp (e.pair point)
  exact (Procedure.ratMul.comp (q.pair q)).congrFun (by
    intro x
    simp only [sample, pow_two]
    rfl)

noncomputable opaque program :
    Procedure (RationalRectangleProgram.inputCode settingsCode) ratCode value :=
  RationalRectangleProgram.program settingsCode sample sampleProgram

end ContinuumCoulomb.NormalizationQuadrature

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_NormalizationArithmetic
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unary arithmetic for the explicit normalization quadrature schedule. -/

namespace ContinuumCoulomb.NormalizationSchedule
open ExactQuantumFactoring.BitStackProgram

noncomputable opaque constant4096Program : Procedure unaryCode unaryCode (fun _ => 4096) :=
  ResolventSchedule.constant4096Program.comp
    ((Procedure.identity unaryCode).pair (Procedure.identity unaryCode))

noncomputable opaque constant8192Program : Procedure unaryCode unaryCode (fun _ => 8192) :=
  (ResolventSchedule.mulProgram.comp
    ((Procedure.constant unaryCode unaryCode 2).pair constant4096Program)).congrFun
      (by intro P; norm_num)

noncomputable opaque scaleSuccessorProgram (c : ℕ)
    (pc : Procedure unaryCode unaryCode (fun _ => c)) :
    Procedure unaryCode unaryCode (fun P => c * (P + 1)) :=
  ResolventSchedule.mulProgram.comp (pc.pair Procedure.unarySuccessor)

noncomputable opaque radiusProgram : Procedure unaryCode unaryCode radius :=
  (scaleSuccessorProgram 8192 constant8192Program).congrFun
    (by intro P; exact (radius_def P).symm)

noncomputable opaque radiusCubeProgram : Procedure unaryCode unaryCode (fun P => radius P ^ 3) :=
  cubeProgram.comp radiusProgram

noncomputable opaque meshPrefixProgram : Procedure unaryCode unaryCode meshPrefix :=
  (ResolventSchedule.mulProgram.comp (constant4096Program.pair radiusCubeProgram)).congrFun
    (by intro P; rfl)

noncomputable opaque meshFactorsProgram : Procedure unaryCode (prodCode unaryCode unaryCode)
    (fun P => (meshPrefix P, P + 1)) := meshPrefixProgram.pair Procedure.unarySuccessor

noncomputable opaque meshRawProgram : Procedure unaryCode unaryCode
    (fun P => meshPrefix P * (P + 1)) := ResolventSchedule.mulProgram.comp meshFactorsProgram

noncomputable opaque meshProgram : Procedure unaryCode unaryCode mesh :=
  meshRawProgram.congrFun (by intro P; rfl)

noncomputable opaque radiusSquareProgram : Procedure unaryCode unaryCode (fun P => radius P ^ 2) :=
  ResolventSchedule.squareProgram.comp radiusProgram

noncomputable opaque accuracyPrefixProgram : Procedure unaryCode unaryCode accuracyPrefix :=
  (ResolventSchedule.mulProgram.comp
    ((Procedure.constant unaryCode unaryCode 48).pair radiusSquareProgram)).congrFun
      (by intro P; rfl)

noncomputable opaque accuracyFactorsProgram : Procedure unaryCode (prodCode unaryCode unaryCode)
    (fun P => (accuracyPrefix P, P + 1)) := accuracyPrefixProgram.pair Procedure.unarySuccessor

noncomputable opaque accuracyRawProgram : Procedure unaryCode unaryCode
    (fun P => accuracyPrefix P * (P + 1)) := ResolventSchedule.mulProgram.comp accuracyFactorsProgram

noncomputable opaque accuracyProgram : Procedure unaryCode unaryCode accuracy :=
  accuracyRawProgram.congrFun (by intro P; rfl)

noncomputable opaque doubleRadiusProgram : Procedure unaryCode unaryCode (fun P => 2 * radius P) :=
  ResolventSchedule.mulProgram.comp ((Procedure.constant unaryCode unaryCode 2).pair radiusProgram)

end ContinuumCoulomb.NormalizationSchedule

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_NormalizationProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual polynomial TM2 computation of the normalization integral at
inverse-polynomial precision. Every mesh and sample parameter is built
using the proved unary arithmetic procedures. -/

namespace ContinuumCoulomb.NormalizationSchedule
open ExactQuantumFactoring.BitStackProgram

noncomputable opaque radiusRationalProgram : Procedure unaryCode ratCode (fun P => (radius P : ℚ)) :=
  Procedure.natToRat.comp (Procedure.unaryToBits.comp radiusProgram)

noncomputable opaque meshRationalProgram : Procedure unaryCode ratCode (fun P => (mesh P : ℚ)) :=
  Procedure.natToRat.comp (Procedure.unaryToBits.comp meshProgram)

noncomputable opaque doubleRadiusRationalProgram : Procedure unaryCode ratCode
    (fun P => ((2 * radius P : ℕ) : ℚ)) :=
  Procedure.natToRat.comp (Procedure.unaryToBits.comp doubleRadiusProgram)

noncomputable opaque lowerProgram : Procedure unaryCode ratCode (fun P => -(radius P : ℚ)) :=
  Procedure.ratNeg.comp radiusRationalProgram

noncomputable opaque stepProgram : Procedure unaryCode ratCode
    (fun P => (2 * (radius P : ℚ)) / (mesh P : ℚ)) :=
  (Procedure.ratDiv.comp (doubleRadiusRationalProgram.pair meshRationalProgram)).congrFun
    (by intro P; simp only [Function.comp_apply, Nat.cast_mul, Nat.cast_ofNat])

noncomputable opaque inputProgram :
    Procedure unaryCode (RationalRectangleProgram.inputCode NormalizationQuadrature.settingsCode) input :=
  (meshProgram.pair ((doubleRadiusProgram.pair accuracyProgram).pair
    (lowerProgram.pair stepProgram))).congrFun (by intro P; rfl)

noncomputable opaque program : Procedure unaryCode ratCode approximate :=
  (NormalizationQuadrature.program.comp inputProgram).congrFun (by intro P; rfl)

end ContinuumCoulomb.NormalizationSchedule

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_CoulombNormalizationProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A certified rational evaluator for the fixed Coulomb normalization
factor. The natural guard depends only on the fixed one-well model. -/

noncomputable section
namespace ContinuumCoulomb.CoulombNormalization
open ExactQuantumFactoring.BitStackProgram

noncomputable opaque precisionProgram (rho : ℕ) : Procedure unaryCode unaryCode (precision rho) := by
  let c := Procedure.constant unaryCode unaryCode
    (guard (GaussianFrequency.frequency rho) + factorBound (guard (GaussianFrequency.frequency rho)))
  exact (ResolventSchedule.mulProgram.comp (c.pair Procedure.unarySuccessor)).congrFun (by intro P; rfl)

noncomputable opaque piCountProgram (rho : ℕ) : Procedure unaryCode unaryCode
    (fun P => 8 * (precision rho P + 1)) :=
  (ResolventSchedule.mulProgram.comp ((Procedure.constant unaryCode unaryCode 8).pair
    (Procedure.unarySuccessor.comp (precisionProgram rho)))).congrFun (by intro P; rfl)

noncomputable opaque program (rho : ℕ) : Procedure unaryCode ratCode (approximate rho) := by
  let n := precisionProgram rho
  let f := (GaussianFrequency.program rho).comp n
  let a := NormalizationSchedule.program.comp n
  let p := PiProgram.program.comp (piCountProgram rho)
  let a2 := Procedure.ratMul.comp (a.pair a)
  exact (Procedure.ratDiv.comp (f.pair (Procedure.ratMul.comp (a2.pair p)))).congrFun
    (by intro P; simp only [approximate, pow_two]; rfl)

end ContinuumCoulomb.CoulombNormalization

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_CoulombEvaluationProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single polynomial-time TM2 program for the actual localized
Coulomb coefficient at every rational separation and unary precision. -/

namespace ContinuumCoulomb.CoulombEvaluation
open ExactQuantumFactoring.BitStackProgram

noncomputable opaque inputProgram (rho : ℕ) :
    Procedure inputCode (RationalRectangleProgram.inputCode RawCoulombSample.settingsCode)
      (fun x => input rho x.1 x.2) := by
  let p := Procedure.first unaryCode ratCode
  let r := (radiusProgram rho).comp p
  let q := (samplePrecisionProgram rho).comp p
  let b := (kernelPrecisionProgram rho).comp p
  let eps := epsilonProgram rho
  let z := Procedure.constant inputCode ratCode (0 : ℚ)
  let s := (Procedure.second unaryCode ratCode).pair (z.pair z)
  let settings := (r.pair q).pair ((b.pair eps).pair s)
  let nr := meshRationalProgram rho
  let rr := radiusRationalProgram rho
  let low := Procedure.ratNeg.comp rr
  let width := Procedure.ratMul.comp ((Procedure.constant inputCode ratCode (2 : ℚ)).pair rr)
  let step := Procedure.ratDiv.comp (width.pair nr)
  exact (((meshProgram rho).comp p).pair (settings.pair (low.pair step))).congrFun
    (by intro x; rfl)

noncomputable opaque rawProgram (rho : ℕ) : Procedure inputCode ratCode
    (fun x => rawApproximate rho x.1 x.2) :=
  ((RawCoulombSample.quadratureProgram rho).comp (inputProgram rho)).congrFun (by intro x; rfl)

noncomputable opaque program (rho : ℕ) : Procedure inputCode ratCode
    (fun x => approximate rho x.1 x.2) := by
  let p := Procedure.first unaryCode ratCode
  let n := (normalizationPrecisionProgram rho).comp p
  let c := (CoulombNormalization.program rho).comp n
  exact (Procedure.ratMul.comp (c.pair (rawProgram rho))).congrFun (by intro x; rfl)

end ContinuumCoulomb.CoulombEvaluation

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_CoulombPairProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial-time rational evaluation of direct Coulomb matrix entries
from their two rational planar coordinates. -/

namespace ContinuumCoulomb.CoulombPairEvaluation
open ExactQuantumFactoring.BitStackProgram

noncomputable opaque squaredDistanceProgram : Procedure pairCode ratCode
    (fun x => squaredDistance x.1 x.2) := by
  let a := Procedure.first pointCode pointCode
  let b := Procedure.second pointCode pointCode
  let ax := (Procedure.first ratCode ratCode).comp a
  let ay := (Procedure.second ratCode ratCode).comp a
  let bx := (Procedure.first ratCode ratCode).comp b
  let byCoord := (Procedure.second ratCode ratCode).comp b
  let dx := Procedure.ratSub.comp (ax.pair bx)
  let dy := Procedure.ratSub.comp (ay.pair byCoord)
  let xx := Procedure.ratMul.comp (dx.pair dx)
  let yy := Procedure.ratMul.comp (dy.pair dy)
  exact (Procedure.ratAdd.comp (xx.pair yy)).congrFun
    (by intro x; simp only [squaredDistance,pow_two]; rfl)

noncomputable opaque precisionProgram : Procedure unaryCode unaryCode precision :=
  (ResolventSchedule.mulProgram.comp ((Procedure.constant unaryCode unaryCode 2).pair
    Procedure.unarySuccessor)).congrFun (by intro P; rfl)

noncomputable opaque rootPrecisionProgram (rho : ℕ) : Procedure unaryCode unaryCode (rootPrecision rho) :=
  (ResolventSchedule.mulProgram.comp
    ((Procedure.constant unaryCode unaryCode (4*lipschitzGuard rho)).pair
      Procedure.unarySuccessor)).congrFun (by intro P; rfl)

noncomputable opaque distanceProgram (rho : ℕ) : Procedure inputCode ratCode
    (fun x => distance rho x.1 x.2.1 x.2.2) :=
  (RationalSquareRoot.program.comp
    (((rootPrecisionProgram rho).comp (Procedure.first unaryCode pairCode)).pair
      (squaredDistanceProgram.comp (Procedure.second unaryCode pairCode)))).congrFun (by intro x; rfl)

noncomputable opaque program (rho : ℕ) : Procedure inputCode ratCode
    (fun x => approximate rho x.1 x.2.1 x.2.2) :=
  ((CoulombEvaluation.program rho).comp
    ((precisionProgram.comp (Procedure.first unaryCode pairCode)).pair
      (distanceProgram rho))).congrFun (by intro x; rfl)

end ContinuumCoulomb.CoulombPairEvaluation

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactQuotientBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Stability of the actual contact quotient. A fixed natural guard for
the fixed positive normalization integral suffices for all inputs. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def contactNormalizationGuard : ℕ :=
  ⌈2 / (∫ r, planarResolventMode r ^ 2)⌉₊ + 1

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_HoppingQuadrature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal compact contact quadrature, using the already certified
resolvent program at each translated rational point. -/

namespace ContinuumCoulomb.HoppingQuadrature
open ExactQuantumFactoring.BitStackProgram

abbrev Input := RationalRectangleProgram.Input Settings

def settingsCode : Settings → List Bool :=
  prodCode (prodCode unaryCode unaryCode) ratCode

def sample (e : Settings) (a b : ℚ) : ℚ :=
  PlanarForcingProgram.value (a, b) *
    ResolventSchedule.approximate (e.1, (a - e.2, b))

def value (x : Input) : ℚ := RationalRectangleProgram.value sample x

noncomputable opaque sampleProgram :
    Procedure (prodCode (prodCode settingsCode ratCode) ratCode) ratCode
      (fun x => sample x.1.1 x.1.2 x.2) := by
  let ax := Procedure.first (prodCode settingsCode ratCode) ratCode
  let e := (Procedure.first settingsCode ratCode).comp ax
  let a := (Procedure.second settingsCode ratCode).comp ax
  let b := Procedure.second (prodCode settingsCode ratCode) ratCode
  let par := (Procedure.first (prodCode unaryCode unaryCode) ratCode).comp e
  let d := (Procedure.second (prodCode unaryCode unaryCode) ratCode).comp e
  let shift := Procedure.ratSub.comp (a.pair d)
  let phi := ResolventSchedule.program.comp (par.pair (shift.pair b))
  let forcing := PlanarForcingProgram.program.comp (a.pair b)
  exact (Procedure.ratMul.comp (forcing.pair phi)).congrFun (by intro x; rfl)

noncomputable opaque program :
    Procedure (RationalRectangleProgram.inputCode settingsCode) ratCode value :=
  RationalRectangleProgram.program settingsCode sample sampleProgram

end ContinuumCoulomb.HoppingQuadrature

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_HoppingSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit polynomial mesh and inner precision for the actual compact
hopping numerator. The displacement is an input rational, not an oracle. -/

noncomputable section
namespace ContinuumCoulomb.HoppingSchedule

def argument (x : Input) : HoppingQuadrature.Input :=
  (mesh x.1.2, (((x.1.1 + 2, accuracy x.1.2), x.2),
    (-1, 2 / (mesh x.1.2 : ℚ))))

def approximate (x : Input) : ℚ := HoppingQuadrature.value (argument x)

end ContinuumCoulomb.HoppingSchedule

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_HoppingProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal polynomial TM2 program for the contact numerator, with
unary displacement bound and inverse-accuracy parameter. -/

namespace ContinuumCoulomb.HoppingSchedule
open ExactQuantumFactoring.BitStackProgram

def inputCode : Input → List Bool := prodCode (prodCode unaryCode unaryCode) ratCode

noncomputable opaque meshFactorsProgram : Procedure unaryCode (prodCode unaryCode unaryCode)
    (fun P => (4096, P + 1)) :=
  NormalizationSchedule.constant4096Program.pair Procedure.unarySuccessor

noncomputable opaque meshRawProgram : Procedure unaryCode unaryCode
    (fun P => 4096 * (P + 1)) := ResolventSchedule.mulProgram.comp meshFactorsProgram

noncomputable opaque meshProgram : Procedure unaryCode unaryCode mesh :=
  meshRawProgram.congrFun (by intro P; rfl)

noncomputable opaque accuracyProgram : Procedure unaryCode unaryCode accuracy :=
  ResolventSchedule.scaleProgram

noncomputable opaque argumentProgram :
    Procedure inputCode (RationalRectangleProgram.inputCode HoppingQuadrature.settingsCode) argument := by
  let rp := Procedure.first (prodCode unaryCode unaryCode) ratCode
  let r := (Procedure.first unaryCode unaryCode).comp rp
  let p := (Procedure.second unaryCode unaryCode).comp rp
  let d := Procedure.second (prodCode unaryCode unaryCode) ratCode
  let n := meshProgram.comp p
  let a := accuracyProgram.comp p
  let r2 := ResolventSchedule.addProgram.comp (r.pair (Procedure.constant inputCode unaryCode 2))
  let nr := Procedure.natToRat.comp (Procedure.unaryToBits.comp n)
  let step := Procedure.ratDiv.comp ((Procedure.constant inputCode ratCode 2).pair nr)
  let lower := Procedure.constant inputCode ratCode (-1)
  exact (n.pair (((r2.pair a).pair d).pair (lower.pair step))).congrFun (by intro x; rfl)

noncomputable opaque program : Procedure inputCode ratCode approximate :=
  (HoppingQuadrature.program.comp argumentProgram).congrFun (by intro x; rfl)

end ContinuumCoulomb.HoppingSchedule

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_ComputableHopping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual normalized hopping coefficient has a polynomial TM2
approximation. The sole fixed guard is chosen from the already proved
positive normalization integral; it is independent of every input. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb.ComputableHopping
open ExactQuantumFactoring.BitStackProgram

def precision (P : ℕ) : ℕ := 16 * contactNormalizationGuard ^ 2 * (P + 1)

def argument (x : Input) : HoppingSchedule.Input := ((x.1.1, precision x.1.2), x.2)

def approximate (x : Input) : ℚ :=
  HoppingSchedule.approximate (argument x) /
    (2 * NormalizationSchedule.approximate (precision x.1.2))

noncomputable opaque precisionFactorsProgram :
    Procedure unaryCode (prodCode unaryCode unaryCode)
      (fun P => (16 * contactNormalizationGuard ^ 2, P + 1)) :=
  (Procedure.constant unaryCode unaryCode (16 * contactNormalizationGuard ^ 2)).pair
    Procedure.unarySuccessor

noncomputable opaque precisionRawProgram : Procedure unaryCode unaryCode
    (fun P => (16 * contactNormalizationGuard ^ 2) * (P + 1)) :=
  ResolventSchedule.mulProgram.comp precisionFactorsProgram

noncomputable opaque precisionProgram : Procedure unaryCode unaryCode precision :=
  precisionRawProgram.congrFun (by intro P; rfl)

noncomputable opaque argumentProgram :
    Procedure HoppingSchedule.inputCode HoppingSchedule.inputCode argument := by
  let rp := Procedure.first (prodCode unaryCode unaryCode) ratCode
  let r := (Procedure.first unaryCode unaryCode).comp rp
  let p := (Procedure.second unaryCode unaryCode).comp rp
  let d := Procedure.second (prodCode unaryCode unaryCode) ratCode
  exact ((r.pair (precisionProgram.comp p)).pair d).congrFun (by intro x; rfl)

noncomputable opaque program : Procedure HoppingSchedule.inputCode ratCode approximate := by
  let rp := Procedure.first (prodCode unaryCode unaryCode) ratCode
  let p := (Procedure.second unaryCode unaryCode).comp rp
  let n := HoppingSchedule.program.comp argumentProgram
  let a := NormalizationSchedule.program.comp (precisionProgram.comp p)
  let two := Procedure.constant HoppingSchedule.inputCode ratCode (2 : ℚ)
  let den := Procedure.ratMul.comp (two.pair a)
  exact (Procedure.ratDiv.comp (n.pair den)).congrFun (by intro x; rfl)

end ContinuumCoulomb.ComputableHopping

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CountertermEvaluation
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual well-depth counterterms are finite sums of certified Coulomb
entries divided by the fixed onsite hopping. A fixed positive denominator
guard makes every rational evaluation well defined. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb.CountertermEvaluation

theorem guard_exists (rho : ℕ) : ∃ C : ℕ, 1 ≤ C ∧
    2 ≤ (C:ℝ)*planarHopping 0 ∧
    localizedPotentialBound (GaussianFrequency.frequency rho) ≤ C ∧
    planarWellDerivativeConstant ≤ C := by
  let B := 1+2/planarHopping 0+
    localizedPotentialBound (GaussianFrequency.frequency rho)+planarWellDerivativeConstant
  obtain ⟨C,hC⟩ := exists_nat_gt B
  have hT := planarHopping_positive 0
  have hV := localizedPotentialBound_nonnegative (GaussianFrequency.frequency rho)
  have hW := planarWellDerivativeConstant_positive
  have h1 : (1:ℝ) ≤ C := by
    dsimp [B] at hC
    have hp : 0 ≤ 2/planarHopping 0 := by positivity
    linarith
  refine ⟨C,by exact_mod_cast h1,?_,?_,?_⟩
  · apply (div_le_iff₀ hT).mp
    dsimp [B] at hC
    linarith
  · dsimp [B] at hC
    linarith [div_nonneg (by norm_num : (0:ℝ) ≤ 2) hT.le]
  · dsimp [B] at hC
    linarith [div_nonneg (by norm_num : (0:ℝ) ≤ 2) hT.le]

def guard (rho : ℕ) : ℕ := Classical.choose (guard_exists rho)

def denominator (rho p : ℕ) : ℚ :=
  max 1 ((guard rho:ℚ)*ComputableHopping.approximate ((1,p),0))

def entry (rho p : ℕ) (a b : ℚ×ℚ) : ℚ :=
  (guard rho:ℚ)*CoulombPairEvaluation.approximate rho p a b / denominator rho p

def offsite (rho p : ℕ) (a b : ℚ×ℚ) : ℚ :=
  if CoulombPairEvaluation.squaredDistance a b = 0 then 0 else entry rho p a b

def row (rho p : ℕ) (a : ℚ×ℚ) (sites : List (ℚ×ℚ)) : ℚ :=
  (sites.map (offsite rho p a)).sum

end ContinuumCoulomb.CountertermEvaluation

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarWellNumerics
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed guard turns the actual heat-resolvent evaluator into an
evaluator of the compact manufactured planar well. The guard is chosen
once on the unit disk; no instance-dependent real parameter is encoded. -/

noncomputable section
namespace ContinuumCoulomb.PlanarWellNumerics

theorem guard_exists : ∃ C : ℕ, 0 < C ∧
    ∀ r : PlanarPosition, ‖r‖ ≤ 1 → 2 ≤ (C:ℝ)*planarResolventMode r := by
  obtain ⟨r,hr,hmin⟩ := (isCompact_closedBall (0:PlanarPosition) 1).exists_isMinOn
    (Metric.nonempty_closedBall.mpr (by norm_num)) planarResolventMode_C7.continuous.continuousOn
  obtain ⟨C,hC⟩ := exists_nat_gt (2/planarResolventMode r + 1)
  have hp := planarResolventMode_positive r
  have hCp : 0 < C := by
    have hh : (0:ℝ) < C := lt_trans (by positivity) hC
    exact_mod_cast hh
  refine ⟨C,hCp,fun s hs => ?_⟩
  have hs' : s ∈ Metric.closedBall (0:PlanarPosition) 1 := by
    simpa only [Metric.mem_closedBall,dist_zero_right] using hs
  have hbase : 2 ≤ (C:ℝ)*planarResolventMode r := by
    have hc : 2/planarResolventMode r ≤ C := by linarith
    exact (div_le_iff₀ hp).mp hc
  exact hbase.trans (mul_le_mul_of_nonneg_left (hmin hs') (Nat.cast_nonneg C))

def guard : ℕ := Classical.choose guard_exists

def precision (p : ℕ) : ℕ := 4*guard^2*(p+1)

def approximate (p : ℕ) (q : ℚ×ℚ) : ℚ :=
  if outside q then 0 else
    -PlanarForcingProgram.value q /
      (2*ResolventSchedule.approximate ((2,precision p),q))

end ContinuumCoulomb.PlanarWellNumerics

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_RationalSmoothTransition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational approximation of the explicit smooth transition. Exponents
near the flat junction are truncated before Taylor evaluation, keeping
both the magnitude parameter and the error polynomial in the precision. -/

namespace ContinuumCoulomb.RationalSmoothTransition

def flat (p : ℕ) (q : ℚ) : ℚ :=
  if (p+1 : ℚ)⁻¹ < q then
    clip (RationalExponential.approximate (p+1) (p+1) (-q⁻¹))
  else 0

def approximate (p : ℕ) (q : ℚ) : ℚ :=
  flat (precision p) q / (flat (precision p) q + flat (precision p) (1-q))

end ContinuumCoulomb.RationalSmoothTransition

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_SmoothTransitionProgram
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal polynomial-time rational programs for the smooth transition
and the fixed transverse cutoff. All large parameters are unary and each
Taylor exponent has already been bounded in `RationalSmoothTransition`. -/

namespace ContinuumCoulomb.SmoothTransitionProgram
open ExactQuantumFactoring.BitStackProgram

def inputCode : Input → List Bool := prodCode unaryCode ratCode

noncomputable opaque clipProgram : Procedure ratCode ratCode RationalSmoothTransition.clip := by
  let q := Procedure.identity ratCode
  let zero := Procedure.constant ratCode ratCode (0:ℚ)
  let one := Procedure.constant ratCode ratCode (1:ℚ)
  let negative := Procedure.intSign.comp Procedure.ratNum
  let large := Procedure.intSign.comp (Procedure.ratNum.comp
    (Procedure.ratSub.comp (one.pair q)))
  exact (Procedure.conditional negative zero (Procedure.conditional large one q)).congrFun (by
    intro q
    simp only [Function.comp_apply,Rat.num_neg,decide_eq_true_eq,id_eq]
    unfold RationalSmoothTransition.clip
    split_ifs with hneg hlarge
    · rw [min_eq_right (le_of_lt (hneg.trans (by norm_num))), max_eq_left hneg.le]
    · rw [min_eq_left (by linarith : (1:ℚ) ≤ q), max_eq_right (by norm_num)]
    · rw [min_eq_right (by linarith : q ≤ 1), max_eq_right (le_of_not_gt hneg)])

noncomputable opaque flatProgram : Procedure inputCode ratCode
    (fun x => RationalSmoothTransition.flat x.1 x.2) := by
  let p := Procedure.first unaryCode ratCode
  let q := Procedure.second unaryCode ratCode
  let next := Procedure.unarySuccessor.comp p
  let nextQ := Procedure.natToRat.comp (Procedure.unaryToBits.comp next)
  let cutoff := Procedure.ratInv.comp nextQ
  let positive := Procedure.intSign.comp (Procedure.ratNum.comp
    (Procedure.ratSub.comp (cutoff.pair q)))
  let exponent := Procedure.ratNeg.comp (Procedure.ratInv.comp q)
  let sample := clipProgram.comp (RationalExponentialProgram.program.comp
    (next.pair (next.pair exponent)))
  let zero := Procedure.constant inputCode ratCode (0:ℚ)
  exact (Procedure.conditional positive sample zero).congrFun (by
    intro x
    simp only [Function.comp_apply,Rat.num_neg,decide_eq_true_eq,id_eq,
      Nat.succ_eq_add_one,Nat.cast_add,Nat.cast_one]
    unfold RationalSmoothTransition.flat
    congr 1
    simp only [sub_neg])

noncomputable opaque precisionProgram : Procedure unaryCode unaryCode RationalSmoothTransition.precision :=
  (Procedure.unaryMul.comp ((Procedure.constant unaryCode unaryCode 1000).pair
    Procedure.unarySuccessor)).congrFun (by intro p; rfl)

noncomputable opaque program : Procedure inputCode ratCode
    (fun x => RationalSmoothTransition.approximate x.1 x.2) := by
  let p := precisionProgram.comp (Procedure.first unaryCode ratCode)
  let q := Procedure.second unaryCode ratCode
  let one := Procedure.constant inputCode ratCode (1:ℚ)
  let complement := Procedure.ratSub.comp (one.pair q)
  let left := flatProgram.comp (p.pair q)
  let right := flatProgram.comp (p.pair complement)
  exact (Procedure.ratDiv.comp (left.pair (Procedure.ratAdd.comp (left.pair right)))).congrFun
    (by intro x; rfl)

def cutoff (p : ℕ) (q : ℚ) : ℚ :=
  RationalSmoothTransition.approximate p (cutoffArgument q)

noncomputable opaque cutoffArgumentProgram : Procedure ratCode ratCode cutoffArgument := by
  let q := Procedure.identity ratCode
  let four := Procedure.constant ratCode ratCode (4:ℚ)
  let three := Procedure.constant ratCode ratCode (3:ℚ)
  let square := Procedure.ratMul.comp (q.pair q)
  exact (Procedure.ratDiv.comp ((Procedure.ratSub.comp (four.pair square)).pair three)).congrFun
    (by intro q; simp only [cutoffArgument,pow_two]; rfl)

noncomputable opaque cutoffProgram : Procedure inputCode ratCode (fun x => cutoff x.1 x.2) :=
  (program.comp ((Procedure.first unaryCode ratCode).pair
    (cutoffArgumentProgram.comp (Procedure.second unaryCode ratCode)))).congrFun (by intro x; rfl)

end ContinuumCoulomb.SmoothTransitionProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_VerticalCutoffProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial-time approximation of the actual transverse cutoff in the
manufactured well field. The rational slab width and coordinate are arbitrary. -/

namespace ContinuumCoulomb.VerticalCutoffProgram
open ExactQuantumFactoring.BitStackProgram

def inputCode : Input → List Bool := prodCode unaryCode (prodCode ratCode ratCode)
def value (x : Input) : ℚ := SmoothTransitionProgram.cutoff x.1 (argument x)

noncomputable opaque argumentProgram : Procedure inputCode ratCode argument := by
  let rest := Procedure.second unaryCode (prodCode ratCode ratCode)
  let S := (Procedure.first ratCode ratCode).comp rest
  let z := (Procedure.second ratCode ratCode).comp rest
  let two := Procedure.constant inputCode ratCode (2:ℚ)
  exact (Procedure.ratMul.comp ((Procedure.ratDiv.comp (two.pair S)).pair z)).congrFun
    (by intro x; rfl)

noncomputable opaque program : Procedure inputCode ratCode value :=
  (SmoothTransitionProgram.cutoffProgram.comp
    ((Procedure.first unaryCode (prodCode ratCode ratCode)).pair argumentProgram)).congrFun
    (by intro x; rfl)

end ContinuumCoulomb.VerticalCutoffProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ManufacturedFieldEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A rational scalar evaluator for the actual manufactured well field.
The well-depth factors are clipped to their proved interval [1,2]. This
stabilizes every encoded input and preserves the valid-instance estimate. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb.ManufacturedFieldEvaluation

def coefficient (rho p : ℕ) (scale : ℚ) (sites : List (ℚ×ℚ)) (a : ℚ×ℚ) : ℚ :=
  1+RationalSmoothTransition.clip (CountertermEvaluation.row rho p a sites/scale)

def planar (rho p : ℕ) (scale : ℚ) (sites : List (ℚ×ℚ)) (r : ℚ×ℚ) : ℚ :=
  (sites.map (fun a => coefficient rho p scale sites a *
    PlanarWellNumerics.approximate p (translate r a))).sum

def rawValue (rho p : ℕ) (scale S : ℚ) (sites : List (ℚ×ℚ))
    (x : CappedKernelProgram.Triple) : ℚ :=
  RationalSmoothTransition.clip (VerticalCutoffProgram.value (p,(S,x.2.2))) *
    planar rho p scale sites (x.1,x.2.1)

def precision (rho m P : ℕ) : ℕ := 16*(CountertermEvaluation.guard rho)^4*(m+1)^2*(P+1)

def value (rho P : ℕ) (scale S : ℚ) (sites : List (ℚ×ℚ))
    (x : CappedKernelProgram.Triple) : ℚ := rawValue rho (precision rho sites.length P) scale S sites x

end ContinuumCoulomb.ManufacturedFieldEvaluation

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ManufacturedVelocityEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual manufactured Moser velocity is sampled using rational
coordinate differences, the certified scalar field evaluator and π.
No value or derivative evaluator is assumed. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb.ManufacturedVelocityEvaluation
open CappedKernelProgram (Triple position)
open NeutralAtom (dirPartial axis)

def precision (rho P : ℕ) : ℕ :=
  12*(1+MoserDifferenceBudget.guard*(4*rho+1))*(P+1)

def sample (rho p : ℕ) (scale S : ℚ) (sites : List (ℚ×ℚ)) (q : Triple) : ℚ :=
  ManufacturedFieldEvaluation.value rho (MoserDifferenceBudget.precision p) scale S sites q

def gradient (rho p : ℕ) (scale S : ℚ) (sites : List (ℚ×ℚ)) (q : Triple) (a : Fin 3) : ℚ :=
  RationalFieldDifferences.first (sample rho p scale S sites) (MoserDifferenceBudget.step p) q a

def laplacian (rho p : ℕ) (scale S : ℚ) (sites : List (ℚ×ℚ)) (q : Triple) : ℚ :=
  RationalFieldDifferences.laplacian (sample rho p scale S sites) (MoserDifferenceBudget.step p) q

def pi (p : ℕ) : ℚ := PiProgram.approximate (8*(p+1))

def component (rho P : ℕ) (scale S : ℚ) (sites : List (ℚ×ℚ))
    (t : ℚ) (q : Triple) (a : Fin 3) : ℚ :=
  let p := precision rho P;
  -(gradient rho p scale S sites q a) /
    max (rho:ℚ) (4*pi p*(rho:ℚ)+t*laplacian rho p scale S sites q)

def value (rho P : ℕ) (scale S : ℚ) (sites : List (ℚ×ℚ)) (t : ℚ) (q : Triple) : Triple :=
  (component rho P scale S sites t q 0,
    (component rho P scale S sites t q 1,component rho P scale S sites t q 2))

end ContinuumCoulomb.ManufacturedVelocityEvaluation

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ManufacturedEuler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal clipped Euler iteration approximates the actual manufactured
Moser flow. Its step count and denominator are fixed polynomials in the
requested unary precision, uniformly over all valid input geometries. -/

noncomputable section
namespace ContinuumCoulomb.ManufacturedEuler
open CappedKernelProgram (Triple position)
open EulerRegisters

def evaluate (rho : ℕ) (e : Environment) (t : ℚ) (q : Triple) : Triple :=
  ManufacturedVelocityEvaluation.value rho e.1 e.2.1.1 e.2.1.2 e.2.2 t q

def approximate (rho U C P : ℕ) (scale S : ℚ) (sites : List (ℚ×ℚ)) (q : Triple) : Triple :=
  let N := steps C P
  let D := denominator C P
  let B := boxNumerator U D q
  trajectory (evaluate rho) (N,((scale,S),sites)) N D B (round D B q) N

end ContinuumCoulomb.ManufacturedEuler

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_EulerProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The bounded-register Euler loop is an actual polynomial-time TM2
program whenever its field sampler is one. The size invariant was proved
for arbitrary sampler outputs, so this certificate holds on all inputs. -/

namespace ContinuumCoulomb.EulerRegisters
open ExactQuantumFactoring.BitStackProgram
open CappedKernelProgram (Triple tripleCode)

variable {E : Type} {ce : E → List Bool}

noncomputable opaque parametersProgram : Procedure (configCode ce) (parametersCode ce) Prod.fst :=
  Procedure.first (parametersCode ce) (prodCode Nat.bits registersCode)
noncomputable opaque environmentProgram : Procedure (configCode ce) ce (fun c : Config E => c.1.1) :=
  (Procedure.first ce (prodCode Nat.bits (prodCode Nat.bits ratCode))).comp parametersProgram
noncomputable opaque parameterTailProgram : Procedure (configCode ce)
    (prodCode Nat.bits (prodCode Nat.bits ratCode)) (fun c : Config E => c.1.2) :=
  (Procedure.second ce _).comp parametersProgram
noncomputable opaque denominatorProgram : Procedure (configCode ce) Nat.bits (fun c : Config E => c.1.2.1) :=
  (Procedure.first Nat.bits _).comp parameterTailProgram
noncomputable opaque boxStepProgram : Procedure (configCode ce) (prodCode Nat.bits ratCode)
    (fun c : Config E => c.1.2.2) := (Procedure.second Nat.bits _).comp parameterTailProgram
noncomputable opaque boxProgram : Procedure (configCode ce) Nat.bits (fun c : Config E => c.1.2.2.1) :=
  (Procedure.first Nat.bits ratCode).comp boxStepProgram
noncomputable opaque stepProgram : Procedure (configCode ce) ratCode (fun c : Config E => c.1.2.2.2) :=
  (Procedure.second Nat.bits ratCode).comp boxStepProgram
noncomputable opaque stateProgram : Procedure (configCode ce) (prodCode Nat.bits registersCode) Prod.snd :=
  Procedure.second (parametersCode ce) (prodCode Nat.bits registersCode)
noncomputable opaque counterProgram : Procedure (configCode ce) Nat.bits (fun c : Config E => c.2.1) :=
  (Procedure.first Nat.bits registersCode).comp stateProgram
noncomputable opaque registersProgram : Procedure (configCode ce) registersCode (fun c : Config E => c.2.2) :=
  (Procedure.second Nat.bits registersCode).comp stateProgram

noncomputable opaque currentPointProgram : Procedure (configCode ce) tripleCode
    (fun c : Config E => point c.1.2.1 c.2.2) :=
  pointProgram.comp (denominatorProgram.pair registersProgram)

noncomputable opaque timeProgram : Procedure (configCode ce) ratCode
    (fun c : Config E => (c.2.1:ℚ)*c.1.2.2.2) :=
  Procedure.ratMul.comp ((Procedure.natToRat.comp counterProgram).pair stepProgram)

noncomputable opaque sampleArgumentsProgram :
    Procedure (configCode ce) (prodCode ce (prodCode ratCode tripleCode))
      (fun c : Config E => (c.1.1,((c.2.1:ℚ)*c.1.2.2.2,point c.1.2.1 c.2.2))) :=
  environmentProgram.pair (timeProgram.pair currentPointProgram)

variable {evaluate : E → ℚ → Triple → Triple}

noncomputable opaque velocityProgram
    (sampleProgram : Procedure (prodCode ce (prodCode ratCode tripleCode)) tripleCode
      (fun x => evaluate x.1 x.2.1 x.2.2)) :
    Procedure (configCode ce) tripleCode (fun c : Config E =>
      evaluate c.1.1 ((c.2.1:ℚ)*c.1.2.2.2) (point c.1.2.1 c.2.2)) :=
  sampleProgram.comp sampleArgumentsProgram

noncomputable opaque proposalArgumentsProgram
    (sampleProgram : Procedure (prodCode ce (prodCode ratCode tripleCode)) tripleCode
      (fun x => evaluate x.1 x.2.1 x.2.2)) :
    Procedure (configCode ce) proposalCode (fun c : Config E =>
      (c.1.2.2.2,(point c.1.2.1 c.2.2,evaluate c.1.1 ((c.2.1:ℚ)*c.1.2.2.2) (point c.1.2.1 c.2.2)))) :=
  stepProgram.pair (currentPointProgram.pair (velocityProgram sampleProgram))

noncomputable opaque nextPointProgram
    (sampleProgram : Procedure (prodCode ce (prodCode ratCode tripleCode)) tripleCode
      (fun x => evaluate x.1 x.2.1 x.2.2)) :
    Procedure (configCode ce) tripleCode (fun c : Config E =>
      proposal c.1.2.2.2 (point c.1.2.1 c.2.2)
        (evaluate c.1.1 ((c.2.1:ℚ)*c.1.2.2.2) (point c.1.2.1 c.2.2))) :=
  proposalProgram.comp (proposalArgumentsProgram sampleProgram)

noncomputable opaque nextRegistersProgram
    (sampleProgram : Procedure (prodCode ce (prodCode ratCode tripleCode)) tripleCode
      (fun x => evaluate x.1 x.2.1 x.2.2)) :
    Procedure (configCode ce) registersCode (fun c : Config E =>
      round c.1.2.1 c.1.2.2.1 (proposal c.1.2.2.2 (point c.1.2.1 c.2.2)
        (evaluate c.1.1 ((c.2.1:ℚ)*c.1.2.2.2) (point c.1.2.1 c.2.2)))) :=
  roundProgram.comp ((denominatorProgram.pair boxProgram).pair (nextPointProgram sampleProgram))

noncomputable opaque advanceProgram
    (sampleProgram : Procedure (prodCode ce (prodCode ratCode tripleCode)) tripleCode
      (fun x => evaluate x.1 x.2.1 x.2.2)) :
    Procedure (configCode ce) (configCode ce) (advance evaluate) :=
  parametersProgram.pair ((Procedure.successor.comp counterProgram).pair
    (nextRegistersProgram sampleProgram))

noncomputable opaque repeatProgram
    (sampleProgram : Procedure (prodCode ce (prodCode ratCode tripleCode)) tripleCode
      (fun x => evaluate x.1 x.2.1 x.2.2)) :
    Procedure (prodCode unaryCode (configCode ce)) (configCode ce)
      (fun x => (advance evaluate)^[x.1] x.2) :=
  (advanceProgram sampleProgram).iterate (32*(Polynomial.X+1)^2)
    (iterate_code_bound ce evaluate)

def run (evaluate : E → ℚ → Triple → Triple) (x : ℕ×Config E) : Triple :=
  let c := (advance evaluate)^[x.1] x.2
  point c.1.2.1 c.2.2

noncomputable opaque program
    (sampleProgram : Procedure (prodCode ce (prodCode ratCode tripleCode)) tripleCode
      (fun x => evaluate x.1 x.2.1 x.2.2)) :
    Procedure (prodCode unaryCode (configCode ce)) tripleCode (run evaluate) :=
  currentPointProgram.comp (repeatProgram sampleProgram)

end ContinuumCoulomb.EulerRegisters

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_FiniteDifferenceProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal rational programs for the three fixed coordinate differences.
Their scalar sampler is supplied as a concrete Procedure, and is evaluated
only a fixed number of times per gradient or Laplacian sample. -/

namespace ContinuumCoulomb.FiniteDifferenceProgram
open ExactQuantumFactoring.BitStackProgram
open CappedKernelProgram (Triple tripleCode)
open RationalFieldDifferences

noncomputable opaque shiftProgram (a : Fin 3) : Procedure (prodCode tripleCode ratCode) tripleCode
    (fun x => shift x.1 x.2 a) := by
  let q := Procedure.first tripleCode ratCode
  let h := Procedure.second tripleCode ratCode
  let zero := Procedure.constant (prodCode tripleCode ratCode) ratCode (0:ℚ)
  let x := (Procedure.first ratCode (prodCode ratCode ratCode)).comp q
  let yz := (Procedure.second ratCode (prodCode ratCode ratCode)).comp q
  let y := (Procedure.first ratCode ratCode).comp yz
  let z := (Procedure.second ratCode ratCode).comp yz
  let dx : Procedure (prodCode tripleCode ratCode) ratCode (fun z => if a=0 then z.2 else 0) := by
    by_cases ha : a=0
    · exact h.congrFun (by intro z; simp only [ha,ite_true, if_true])
    · exact zero.congrFun (by intro z; simp only [ha,ite_false, if_false])
  let dy : Procedure (prodCode tripleCode ratCode) ratCode (fun z => if a=1 then z.2 else 0) := by
    by_cases ha : a=1
    · exact h.congrFun (by intro z; simp only [ha,ite_true, if_true])
    · exact zero.congrFun (by intro z; simp only [ha,ite_false, if_false])
  let dz : Procedure (prodCode tripleCode ratCode) ratCode (fun z => if a=2 then z.2 else 0) := by
    by_cases ha : a=2
    · exact h.congrFun (by intro z; simp only [ha,ite_true, if_true])
    · exact zero.congrFun (by intro z; simp only [ha,ite_false, if_false])
  let xx := Procedure.ratAdd.comp (x.pair dx)
  let yy := Procedure.ratAdd.comp (y.pair dy)
  let zz := Procedure.ratAdd.comp (z.pair dz)
  exact (xx.pair (yy.pair zz)).congrFun (by intro x; rfl)

variable {E : Type} {ce : E → List Bool} {sample : E → Triple → ℚ} {step : E → ℚ}

noncomputable opaque plusArgumentProgram (a : Fin 3)
    (stepProgram : Procedure ce ratCode step) :
    Procedure (prodCode ce tripleCode) tripleCode (fun x => shift x.2 (step x.1) a) :=
  (shiftProgram a).comp ((Procedure.second ce tripleCode).pair
    (stepProgram.comp (Procedure.first ce tripleCode)))

noncomputable opaque minusArgumentProgram (a : Fin 3)
    (stepProgram : Procedure ce ratCode step) :
    Procedure (prodCode ce tripleCode) tripleCode (fun x => shift x.2 (-step x.1) a) :=
  (shiftProgram a).comp ((Procedure.second ce tripleCode).pair
    (Procedure.ratNeg.comp (stepProgram.comp (Procedure.first ce tripleCode))))

noncomputable opaque plusSampleProgram (a : Fin 3)
    (sampleProgram : Procedure (prodCode ce tripleCode) ratCode (fun x => sample x.1 x.2))
    (stepProgram : Procedure ce ratCode step) :
    Procedure (prodCode ce tripleCode) ratCode (fun x => sample x.1 (shift x.2 (step x.1) a)) :=
  sampleProgram.comp ((Procedure.first ce tripleCode).pair (plusArgumentProgram a stepProgram))

noncomputable opaque minusSampleProgram (a : Fin 3)
    (sampleProgram : Procedure (prodCode ce tripleCode) ratCode (fun x => sample x.1 x.2))
    (stepProgram : Procedure ce ratCode step) :
    Procedure (prodCode ce tripleCode) ratCode (fun x => sample x.1 (shift x.2 (-step x.1) a)) :=
  sampleProgram.comp ((Procedure.first ce tripleCode).pair (minusArgumentProgram a stepProgram))

noncomputable opaque firstProgram (a : Fin 3)
    (sampleProgram : Procedure (prodCode ce tripleCode) ratCode (fun x => sample x.1 x.2))
    (stepProgram : Procedure ce ratCode step) :
    Procedure (prodCode ce tripleCode) ratCode
      (fun x => first (sample x.1) (step x.1) x.2 a) := by
  let diff := Procedure.ratSub.comp ((plusSampleProgram a sampleProgram stepProgram).pair sampleProgram)
  exact Procedure.ratDiv.comp (diff.pair (stepProgram.comp (Procedure.first ce tripleCode)))

noncomputable opaque secondNumeratorProgram (a : Fin 3)
    (sampleProgram : Procedure (prodCode ce tripleCode) ratCode (fun x => sample x.1 x.2))
    (stepProgram : Procedure ce ratCode step) :
    Procedure (prodCode ce tripleCode) ratCode (fun x =>
      sample x.1 (shift x.2 (step x.1) a)+sample x.1 (shift x.2 (-step x.1) a)-2*sample x.1 x.2) := by
  let ends := Procedure.ratAdd.comp ((plusSampleProgram a sampleProgram stepProgram).pair
    (minusSampleProgram a sampleProgram stepProgram))
  let center := Procedure.ratMul.comp
    ((Procedure.constant (prodCode ce tripleCode) ratCode (2:ℚ)).pair sampleProgram)
  exact Procedure.ratSub.comp (ends.pair center)

noncomputable opaque stepSquareProgram (stepProgram : Procedure ce ratCode step) :
    Procedure (prodCode ce tripleCode) ratCode (fun x => step x.1^2) := by
  let h := stepProgram.comp (Procedure.first ce tripleCode)
  exact (Procedure.ratMul.comp (h.pair h)).congrFun (by intro x; simp only [pow_two]; rfl)

noncomputable opaque secondProgram (a : Fin 3)
    (sampleProgram : Procedure (prodCode ce tripleCode) ratCode (fun x => sample x.1 x.2))
    (stepProgram : Procedure ce ratCode step) :
    Procedure (prodCode ce tripleCode) ratCode
      (fun x => second (sample x.1) (step x.1) x.2 a) :=
  Procedure.ratDiv.comp ((secondNumeratorProgram a sampleProgram stepProgram).pair
    (stepSquareProgram stepProgram))

noncomputable opaque laplacianProgram
    (sampleProgram : Procedure (prodCode ce tripleCode) ratCode (fun x => sample x.1 x.2))
    (stepProgram : Procedure ce ratCode step) :
    Procedure (prodCode ce tripleCode) ratCode
      (fun x => laplacian (sample x.1) (step x.1) x.2) := by
  let p0 := secondProgram (0:Fin 3) sampleProgram stepProgram
  let p1 := secondProgram (1:Fin 3) sampleProgram stepProgram
  let p2 := secondProgram (2:Fin 3) sampleProgram stepProgram
  exact (Procedure.ratAdd.comp (p0.pair (Procedure.ratAdd.comp (p1.pair p2)))).congrFun (by
    intro x
    simp only [RationalFieldDifferences.laplacian,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    rfl)

end ContinuumCoulomb.FiniteDifferenceProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_CountertermProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal polynomial programs evaluate the exact counterterm formula
with the error certified in CountertermEvaluation. -/

namespace ContinuumCoulomb.CountertermEvaluation
open ExactQuantumFactoring.BitStackProgram

def rowCode : RowInput → List Bool := prodCode unaryCode
  (prodCode CoulombPairEvaluation.pointCode (listCode CoulombPairEvaluation.pointCode))

noncomputable opaque maxOneProgram : Procedure ratCode ratCode (fun q => max 1 q) := by
  let one := Procedure.constant ratCode ratCode (1:ℚ)
  let q := Procedure.identity ratCode
  let test := Procedure.intSign.comp (Procedure.ratNum.comp (Procedure.ratSub.comp (q.pair one)))
  exact (Procedure.conditional test one q).congrFun (by
    intro q
    simp only [Function.comp_apply,Rat.num_neg,decide_eq_true_eq,id_eq]
    by_cases h : q < 1
    · rw [ite_eq_left (by linarith),max_eq_left h.le]
    · rw [ite_eq_right (by linarith),max_eq_right (le_of_not_gt h)])

noncomputable opaque onsiteArgumentProgram : Procedure unaryCode HoppingSchedule.inputCode
    (fun p => ((1,p),0)) := by
  let p := Procedure.identity unaryCode
  let r := Procedure.constant unaryCode unaryCode 1
  let z := Procedure.constant unaryCode ratCode (0:ℚ)
  exact (r.pair p).pair z

noncomputable opaque onsiteProgram : Procedure unaryCode ratCode
    (fun p => ComputableHopping.approximate ((1,p),0)) :=
  ComputableHopping.program.comp onsiteArgumentProgram

noncomputable opaque guardProgram (rho : ℕ) : Procedure unaryCode ratCode
    (fun _ => (guard rho:ℚ)) := Procedure.constant unaryCode ratCode (guard rho:ℚ)

noncomputable opaque scaledOnsiteProgram (rho : ℕ) : Procedure unaryCode ratCode
    (fun p => (guard rho:ℚ)*ComputableHopping.approximate ((1,p),0)) :=
  Procedure.ratMul.comp ((guardProgram rho).pair onsiteProgram)

noncomputable opaque denominatorProgram (rho : ℕ) : Procedure unaryCode ratCode (denominator rho) :=
  maxOneProgram.comp (scaledOnsiteProgram rho)

noncomputable opaque entryNumeratorProgram (rho : ℕ) : Procedure CoulombPairEvaluation.inputCode ratCode
    (fun x => (guard rho:ℚ)*CoulombPairEvaluation.approximate rho x.1 x.2.1 x.2.2) := by
  let C := Procedure.constant CoulombPairEvaluation.inputCode ratCode (guard rho:ℚ)
  exact Procedure.ratMul.comp (C.pair (CoulombPairEvaluation.program rho))

noncomputable opaque entryDenominatorProgram (rho : ℕ) : Procedure CoulombPairEvaluation.inputCode ratCode
    (fun x => denominator rho x.1) :=
  (denominatorProgram rho).comp (Procedure.first unaryCode CoulombPairEvaluation.pairCode)

noncomputable opaque entryArgumentsProgram (rho : ℕ) :
    Procedure CoulombPairEvaluation.inputCode (prodCode ratCode ratCode)
      (fun x => ((guard rho:ℚ)*CoulombPairEvaluation.approximate rho x.1 x.2.1 x.2.2,
        denominator rho x.1)) :=
  (entryNumeratorProgram rho).pair (entryDenominatorProgram rho)

noncomputable opaque entryProgram (rho : ℕ) : Procedure CoulombPairEvaluation.inputCode ratCode
    (fun x => entry rho x.1 x.2.1 x.2.2) :=
  Procedure.ratDiv.comp (entryArgumentsProgram rho)

noncomputable opaque offsiteProgram (rho : ℕ) : Procedure CoulombPairEvaluation.inputCode ratCode
    (fun x => offsite rho x.1 x.2.1 x.2.2) := by
  let pairs := Procedure.second unaryCode CoulombPairEvaluation.pairCode
  let dist := CoulombPairEvaluation.squaredDistanceProgram.comp pairs
  let test := Procedure.binaryZero.comp (Procedure.intAbs.comp (Procedure.ratNum.comp dist))
  let zero := Procedure.constant CoulombPairEvaluation.inputCode ratCode (0:ℚ)
  exact (Procedure.conditional test zero (entryProgram rho)).congrFun (by
    intro x
    simp only [Function.comp_apply,decide_eq_true_eq,Int.natAbs_eq_zero,Rat.num_eq_zero,offsite])

noncomputable opaque offsiteEnvironmentProgram (rho : ℕ) :
    Procedure (prodCode (prodCode unaryCode CoulombPairEvaluation.pointCode)
      CoulombPairEvaluation.pointCode) ratCode (fun x => offsite rho x.1.1 x.1.2 x.2) := by
  let env := Procedure.first (prodCode unaryCode CoulombPairEvaluation.pointCode)
    CoulombPairEvaluation.pointCode
  let p := (Procedure.first unaryCode CoulombPairEvaluation.pointCode).comp env
  let a := (Procedure.second unaryCode CoulombPairEvaluation.pointCode).comp env
  let b := Procedure.second (prodCode unaryCode CoulombPairEvaluation.pointCode)
    CoulombPairEvaluation.pointCode
  exact (offsiteProgram rho).comp (p.pair (a.pair b))

noncomputable opaque rowProgram (rho : ℕ) : Procedure rowCode ratCode
    (fun x => row rho x.1 x.2.1 x.2.2) := by
  let p := Procedure.first unaryCode
    (prodCode CoulombPairEvaluation.pointCode (listCode CoulombPairEvaluation.pointCode))
  let tail := Procedure.second unaryCode
    (prodCode CoulombPairEvaluation.pointCode (listCode CoulombPairEvaluation.pointCode))
  let a := (Procedure.first CoulombPairEvaluation.pointCode
    (listCode CoulombPairEvaluation.pointCode)).comp tail
  let sites := (Procedure.second CoulombPairEvaluation.pointCode
    (listCode CoulombPairEvaluation.pointCode)).comp tail
  let mapped := (Procedure.listMapWith (ea := prodCode unaryCode CoulombPairEvaluation.pointCode)
    (eb := CoulombPairEvaluation.pointCode) (ec := ratCode)
    (f := fun env b => offsite rho env.1 env.2 b) (0,0) 0
    (offsiteEnvironmentProgram rho)).comp ((p.pair a).pair sites)
  exact (RationalSumProgram.sumProgram.comp mapped).congrFun (by intro x; rfl)

end ContinuumCoulomb.CountertermEvaluation

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_PlanarWellProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed well profile has an actual rational polynomial-time
evaluator. The positive denominator guard is independent of all inputs. -/

namespace ContinuumCoulomb.PlanarWellNumerics
open ExactQuantumFactoring.BitStackProgram

def inputCode : Input → List Bool := prodCode unaryCode (prodCode ratCode ratCode)

noncomputable opaque precisionProgram : Procedure unaryCode unaryCode precision :=
  (Procedure.unaryMul.comp ((Procedure.constant unaryCode unaryCode (4*guard^2)).pair
    Procedure.unarySuccessor)).congrFun (by intro p; rfl)

noncomputable opaque normSquareProgram : Procedure (prodCode ratCode ratCode) ratCode
    (fun q => q.1^2+q.2^2) := by
  let x := Procedure.first ratCode ratCode
  let y := Procedure.second ratCode ratCode
  let xx := Procedure.ratMul.comp (x.pair x)
  let yy := Procedure.ratMul.comp (y.pair y)
  exact (Procedure.ratAdd.comp (xx.pair yy)).congrFun (by intro q; simp only [pow_two]; rfl)

noncomputable opaque program : Procedure inputCode ratCode
    (fun x => approximate x.1 x.2) := by
  let p := precisionProgram.comp (Procedure.first unaryCode (prodCode ratCode ratCode))
  let q := Procedure.second unaryCode (prodCode ratCode ratCode)
  let r := Procedure.constant inputCode unaryCode 2
  let one := Procedure.constant inputCode ratCode (1:ℚ)
  let zero := Procedure.constant inputCode ratCode (0:ℚ)
  let two := Procedure.constant inputCode ratCode (2:ℚ)
  let norm := normSquareProgram.comp q
  let inside := Procedure.intSign.comp (Procedure.ratNum.comp (Procedure.ratSub.comp (norm.pair one)))
  let forcing := Procedure.ratNeg.comp (PlanarForcingProgram.program.comp q)
  let phi := ResolventSchedule.program.comp ((r.pair p).pair q)
  let sample := Procedure.ratDiv.comp (forcing.pair (Procedure.ratMul.comp (two.pair phi)))
  exact (Procedure.conditional inside sample zero).congrFun (by
    intro x
    simp only [Function.comp_apply,Rat.num_neg,decide_eq_true_eq]
    unfold approximate outside
    change (if x.2.1^2+x.2.2^2-1 < 0 then
      -PlanarForcingProgram.value x.2/(2*ResolventSchedule.approximate ((2,precision x.1),x.2))
      else 0) = (if 1 ≤ x.2.1^2+x.2.2^2 then 0 else
      -PlanarForcingProgram.value x.2/(2*ResolventSchedule.approximate ((2,precision x.1),x.2)))
    by_cases hq : 1 ≤ x.2.1^2+x.2.2^2
    · rw [ite_eq_right (by linarith),ite_eq_left hq]
    · rw [ite_eq_left (by linarith),ite_eq_right hq])

end ContinuumCoulomb.PlanarWellNumerics

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_ManufacturedFieldProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal polynomial TM2 scalar evaluator for the actual manufactured
three-dimensional well field. All sites, widths and scales are input data. -/

namespace ContinuumCoulomb.ManufacturedFieldEvaluation
open ExactQuantumFactoring.BitStackProgram

def planarCode : PlanarInput → List Bool := prodCode unaryCode
  (prodCode ratCode (prodCode sitesCode pointCode))
def termCode : TermInput → List Bool := prodCode planarCode pointCode
abbrev Input := ℕ×((ℚ×ℚ)×(List (ℚ×ℚ)×CappedKernelProgram.Triple))
def inputCode : Input → List Bool := prodCode unaryCode
  (prodCode (prodCode ratCode ratCode) (prodCode sitesCode CappedKernelProgram.tripleCode))

noncomputable opaque translateProgram : Procedure (prodCode pointCode pointCode) pointCode
    (fun x => translate x.1 x.2) := by
  let a := Procedure.first pointCode pointCode
  let b := Procedure.second pointCode pointCode
  let a0 := (Procedure.first ratCode ratCode).comp a
  let a1 := (Procedure.second ratCode ratCode).comp a
  let b0 := (Procedure.first ratCode ratCode).comp b
  let b1 := (Procedure.second ratCode ratCode).comp b
  exact (Procedure.ratSub.comp (a0.pair b0)).pair (Procedure.ratSub.comp (a1.pair b1))

noncomputable opaque termEnvironmentProgram : Procedure termCode planarCode Prod.fst :=
  Procedure.first planarCode pointCode
noncomputable opaque termSiteProgram : Procedure termCode pointCode Prod.snd :=
  Procedure.second planarCode pointCode
noncomputable opaque termPrecisionProgram : Procedure termCode unaryCode (fun x => x.1.1) :=
  (Procedure.first unaryCode (prodCode ratCode (prodCode sitesCode pointCode))).comp termEnvironmentProgram
noncomputable opaque termDataProgram : Procedure termCode
    (prodCode ratCode (prodCode sitesCode pointCode)) (fun x => x.1.2) :=
  (Procedure.second unaryCode _).comp termEnvironmentProgram
noncomputable opaque termScaleProgram : Procedure termCode ratCode (fun x => x.1.2.1) :=
  (Procedure.first ratCode _).comp termDataProgram
noncomputable opaque termListPointProgram : Procedure termCode (prodCode sitesCode pointCode)
    (fun x => x.1.2.2) := (Procedure.second ratCode _).comp termDataProgram
noncomputable opaque termSitesProgram : Procedure termCode sitesCode (fun x => x.1.2.2.1) :=
  (Procedure.first sitesCode pointCode).comp termListPointProgram
noncomputable opaque termPointProgram : Procedure termCode pointCode (fun x => x.1.2.2.2) :=
  (Procedure.second sitesCode pointCode).comp termListPointProgram

noncomputable opaque termRowProgram (rho : ℕ) : Procedure termCode ratCode
    (fun x => CountertermEvaluation.row rho x.1.1 x.2 x.1.2.2.1) :=
  (CountertermEvaluation.rowProgram rho).comp
    (termPrecisionProgram.pair (termSiteProgram.pair termSitesProgram))

noncomputable opaque termFractionProgram (rho : ℕ) : Procedure termCode ratCode
    (fun x => CountertermEvaluation.row rho x.1.1 x.2 x.1.2.2.1/x.1.2.1) :=
  Procedure.ratDiv.comp ((termRowProgram rho).pair termScaleProgram)

noncomputable opaque termClippedProgram (rho : ℕ) : Procedure termCode ratCode
    (fun x => RationalSmoothTransition.clip
      (CountertermEvaluation.row rho x.1.1 x.2 x.1.2.2.1/x.1.2.1)) :=
  SmoothTransitionProgram.clipProgram.comp (termFractionProgram rho)

noncomputable opaque coefficientProgram (rho : ℕ) : Procedure termCode ratCode
    (fun x => coefficient rho x.1.1 x.1.2.1 x.1.2.2.1 x.2) :=
  Procedure.ratAdd.comp ((Procedure.constant termCode ratCode (1:ℚ)).pair (termClippedProgram rho))

noncomputable opaque termRelativeProgram : Procedure termCode pointCode
    (fun x => translate x.1.2.2.2 x.2) :=
  translateProgram.comp (termPointProgram.pair termSiteProgram)

noncomputable opaque termWellProgram : Procedure termCode ratCode
    (fun x => PlanarWellNumerics.approximate x.1.1 (translate x.1.2.2.2 x.2)) :=
  by
    let p := PlanarWellNumerics.program.comp (termPrecisionProgram.pair termRelativeProgram)
    exact p.congrFun (by intro x; rfl)

noncomputable opaque termProgram (rho : ℕ) : Procedure termCode ratCode
    (fun x => coefficient rho x.1.1 x.1.2.1 x.1.2.2.1 x.2 *
      PlanarWellNumerics.approximate x.1.1 (translate x.1.2.2.2 x.2)) :=
  Procedure.ratMul.comp ((coefficientProgram rho).pair termWellProgram)

noncomputable opaque planarProgram (rho : ℕ) : Procedure planarCode ratCode
    (fun x => planar rho x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  let tail := Procedure.second unaryCode (prodCode ratCode (prodCode sitesCode pointCode))
  let listpoint := (Procedure.second ratCode (prodCode sitesCode pointCode)).comp tail
  let sites := (Procedure.first sitesCode pointCode).comp listpoint
  let mapped := (Procedure.listMapWith (ea := planarCode) (eb := pointCode) (ec := ratCode)
    (f := fun env a => coefficient rho env.1 env.2.1 env.2.2.1 a *
      PlanarWellNumerics.approximate env.1 (translate env.2.2.2 a))
    (0,0) 0 (termProgram rho)).comp ((Procedure.identity planarCode).pair sites)
  exact RationalSumProgram.sumProgram.comp mapped

noncomputable opaque precisionFactorsProgram : Procedure (prodCode unaryCode unaryCode)
    (prodCode unaryCode unaryCode) (fun x => ((x.1+1)^2,x.2+1)) := by
  let m := Procedure.unarySuccessor.comp (Procedure.first unaryCode unaryCode)
  let p := Procedure.unarySuccessor.comp (Procedure.second unaryCode unaryCode)
  exact ((Procedure.unaryMul.comp (m.pair m)).pair p).congrFun
    (by intro x; simp only [pow_two]; rfl)

noncomputable opaque precisionProgram (rho : ℕ) : Procedure (prodCode unaryCode unaryCode)
    unaryCode (fun x => precision rho x.1 x.2) := by
  let base := Procedure.unaryMul.comp precisionFactorsProgram
  let C := Procedure.constant (prodCode unaryCode unaryCode) unaryCode
    (16*(CountertermEvaluation.guard rho)^4)
  exact (Procedure.unaryMul.comp (C.pair base)).congrFun (by intro x; change 16*(CountertermEvaluation.guard rho)^4*((x.1+1)^2*(x.2+1)) = _; unfold precision; ring)

noncomputable opaque dataProgram : Procedure inputCode
    (prodCode (prodCode ratCode ratCode) (prodCode sitesCode CappedKernelProgram.tripleCode))
    (fun x => x.2) := Procedure.second unaryCode _
noncomputable opaque parametersProgram : Procedure inputCode (prodCode ratCode ratCode)
    (fun x => x.2.1) := (Procedure.first _ _).comp dataProgram
noncomputable opaque geometryProgram : Procedure inputCode (prodCode sitesCode CappedKernelProgram.tripleCode)
    (fun x => x.2.2) := (Procedure.second _ _).comp dataProgram
noncomputable opaque sitesProgram : Procedure inputCode sitesCode (fun x => x.2.2.1) :=
  (Procedure.first _ _).comp geometryProgram
noncomputable opaque pointProgram : Procedure inputCode CappedKernelProgram.tripleCode (fun x => x.2.2.2) :=
  (Procedure.second _ _).comp geometryProgram
noncomputable opaque scaleProgram : Procedure inputCode ratCode (fun x => x.2.1.1) :=
  (Procedure.first ratCode ratCode).comp parametersProgram
noncomputable opaque widthProgram : Procedure inputCode ratCode (fun x => x.2.1.2) :=
  (Procedure.second ratCode ratCode).comp parametersProgram
noncomputable opaque coordinateTailProgram : Procedure inputCode (prodCode ratCode ratCode)
    (fun x => x.2.2.2.2) := (Procedure.second ratCode (prodCode ratCode ratCode)).comp pointProgram
noncomputable opaque planarPointProgram : Procedure inputCode pointCode
    (fun x => (x.2.2.2.1,x.2.2.2.2.1)) :=
  ((Procedure.first ratCode (prodCode ratCode ratCode)).comp pointProgram).pair
    ((Procedure.first ratCode ratCode).comp coordinateTailProgram)
noncomputable opaque heightProgram : Procedure inputCode ratCode (fun x => x.2.2.2.2.2) :=
  (Procedure.second ratCode ratCode).comp coordinateTailProgram

noncomputable opaque rawCutoffProgram : Procedure inputCode ratCode
    (fun x => RationalSmoothTransition.clip (VerticalCutoffProgram.value (x.1,(x.2.1.2,x.2.2.2.2.2)))) := by
  let p : Procedure inputCode unaryCode Prod.fst := Procedure.first unaryCode
    (prodCode (prodCode ratCode ratCode) (prodCode sitesCode CappedKernelProgram.tripleCode))
  exact SmoothTransitionProgram.clipProgram.comp (VerticalCutoffProgram.program.comp
    (p.pair (widthProgram.pair heightProgram)))

noncomputable opaque rawPlanarProgram (rho : ℕ) : Procedure inputCode ratCode
    (fun x => planar rho x.1 x.2.1.1 x.2.2.1 (x.2.2.2.1,x.2.2.2.2.1)) :=
  by
    let p := (planarProgram rho).comp ((Procedure.first unaryCode
      (prodCode (prodCode ratCode ratCode) (prodCode sitesCode CappedKernelProgram.tripleCode))).pair
      (scaleProgram.pair (sitesProgram.pair planarPointProgram)))
    exact p.congrFun (by intro x; rfl)

noncomputable opaque rawProgram (rho : ℕ) : Procedure inputCode ratCode
    (fun x => rawValue rho x.1 x.2.1.1 x.2.1.2 x.2.2.1 x.2.2.2) :=
  Procedure.ratMul.comp (rawCutoffProgram.pair (rawPlanarProgram rho))

noncomputable opaque inputPrecisionProgram (rho : ℕ) : Procedure inputCode unaryCode
    (fun x => precision rho x.2.2.1.length x.1) := by
  let p : Procedure inputCode unaryCode Prod.fst := Procedure.first unaryCode
    (prodCode (prodCode ratCode ratCode) (prodCode sitesCode CappedKernelProgram.tripleCode))
  let m := (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength pointCode (0,0)).comp sitesProgram
  exact (precisionProgram rho).comp (m.pair p)

noncomputable opaque program (rho : ℕ) : Procedure inputCode ratCode
    (fun x => value rho x.1 x.2.1.1 x.2.1.2 x.2.2.1 x.2.2.2) :=
  by
    let p := (rawProgram rho).comp ((inputPrecisionProgram rho).pair dataProgram)
    exact p.congrFun (by intro x; rfl)

end ContinuumCoulomb.ManufacturedFieldEvaluation

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_MoserDifferenceProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal polynomial integer arithmetic for the fixed finite-difference
precision and rational step of the manufactured field evaluator. -/

namespace ContinuumCoulomb.MoserDifferenceBudget
open ExactQuantumFactoring.BitStackProgram

noncomputable opaque nextSquareProgram : Procedure unaryCode unaryCode (fun P => (P+1)^2) :=
  (Procedure.unaryMul.comp (Procedure.unarySuccessor.pair Procedure.unarySuccessor)).congrFun
    (by intro P; simp only [pow_two]; rfl)

noncomputable opaque nextCubeProgram : Procedure unaryCode unaryCode (fun P => (P+1)^3) :=
  (Procedure.unaryMul.comp (nextSquareProgram.pair Procedure.unarySuccessor)).congrFun
    (by intro P; simp only [pow_succ]; rfl)

/-- A fixed integer bounds the finite-difference precision independently of the
input instance. -/
noncomputable opaque precisionScaleData : {n : ℕ // n = 16384*guard^2} := ⟨16384*guard^2,rfl⟩
noncomputable def precisionScale : ℕ := precisionScaleData.val

theorem precisionScale_eq : precisionScale = 16384*guard^2 := precisionScaleData.property

noncomputable opaque precisionProgram : Procedure unaryCode unaryCode precision := by
  let p := Procedure.unaryMul.comp ((Procedure.constant unaryCode unaryCode precisionScale).pair nextCubeProgram)
  exact p.congrFun (by
    intro P
    change precisionScale*(P+1)^3 = precision P
    rw [precisionScale_eq]
    rfl)

noncomputable opaque stepDenominatorProgram : Procedure unaryCode ratCode
    (fun P => 16*(guard:ℚ)*(P+1)) := by
  let c := Procedure.constant unaryCode ratCode (16*(guard:ℚ))
  let p := Procedure.natToRat.comp (Procedure.unaryToBits.comp Procedure.unarySuccessor)
  exact (Procedure.ratMul.comp (c.pair p)).congrFun (by intro P; change 16*(guard:ℚ)*(Nat.succ P:ℚ) = _; simp only [Nat.cast_succ])

noncomputable opaque stepProgram : Procedure unaryCode ratCode step :=
  Procedure.ratInv.comp stepDenominatorProgram

end ContinuumCoulomb.MoserDifferenceBudget

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_ManufacturedVelocityProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The manufactured Moser velocity has a literal polynomial TM2 evaluator.
It composes the already certified field sampler, three fixed rational
coordinate differences, and the clamped positive-density quotient. -/

namespace ContinuumCoulomb.ManufacturedVelocityEvaluation
open ExactQuantumFactoring.BitStackProgram
open CappedKernelProgram (Triple tripleCode)

def environmentCode : Environment → List Bool := prodCode unaryCode
  (prodCode (prodCode ratCode ratCode) ManufacturedFieldEvaluation.sitesCode)
def sampleCode : (Environment×Triple) → List Bool := prodCode environmentCode tripleCode
abbrev Input := Environment×(ℚ×Triple)
def inputCode : Input → List Bool := prodCode environmentCode (prodCode ratCode tripleCode)

noncomputable opaque envPrecisionProgram : Procedure environmentCode unaryCode Prod.fst :=
  Procedure.first unaryCode _
noncomputable opaque envDataProgram : Procedure environmentCode
    (prodCode (prodCode ratCode ratCode) ManufacturedFieldEvaluation.sitesCode) Prod.snd :=
  Procedure.second unaryCode _
noncomputable opaque envParametersProgram : Procedure environmentCode (prodCode ratCode ratCode)
    (fun e => e.2.1) := (Procedure.first _ _).comp envDataProgram
noncomputable opaque envSitesProgram : Procedure environmentCode ManufacturedFieldEvaluation.sitesCode
    (fun e => e.2.2) := (Procedure.second _ _).comp envDataProgram
noncomputable opaque innerPrecisionProgram (rho : ℕ) : Procedure unaryCode unaryCode (precision rho) :=
  (Procedure.unaryMul.comp ((Procedure.constant unaryCode unaryCode
    (12*(1+MoserDifferenceBudget.guard*(4*rho+1)))).pair Procedure.unarySuccessor))

noncomputable opaque sampleEnvironmentProgram : Procedure sampleCode environmentCode Prod.fst :=
  Procedure.first environmentCode tripleCode
noncomputable opaque samplePointProgram : Procedure sampleCode tripleCode Prod.snd :=
  Procedure.second environmentCode tripleCode
noncomputable opaque samplePrecisionProgram : Procedure sampleCode unaryCode
    (fun x => MoserDifferenceBudget.precision x.1.1) :=
  MoserDifferenceBudget.precisionProgram.comp (envPrecisionProgram.comp sampleEnvironmentProgram)
noncomputable opaque sampleDataProgram : Procedure sampleCode
    (prodCode (prodCode ratCode ratCode) (prodCode ManufacturedFieldEvaluation.sitesCode tripleCode))
    (fun x => (x.1.2.1,(x.1.2.2,x.2))) :=
  (envParametersProgram.comp sampleEnvironmentProgram).pair
    ((envSitesProgram.comp sampleEnvironmentProgram).pair samplePointProgram)
noncomputable opaque scalarSampleProgram (rho : ℕ) : Procedure sampleCode ratCode
    (fun x => sample rho x.1.1 x.1.2.1.1 x.1.2.1.2 x.1.2.2 x.2) :=
  by
    let p := (ManufacturedFieldEvaluation.program rho).comp (samplePrecisionProgram.pair sampleDataProgram)
    exact p.congrFun (by intro x; rfl)
noncomputable opaque spatialStepProgram : Procedure environmentCode ratCode
    (fun e => MoserDifferenceBudget.step e.1) :=
  MoserDifferenceBudget.stepProgram.comp envPrecisionProgram

noncomputable opaque gradientProgram (rho : ℕ) (a : Fin 3) : Procedure sampleCode ratCode
    (fun x => gradient rho x.1.1 x.1.2.1.1 x.1.2.1.2 x.1.2.2 x.2 a) :=
  by
    let p := FiniteDifferenceProgram.firstProgram (E := Environment) (ce := environmentCode)
      (sample := fun e q => sample rho e.1 e.2.1.1 e.2.1.2 e.2.2 q)
      (step := fun e => MoserDifferenceBudget.step e.1) a (scalarSampleProgram rho) spatialStepProgram
    exact p.congrFun (by intro x; rfl)
noncomputable opaque laplacianProgram (rho : ℕ) : Procedure sampleCode ratCode
    (fun x => laplacian rho x.1.1 x.1.2.1.1 x.1.2.1.2 x.1.2.2 x.2) :=
  by
    let p := FiniteDifferenceProgram.laplacianProgram (E := Environment) (ce := environmentCode)
      (sample := fun e q => sample rho e.1 e.2.1.1 e.2.1.2 e.2.2 q)
      (step := fun e => MoserDifferenceBudget.step e.1) (scalarSampleProgram rho) spatialStepProgram
    exact p.congrFun (by intro x; rfl)
noncomputable opaque piProgram : Procedure environmentCode ratCode (fun e => pi e.1) :=
  PiProgram.program.comp ((Procedure.unaryMul.comp
    ((Procedure.constant unaryCode unaryCode 8).pair Procedure.unarySuccessor)).comp envPrecisionProgram)

noncomputable opaque inputEnvironmentProgram : Procedure inputCode environmentCode Prod.fst :=
  Procedure.first environmentCode (prodCode ratCode tripleCode)
noncomputable opaque inputTimePointProgram : Procedure inputCode (prodCode ratCode tripleCode) Prod.snd :=
  Procedure.second environmentCode (prodCode ratCode tripleCode)
noncomputable opaque inputTimeProgram : Procedure inputCode ratCode (fun x => x.2.1) :=
  (Procedure.first ratCode tripleCode).comp inputTimePointProgram
noncomputable opaque inputPointProgram : Procedure inputCode tripleCode (fun x => x.2.2) :=
  (Procedure.second ratCode tripleCode).comp inputTimePointProgram
noncomputable opaque inputSampleProgram : Procedure inputCode sampleCode (fun x => (x.1,x.2.2)) :=
  inputEnvironmentProgram.pair inputPointProgram
noncomputable opaque rawDenominatorProgram (rho : ℕ) : Procedure inputCode ratCode
    (fun x => 4*pi x.1.1*(rho:ℚ)+x.2.1*laplacian rho x.1.1 x.1.2.1.1 x.1.2.1.2 x.1.2.2 x.2.2) := by
  let base := Procedure.ratMul.comp ((Procedure.constant inputCode ratCode (4:ℚ)).pair
    (piProgram.comp inputEnvironmentProgram))
  let first := Procedure.ratMul.comp (base.pair (Procedure.constant inputCode ratCode (rho:ℚ)))
  let second := Procedure.ratMul.comp (inputTimeProgram.pair ((laplacianProgram rho).comp inputSampleProgram))
  exact Procedure.ratAdd.comp (first.pair second)

noncomputable opaque maxDensityProgram (rho : ℕ) : Procedure ratCode ratCode (fun q => max (rho:ℚ) q) := by
  let q := Procedure.identity ratCode
  let r := Procedure.constant ratCode ratCode (rho:ℚ)
  let negative := Procedure.intSign.comp (Procedure.ratNum.comp (Procedure.ratSub.comp (q.pair r)))
  exact (Procedure.conditional negative r q).congrFun (by
    intro q
    simp only [Function.comp_apply,Rat.num_neg,decide_eq_true_eq,id_eq]
    split_ifs with h
    · exact (max_eq_left (by linarith)).symm
    · exact (max_eq_right (by linarith)).symm)

noncomputable opaque denominatorProgram (rho : ℕ) : Procedure inputCode ratCode
    (fun x => max (rho:ℚ) (4*pi x.1.1*(rho:ℚ)+x.2.1*
      laplacian rho x.1.1 x.1.2.1.1 x.1.2.1.2 x.1.2.2 x.2.2)) :=
  (maxDensityProgram rho).comp (rawDenominatorProgram rho)
noncomputable opaque coreComponentProgram (rho : ℕ) (a : Fin 3) : Procedure inputCode ratCode
    (fun x => -gradient rho x.1.1 x.1.2.1.1 x.1.2.1.2 x.1.2.2 x.2.2 a /
      max (rho:ℚ) (4*pi x.1.1*(rho:ℚ)+x.2.1*
        laplacian rho x.1.1 x.1.2.1.1 x.1.2.1.2 x.1.2.2 x.2.2)) :=
  Procedure.ratDiv.comp ((Procedure.ratNeg.comp ((gradientProgram rho a).comp inputSampleProgram)).pair
    (denominatorProgram rho))
noncomputable opaque preparedEnvironmentProgram (rho : ℕ) : Procedure environmentCode environmentCode
    (fun e => (precision rho e.1,e.2)) :=
  ((innerPrecisionProgram rho).comp envPrecisionProgram).pair envDataProgram
noncomputable opaque preparedInputProgram (rho : ℕ) : Procedure inputCode inputCode
    (fun x => ((precision rho x.1.1,x.1.2),x.2)) :=
  ((preparedEnvironmentProgram rho).comp inputEnvironmentProgram).pair inputTimePointProgram
noncomputable opaque componentProgram (rho : ℕ) (a : Fin 3) : Procedure inputCode ratCode
    (fun x => component rho x.1.1 x.1.2.1.1 x.1.2.1.2 x.1.2.2 x.2.1 x.2.2 a) :=
  by
    let p := (coreComponentProgram rho a).comp (preparedInputProgram rho)
    exact p.congrFun (by intro x; rfl)
noncomputable opaque program (rho : ℕ) : Procedure inputCode tripleCode
    (fun x => value rho x.1.1 x.1.2.1.1 x.1.2.1.2 x.1.2.2 x.2.1 x.2.2) :=
  (componentProgram rho 0).pair ((componentProgram rho 1).pair (componentProgram rho 2))

end ContinuumCoulomb.ManufacturedVelocityEvaluation

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_MoserCoordinateProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A deterministic polynomial TM2 program for the actual rounded Moser
coordinate construction. The fixed integers U,C occur as hardcoded constants;
precision is unary and geometric input data are binary rationals. -/

namespace ContinuumCoulomb.ManufacturedEuler
open ExactQuantumFactoring.BitStackProgram
open CappedKernelProgram (Triple tripleCode)
open EulerRegisters

abbrev Input := ManufacturedFieldEvaluation.Input
def inputCode : Input → List Bool := ManufacturedFieldEvaluation.inputCode

noncomputable def value (rho U C : ℕ) (x : Input) : Triple :=
  approximate rho U C x.1 x.2.1.1 x.2.1.2 x.2.2.1 x.2.2.2

noncomputable opaque stepsProgram (C : ℕ) : Procedure unaryCode unaryCode (steps C) :=
  Procedure.unaryMul.comp ((Procedure.constant unaryCode unaryCode (16*C^2)).pair Procedure.unarySuccessor)
noncomputable opaque inputStepsProgram (C : ℕ) : Procedure inputCode unaryCode (fun x => steps C x.1) :=
  (stepsProgram C).comp (Procedure.first unaryCode
    (prodCode (prodCode ratCode ratCode) (prodCode ManufacturedFieldEvaluation.sitesCode tripleCode)))
noncomputable opaque denominatorProgram (C : ℕ) : Procedure inputCode Nat.bits (fun x => denominator C x.1) := by
  let n := Procedure.unaryToBits.comp (inputStepsProgram C)
  exact (Procedure.binaryMul.comp (n.pair n)).congrFun (by intro x; simp only [denominator,pow_two]; rfl)
noncomputable opaque inputPointProgram : Procedure inputCode tripleCode (fun x => x.2.2.2) :=
  ManufacturedFieldEvaluation.pointProgram

noncomputable opaque inputRadiusProgram : Procedure tripleCode Nat.bits inputRadius := by
  let a := Procedure.intAbs.comp (Procedure.ratNum.comp tripleFirstProgram)
  let b := Procedure.intAbs.comp (Procedure.ratNum.comp tripleSecondProgram)
  let c := Procedure.intAbs.comp (Procedure.ratNum.comp tripleThirdProgram)
  exact Procedure.binaryAdd.comp ((Procedure.binaryAdd.comp (a.pair b)).pair c)
noncomputable opaque boxProgram (U C : ℕ) : Procedure inputCode Nat.bits
    (fun x => boxNumerator U (denominator C x.1) x.2.2.2) := by
  let r := inputRadiusProgram.comp inputPointProgram
  let u := Procedure.constant inputCode Nat.bits U
  let r' := Procedure.successor.comp (Procedure.binaryAdd.comp (r.pair u))
  exact (Procedure.binaryMul.comp ((denominatorProgram C).pair r')).congrFun (by intro x; rfl)
noncomputable opaque stepProgram (C : ℕ) : Procedure inputCode ratCode
    (fun x => (steps C x.1:ℚ)⁻¹) :=
  Procedure.ratInv.comp (Procedure.natToRat.comp (Procedure.unaryToBits.comp (inputStepsProgram C)))

noncomputable opaque environmentProgram (C : ℕ) :
    Procedure inputCode ManufacturedVelocityEvaluation.environmentCode
      (fun x => (steps C x.1,(x.2.1,x.2.2.1))) :=
  (inputStepsProgram C).pair
    (ManufacturedFieldEvaluation.parametersProgram.pair ManufacturedFieldEvaluation.sitesProgram)
noncomputable opaque parameterNumbersProgram (U C : ℕ) :
    Procedure inputCode (prodCode Nat.bits (prodCode Nat.bits ratCode))
      (fun x => (denominator C x.1,(boxNumerator U (denominator C x.1) x.2.2.2,(steps C x.1:ℚ)⁻¹))) :=
  (denominatorProgram C).pair ((boxProgram U C).pair (stepProgram C))
noncomputable opaque parametersProgram (U C : ℕ) :
    Procedure inputCode (parametersCode ManufacturedVelocityEvaluation.environmentCode)
      (fun x => ((steps C x.1,(x.2.1,x.2.2.1)),
        (denominator C x.1,(boxNumerator U (denominator C x.1) x.2.2.2,(steps C x.1:ℚ)⁻¹)))) :=
  (environmentProgram C).pair (parameterNumbersProgram U C)
noncomputable opaque registersProgram (U C : ℕ) : Procedure inputCode registersCode
    (fun x => round (denominator C x.1) (boxNumerator U (denominator C x.1) x.2.2.2) x.2.2.2) :=
  by
    let p := roundProgram.comp (((denominatorProgram C).pair (boxProgram U C)).pair inputPointProgram)
    exact p.congrFun (by intro x; rfl)
noncomputable opaque initialProgram (U C : ℕ) :
    Procedure inputCode (configCode ManufacturedVelocityEvaluation.environmentCode)
      (fun x => initial (steps C x.1,(x.2.1,x.2.2.1)) (steps C x.1) (denominator C x.1)
        (boxNumerator U (denominator C x.1) x.2.2.2)
        (round (denominator C x.1) (boxNumerator U (denominator C x.1) x.2.2.2) x.2.2.2)) :=
  (parametersProgram U C).pair
    ((Procedure.constant inputCode Nat.bits 0).pair (registersProgram U C))
noncomputable opaque runArgumentsProgram (U C : ℕ) :
    Procedure inputCode (prodCode unaryCode (configCode ManufacturedVelocityEvaluation.environmentCode))
      (fun x => (steps C x.1, initial (steps C x.1,(x.2.1,x.2.2.1)) (steps C x.1)
        (denominator C x.1) (boxNumerator U (denominator C x.1) x.2.2.2)
        (round (denominator C x.1) (boxNumerator U (denominator C x.1) x.2.2.2) x.2.2.2))) :=
  (inputStepsProgram C).pair (initialProgram U C)

theorem run_initial (rho : ℕ) (e : Environment) (N D B : ℕ) (r : Registers) :
    run (evaluate rho) (N,initial e N D B r) = trajectory (evaluate rho) e N D B r N := by
  change point (((advance (evaluate rho))^[N] (initial e N D B r)).1.2.1)
    (((advance (evaluate rho))^[N] (initial e N D B r)).2.2) = _
  rw [iterate_parameters]
  rfl

noncomputable opaque program (rho U C : ℕ) : Procedure inputCode tripleCode (value rho U C) := by
  let p := (EulerRegisters.program (E := Environment)
    (ce := ManufacturedVelocityEvaluation.environmentCode) (evaluate := evaluate rho)
    (ManufacturedVelocityEvaluation.program rho)).comp
    (runArgumentsProgram U C)
  exact p.congrFun (by
    intro x
    change run (evaluate rho) (steps C x.1,initial (steps C x.1,(x.2.1,x.2.2.1))
      (steps C x.1) (denominator C x.1) (boxNumerator U (denominator C x.1) x.2.2.2)
      (round (denominator C x.1) (boxNumerator U (denominator C x.1) x.2.2.2) x.2.2.2)) = _
    rw [run_initial]
    rfl)

end ContinuumCoulomb.ManufacturedEuler

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_TransformedGauss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual rational transport of Gauss nodes. A common polynomial precision
absorbs both the initial square-root error and the numerical flow error. -/

noncomputable section
open scoped NNReal
namespace ContinuumCoulomb.TransformedGauss
open CappedKernelProgram (Triple position)
open EulerRegisters (Registers)
open RationalGaussNodes (Signs)

def value (rho U C K P N : ℕ) (scale S : ℚ) (sites : List (ℚ×ℚ))
    (k : Registers) (b : Signs) : Triple :=
  let T := precision K P
  ManufacturedEuler.approximate rho U C T scale S sites (RationalGaussNodes.value T N k b)

end ContinuumCoulomb.TransformedGauss

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_TransformedGaussProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal polynomial TM2 program for the transported rational Gauss
node. The reciprocal mesh denominator and lattice coordinates are binary;
the requested reciprocal error bound is unary. -/

namespace ContinuumCoulomb.TransformedGauss
open ExactQuantumFactoring.BitStackProgram
open CappedKernelProgram (Triple tripleCode)
open EulerRegisters (Registers registersCode)
open RationalGaussNodes (Signs signsCode)

def inputCode : Input → List Bool :=
  prodCode (prodCode unaryCode Nat.bits)
    (prodCode (prodCode ratCode ratCode)
      (prodCode ManufacturedFieldEvaluation.sitesCode (prodCode registersCode signsCode)))

noncomputable def output (rho U C K : ℕ) (x : Input) : Triple :=
  value rho U C K x.1.1 x.1.2 x.2.1.1 x.2.1.2 x.2.2.1 x.2.2.2.1 x.2.2.2.2

noncomputable opaque precisionProgram (K : ℕ) : Procedure unaryCode unaryCode (precision K) := by
  let p := Procedure.unaryMul.comp
    ((Procedure.constant unaryCode unaryCode (2*(K+1))).pair Procedure.unarySuccessor)
  exact p.congrFun (by intro P; rfl)

noncomputable opaque inputParametersProgram : Procedure inputCode (prodCode unaryCode Nat.bits) Prod.fst :=
  Procedure.first _ _
noncomputable opaque dataProgram : Procedure inputCode
    (prodCode (prodCode ratCode ratCode)
      (prodCode ManufacturedFieldEvaluation.sitesCode (prodCode registersCode signsCode))) Prod.snd :=
  Procedure.second _ _
noncomputable opaque inputPrecisionProgram (K : ℕ) : Procedure inputCode unaryCode
    (fun x => precision K x.1.1) :=
  (precisionProgram K).comp ((Procedure.first unaryCode Nat.bits).comp inputParametersProgram)
noncomputable opaque denominatorProgram : Procedure inputCode Nat.bits (fun x => x.1.2) :=
  (Procedure.second unaryCode Nat.bits).comp inputParametersProgram
noncomputable opaque fieldParametersProgram : Procedure inputCode (prodCode ratCode ratCode)
    (fun x => x.2.1) := (Procedure.first _ _).comp dataProgram
noncomputable opaque tailProgram : Procedure inputCode
    (prodCode ManufacturedFieldEvaluation.sitesCode (prodCode registersCode signsCode))
    (fun x => x.2.2) := (Procedure.second _ _).comp dataProgram
noncomputable opaque sitesProgram : Procedure inputCode ManufacturedFieldEvaluation.sitesCode
    (fun x => x.2.2.1) := (Procedure.first _ _).comp tailProgram
noncomputable opaque nodeDataProgram : Procedure inputCode (prodCode registersCode signsCode)
    (fun x => x.2.2.2) := (Procedure.second _ _).comp tailProgram

noncomputable opaque nodeArgumentsProgram (K : ℕ) : Procedure inputCode RationalGaussNodes.inputCode
    (fun x => (precision K x.1.1,(x.1.2,x.2.2.2))) :=
  (inputPrecisionProgram K).pair (denominatorProgram.pair nodeDataProgram)
noncomputable opaque initialNodeProgram (K : ℕ) : Procedure inputCode tripleCode
    (fun x => RationalGaussNodes.value (precision K x.1.1) x.1.2 x.2.2.2.1 x.2.2.2.2) :=
  RationalGaussNodes.program.comp (nodeArgumentsProgram K)
noncomputable opaque flowArgumentsProgram (K : ℕ) : Procedure inputCode ManufacturedEuler.inputCode
    (fun x => (precision K x.1.1,(x.2.1,(x.2.2.1,
      RationalGaussNodes.value (precision K x.1.1) x.1.2 x.2.2.2.1 x.2.2.2.2)))) :=
  (inputPrecisionProgram K).pair
    (fieldParametersProgram.pair (sitesProgram.pair (initialNodeProgram K)))

noncomputable opaque program (rho U C K : ℕ) : Procedure inputCode tripleCode (output rho U C K) := by
  let p := (ManufacturedEuler.program rho U C).comp (flowArgumentsProgram K)
  exact p.congrFun (by intro x; rfl)

end ContinuumCoulomb.TransformedGauss

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_TransformedGaussList
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The same certified node program is applied to the whole finite list of
Gauss labels. It preserves the nucleus count and, at the proved precision,
pairwise distinctness. -/

open scoped NNReal
namespace ContinuumCoulomb.TransformedGauss
open ExactQuantumFactoring.BitStackProgram
open CappedKernelProgram (Triple tripleCode position)
open EulerRegisters (Registers registersCode)
open RationalGaussNodes (Signs signsCode)

def labelCode : Label → List Bool := prodCode registersCode signsCode
def listInputCode : (Environment×List Label) → List Bool :=
  prodCode environmentCode (listCode labelCode)

noncomputable def nodes (rho U C K : ℕ) (x : Environment×List Label) : List Triple :=
  x.2.map (fun l => value rho U C K x.1.1.1 x.1.1.2 x.1.2.1.1 x.1.2.1.2 x.1.2.2 l.1 l.2)

noncomputable opaque nodeEnvironmentProgram :
    Procedure (prodCode environmentCode labelCode) environmentCode Prod.fst :=
  Procedure.first _ _
noncomputable opaque nodeLabelProgram :
    Procedure (prodCode environmentCode labelCode) labelCode Prod.snd := Procedure.second _ _
noncomputable opaque nodeParametersProgram :
    Procedure (prodCode environmentCode labelCode) (prodCode unaryCode Nat.bits)
      (fun x => x.1.1) := (Procedure.first _ _).comp nodeEnvironmentProgram
noncomputable opaque nodeFieldProgram :
    Procedure (prodCode environmentCode labelCode)
      (prodCode (prodCode ratCode ratCode) ManufacturedFieldEvaluation.sitesCode)
      (fun x => x.1.2) := (Procedure.second _ _).comp nodeEnvironmentProgram
noncomputable opaque nodeArgumentProgram :
    Procedure (prodCode environmentCode labelCode) inputCode
      (fun x => (x.1.1,(x.1.2.1,(x.1.2.2,x.2)))) :=
  nodeParametersProgram.pair
    (((Procedure.first _ _).comp nodeFieldProgram).pair
      (((Procedure.second _ _).comp nodeFieldProgram).pair nodeLabelProgram))

noncomputable opaque listProgram (rho U C K : ℕ) :
    Procedure listInputCode (listCode tripleCode) (nodes rho U C K) := by
  let sample := (program rho U C K).comp nodeArgumentProgram
  exact (Procedure.listMapWith (ea := environmentCode) (eb := labelCode) (ec := tripleCode)
    (f := fun e l => value rho U C K e.1.1 e.1.2 e.2.1.1 e.2.1.2 e.2.2 l.1 l.2)
    ((0,(0,0)),(false,(false,false))) (0,(0,0)) sample).congrFun (by intro x; rfl)

end ContinuumCoulomb.TransformedGauss

end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_BitStackDependentChoice
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram.Procedure
variable {α β : Type} {ea : α→List Bool} {eb : β→List Bool} {f : α→β}
noncomputable def chooseBitD (c : α→Prop) [DecidablePred c]
    (p : Procedure (fun x:{a // ¬c a}=>ea x.val) eb (fun x=>f x.val))
    (q : Procedure (fun x:{a // c a}=>ea x.val) eb (fun x=>f x.val)) :
    Procedure (fun a=>decide (c a)::ea a) eb f where
  K:=(p.K ⊕ q.K) ⊕ Fin 2
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=Sum.inr 0
  output:=Sum.inr 0
  program:=.cases (Sum.inr 0) .skip
    (p.shared.program.relabel (leftPublic p.K q.K))
    (q.shared.program.relabel (rightPublic p.K q.K))
  bound:=p.shared.bound+q.shared.bound+1
  runs a:=by
    have hpmono:=eval_nat_mono p.shared.bound (Nat.le_succ (ea a).length)
    have hqmono:=eval_nat_mono q.shared.bound (Nat.le_succ (ea a).length)
    by_cases h:c a
    · obtain ⟨t,ht,hd⟩:=q.shared.runs ⟨a,h⟩
      have hh:=hd.relabel (rightPublic p.K q.K) (fun _=>[])
      simp only [overlay_singleton] at hh
      have he : rightPublic p.K q.K q.shared.input=Sum.inr 0:=rfl
      rw [he] at hh
      refine ⟨t+1,?_,?_⟩
      · simpa only [List.length_cons,Polynomial.eval_add,Polynomial.eval_one] using
          Nat.add_le_add_right ((ht.trans hqmono).trans (Nat.le_add_left
            (q.shared.bound.eval ((ea a).length+1)) (p.shared.bound.eval ((ea a).length+1)))) 1
      · simp only [h,decide_true]
        have hu : Function.update (singletonStore (Sum.inr 0 : (p.K⊕q.K)⊕Fin 2)
            (true::ea a)) (Sum.inr 0) (ea a)=singletonStore (Sum.inr 0) (ea a):=by
          simp [singletonStore]
        simpa only [hu] using Runs.cases_true (p:=Program.skip)
          (q:=p.shared.program.relabel (leftPublic p.K q.K))
          (xs:=ea a) (s:=singletonStore (Sum.inr 0) (true::ea a)) (by simp [singletonStore])
          (by rw [hu];exact hh)
    · obtain ⟨t,ht,hd⟩:=p.shared.runs ⟨a,h⟩
      have hh:=hd.relabel (leftPublic p.K q.K) (fun _=>[])
      simp only [overlay_singleton] at hh
      have he : leftPublic p.K q.K p.shared.input=Sum.inr 0:=rfl
      rw [he] at hh
      refine ⟨t+1,?_,?_⟩
      · simpa only [List.length_cons,Polynomial.eval_add,Polynomial.eval_one] using
          Nat.add_le_add_right ((ht.trans hpmono).trans (Nat.le_add_right
            (p.shared.bound.eval ((ea a).length+1)) (q.shared.bound.eval ((ea a).length+1)))) 1
      · simp only [h,decide_false]
        have hu : Function.update (singletonStore (Sum.inr 0 : (p.K⊕q.K)⊕Fin 2)
            (false::ea a)) (Sum.inr 0) (ea a)=singletonStore (Sum.inr 0) (ea a):=by
          simp [singletonStore]
        simpa only [hu] using Runs.cases_false (p:=Program.skip)
          (r:=q.shared.program.relabel (rightPublic p.K q.K))
          (xs:=ea a) (s:=singletonStore (Sum.inr 0) (false::ea a)) (by simp [singletonStore])
          (by rw [hu];exact hh)
noncomputable def splitOn (c : α→Prop) [DecidablePred c]
    (test : Procedure ea boolCode (fun a=>decide (c a)))
    (yes : Procedure (fun x:{a // c a}=>ea x.val) eb (fun x=>f x.val))
    (no : Procedure (fun x:{a // ¬c a}=>ea x.val) eb (fun x=>f x.val)) : Procedure ea eb f:=by
  let p:=no.comp (unprefix (fun x:{a // ¬c a}=>ea x.val) false)
  let q:=yes.comp (unprefix (fun x:{a // c a}=>ea x.val) false)
  let choice:=(chooseBitD c p q).comp (unprefix (fun a=>decide (c a)::false::ea a) true)
  let input:= (test.pair (identity ea)).result (ec:=fun a=>true::decide (c a)::false::ea a)
    (h:=id) (by intro a;rfl)
  exact choice.comp input
end ExactQuantumFactoring.BitStackProgram.Procedure

end



end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_PrefixPrograms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal prefixCode parsing for the source serialization. A parser emits
the first encoded field and its untouched following bit string. -/

namespace ContinuumCoulomb.PrefixPrograms
open ExactQuantumFactoring.BitStackProgram

abbrev Splitter {α : Type} (c : BinaryEncoding.Codec α) :=
  Procedure (prefixCode c) (prodCode c.encode id) id

noncomputable def natural : Splitter BinaryEncoding.natural := by
  let num : Procedure (prodCode Nat.bits id) BinaryEncoding.natural.encode Prod.fst :=
    EncodingPrograms.naturalOutput.comp (Procedure.first Nat.bits id)
  let tail : Procedure (prodCode Nat.bits id) id Prod.snd := Procedure.second Nat.bits id
  exact (num.pair tail).congrEncoding (by
    intro x
    change quoteBits x.1.bits ++ x.2 = BinaryEncoding.encodeDigits x.1.bits ++ x.2
    rw [AmplificationProgram.encodeDigits_quote]) (by intro x; rfl)

noncomputable def integerPayload : Procedure (prefixCode BinaryEncoding.integer)
    (prodCode Nat.bits id) (fun x => (EncodingPrograms.integerPayload x.1, x.2)) :=
  (Procedure.tail.precompose (prefixCode BinaryEncoding.integer)).result (by
    rintro ⟨z, s⟩
    cases z <;>
      change BinaryEncoding.encodeDigits _ ++ s = quoteBits _ ++ s <;>
      rw [AmplificationProgram.encodeDigits_quote] <;> rfl)

noncomputable def integerSign : Procedure (prefixCode BinaryEncoding.integer) Procedure.boolCode
    (fun x => EncodingPrograms.integerNegative x.1) :=
  (Procedure.head.precompose (prefixCode BinaryEncoding.integer)).congrFun (by
    rintro ⟨z, s⟩
    cases z <;> rfl)

noncomputable def integerValue : Procedure (prefixCode BinaryEncoding.integer) intCode Prod.fst := by
  let payload : Procedure (prefixCode BinaryEncoding.integer) Nat.bits
      (fun x => EncodingPrograms.integerPayload x.1) :=
    (Procedure.first Nat.bits id).comp integerPayload
  let positive := Procedure.natToInt.comp payload
  let negative := Procedure.intNeg.comp (Procedure.natToInt.comp (Procedure.successor.comp payload))
  exact (Procedure.conditional integerSign negative positive).congrFun (by
    rintro ⟨z, s⟩
    cases z with
    | ofNat n => rfl
    | negSucc n => change -(↑(n + 1) : ℤ) = Int.negSucc n; omega)

noncomputable def integer : Splitter BinaryEncoding.integer :=
  ((EncodingPrograms.integerOutput.comp integerValue).pair
    ((Procedure.second Nat.bits id).comp integerPayload)).congrFun (by intro x; rfl)

section Pair
variable {α β : Type} (c : BinaryEncoding.Codec α) (d : BinaryEncoding.Codec β)
variable (pc : Splitter c) (pd : Splitter d)

noncomputable def pairHeader : Procedure (prefixCode (BinaryEncoding.pair c d))
    (prodCode c.encode (prefixCode d)) (fun x => (x.1.1, (x.1.2, x.2))) :=
  ((pc.precompose (fun x : (α × β) × List Bool => (x.1.1, d.encode x.1.2 ++ x.2))).congrEncoding
    (by intro x; exact (List.append_assoc _ _ _).symm) (by intro x; rfl)).result
      (by intro x; rfl)

noncomputable def pairFirst : Procedure (prefixCode (BinaryEncoding.pair c d)) c.encode
    (fun x => x.1.1) := (Procedure.first c.encode (prefixCode d)).comp (pairHeader c d pc)

noncomputable def pairRest : Procedure (prefixCode (BinaryEncoding.pair c d)) (prodCode d.encode id)
    (fun x => (x.1.2, x.2)) :=
  pd.comp ((Procedure.second c.encode (prefixCode d)).comp (pairHeader c d pc))

noncomputable def pairSecond : Procedure (prefixCode (BinaryEncoding.pair c d)) d.encode
    (fun x => x.1.2) := (Procedure.first d.encode id).comp (pairRest c d pc pd)

noncomputable def pairTail : Procedure (prefixCode (BinaryEncoding.pair c d)) id
    (fun x => x.2) := (Procedure.second d.encode id).comp (pairRest c d pc pd)

noncomputable def pairValue : Procedure (prefixCode (BinaryEncoding.pair c d))
    (BinaryEncoding.pair c d).encode (fun x => x.1) :=
  ((EncodingPrograms.appendPair c d).comp
    ((pairFirst c d pc).pair (pairSecond c d pc pd))).congrFun (by intro x; rfl)

noncomputable def pair : Splitter (BinaryEncoding.pair c d) :=
  ((pairValue c d pc pd).pair (pairTail c d pc pd)).congrFun (by intro x; rfl)

end Pair

end ContinuumCoulomb.PrefixPrograms

end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_BitStackListWords
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
lemma flatten_length_le_code (xs : List (List Bool)) :
    xs.flatten.length ≤ (listCode (id : List Bool→List Bool) xs).length := by
  induction xs with
  | nil=>simp [listCode]
  | cons x xs ih=>
    simp only [List.flatten_cons,List.length_append,listCode_length_cons,id_eq]
    omega
namespace Procedure
noncomputable def listJoinWords : Procedure (listCode (id : List Bool→List Bool)) id List.flatten := by
  let step:=(append.comp (swap (id : List Bool→List Bool) id))
  let rep:=foldList [] step Polynomial.X (by
    intro xs ys i
    change ((xs.take i).foldl (fun ys x=>ys++x) ys).length ≤ _
    rw [fold_append_words,List.length_append]
    have hh:=flatten_length_le_code (xs.take i)
    have ht:=listCode_length_take_le (id : List Bool→List Bool) i xs
    simp only [Polynomial.eval_X,id_eq]
    omega)
  exact (rep.comp ((identity (listCode (id : List Bool→List Bool))).pair
    (constant (listCode (id : List Bool→List Bool)) id []))).congrFun (by
      intro xs;change xs.foldl (fun ys x=>ys++x) []=xs.flatten
      simpa only [List.nil_append] using fold_append_words xs [])
noncomputable def listFlatMapWords {α : Type} {ea : α→List Bool} {f : α→List Bool}
    (d : α) (p : Procedure ea id f) : Procedure (listCode ea) id (fun xs=>xs.flatMap f) :=
  (listJoinWords.comp (listMap d [] p)).congrFun (by intro xs;rfl)
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_PrefixListPrograms
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual conversion of the source's counted prefix list to quoted
machine list registers. Each field is parsed by its literal splitter;
the loop count and all temporary word lengths are bounded by the input. -/

namespace ContinuumCoulomb.PrefixListPrograms
open ExactQuantumFactoring.BitStackProgram PrefixPrograms

def stateCode {α : Type} (c : BinaryEncoding.Codec α) : State α → List Bool :=
  fun s => prodCode Nat.bits (prodCode id (listCode c.encode)) (stateView c s)

theorem quoted_length {α : Type} (c : BinaryEncoding.Codec α) (xs : List α) :
    (listCode c.encode xs).length = 2 * (xs.flatMap c.encode).length + 2 * xs.length + 1 := by
  induction xs with
  | nil => simp [listCode]
  | cons a xs ih =>
    simp only [listCode_length_cons, List.flatMap_cons, List.length_append, List.length_cons, ih]
    omega

theorem stateCode_length {α : Type} (c : BinaryEncoding.Codec α) (s : State α) :
    (stateCode c s).length = 2 * s.1.length.bits.length +
      2 * ((s.1.flatMap c.encode).length + s.2.1.length) + 2 + (listCode c.encode s.2.2).length := by
  simp only [stateCode, stateView, prodCode, pairBits_length, List.length_append, id_eq]
  omega

theorem state_growth {α : Type} (c : BinaryEncoding.Codec α)
    (hc : ∀ a, 0 < (c.encode a).length) (s : State α) (i : ℕ) :
    (stateCode c (step^[i] s)).length ≤ 3 * (stateCode c s).length + 1 := by
  rcases s with ⟨xs, tail, acc⟩
  rw [step_iterate]
  have hn := bits_length_mono (show (xs.drop i).length ≤ xs.length by simp only [List.length_drop]; omega)
  have hsplit : ((xs.take i).flatMap c.encode).length + ((xs.drop i).flatMap c.encode).length =
      (xs.flatMap c.encode).length := by
    rw [← List.length_append, ← List.flatMap_append, List.take_append_drop]
  have hl := flat_length c hc xs
  have hacc := listCode_length_append c.encode (xs.take i).reverse acc
  rw [listCode_length_rev] at hacc
  have htake := listCode_length_take_le c.encode i xs
  rw [quoted_length c xs] at htake
  simp only [stateCode_length]
  omega

noncomputable def listOutput {α : Type} (c : BinaryEncoding.Codec α) (d : α) :
    Procedure (listCode c.encode) (BinaryEncoding.list c).encode id := by
  let emit : Procedure c.encode id c.encode := (Procedure.identity c.encode).result (by intro a; rfl)
  let flat := Procedure.listFlatMapWords d emit
  let count := Procedure.unaryToBits.comp (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength c.encode d)
  let header : Procedure (listCode c.encode) id (fun xs => BinaryEncoding.natural.encode xs.length) :=
    (EncodingPrograms.naturalOutput.comp count).result (by intro xs; rfl)
  exact (Procedure.append.comp (header.pair flat)).result (by intro xs; rfl)

section Parser
variable {α : Type} (c : BinaryEncoding.Codec α) (pc : Splitter c) (d : α)

noncomputable def countProgram : Procedure (stateCode c) Nat.bits (fun s => s.1.length) :=
  (Procedure.first Nat.bits (prodCode id (listCode c.encode))).precompose (stateView c)

noncomputable def streamProgram : Procedure (stateCode c) id
    (fun s => s.1.flatMap c.encode ++ s.2.1) :=
  ((Procedure.first id (listCode c.encode)).comp
    (Procedure.second Nat.bits (prodCode id (listCode c.encode)))).precompose (stateView c)

noncomputable def accProgram : Procedure (stateCode c) (listCode c.encode) (fun s => s.2.2) :=
  ((Procedure.second id (listCode c.encode)).comp
    (Procedure.second Nat.bits (prodCode id (listCode c.encode)))).precompose (stateView c)

noncomputable def headerProgram : Procedure (fun s : NonemptyState α => stateCode c s.val)
    (prodCode c.encode id)
    (fun s => (s.val.1.headD d, s.val.1.tail.flatMap c.encode ++ s.val.2.1)) := by
  let word := (streamProgram c).precompose (fun s : NonemptyState α => s.val)
  let asPrefix : Procedure (fun s : NonemptyState α => stateCode c s.val) (prefixCode c)
      (fun s => (s.val.1.headD d, s.val.1.tail.flatMap c.encode ++ s.val.2.1)) :=
    word.result (by
      rintro ⟨⟨xs, tail, acc⟩, h⟩
      cases xs with
      | nil => contradiction
      | cons a xs => simp only [List.flatMap_cons, List.headD_cons, List.tail_cons, prefixCode,
          id_eq, List.append_assoc])
  exact pc.comp asPrefix

noncomputable def nonemptyStep : Procedure (fun s : NonemptyState α => stateCode c s.val)
    (stateCode c) (fun s => step s.val) := by
  let head : Procedure (fun s : NonemptyState α => stateCode c s.val) c.encode
      (fun s => s.val.1.headD d) :=
    (Procedure.first c.encode id).comp (headerProgram c pc d)
  let tail : Procedure (fun s : NonemptyState α => stateCode c s.val) id
      (fun s => s.val.1.tail.flatMap c.encode ++ s.val.2.1) :=
    (Procedure.second c.encode id).comp (headerProgram c pc d)
  let acc := (accProgram c).precompose (fun s : NonemptyState α => s.val)
  let nextAcc := (Procedure.listCons c.encode).comp (head.pair acc)
  let count := (countProgram c).precompose (fun s : NonemptyState α => s.val)
  let nextCount := Procedure.binarySub.comp (count.pair
    (Procedure.constant (fun s : NonemptyState α => stateCode c s.val) Nat.bits 1))
  exact (nextCount.pair (tail.pair nextAcc)).result (by
    rintro ⟨⟨xs, tail, acc⟩, h⟩
    cases xs with
    | nil => contradiction
    | cons a xs => simp only [stateCode, stateView, step, List.headD_cons, List.tail_cons,
        List.length_cons, Nat.add_sub_cancel, Function.comp_apply])

noncomputable def stepProgram : Procedure (stateCode c) (stateCode c) step := by
  let test : Procedure (stateCode c) Procedure.boolCode (fun s => decide (s.1 = [])) :=
    (Procedure.binaryZero.comp (countProgram c)).congrFun (by
      intro s
      simp only [Function.comp_apply, List.length_eq_zero_iff])
  let yes : Procedure (fun s : {s : State α // s.1 = []} => stateCode c s.val)
      (stateCode c) (fun s => step s.val) :=
    ((Procedure.identity (stateCode c)).precompose (fun s : {s : State α // s.1 = []} => s.val)).congrFun
      (by intro s; simp only [id_eq, step, s.property])
  exact Procedure.splitOn (fun s : State α => s.1 = []) test yes (nonemptyStep c pc d)

noncomputable def iterationProgram (hc : ∀ a, 0 < (c.encode a).length) :
    Procedure (prodCode unaryCode (stateCode c)) (stateCode c) (fun x => step^[x.1] x.2) :=
  (stepProgram c pc d).iterate (Polynomial.C 3 * Polynomial.X + 1) (by
    intro n s i _
    have h := state_growth c hc s i
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      Polynomial.eval_one]
    omega)

noncomputable def inputCount : Procedure (prefixCode (BinaryEncoding.list c)) Nat.bits
    (fun x => x.1.length) :=
  ((Procedure.first Nat.bits id).precompose
    (fun x : List α × List Bool => (x.1.length, x.1.flatMap c.encode ++ x.2))).congrEncoding (by
      intro x
      change quoteBits x.1.length.bits ++ (x.1.flatMap c.encode ++ x.2) =
        (BinaryEncoding.encodeDigits x.1.length.bits ++ x.1.flatMap c.encode) ++ x.2
      rw [AmplificationProgram.encodeDigits_quote, List.append_assoc]) (by intro x; rfl)

noncomputable def inputStream : Procedure (prefixCode (BinaryEncoding.list c)) id
    (fun x => x.1.flatMap c.encode ++ x.2) :=
  ((Procedure.second Nat.bits id).precompose
    (fun x : List α × List Bool => (x.1.length, x.1.flatMap c.encode ++ x.2))).congrEncoding (by
      intro x
      change quoteBits x.1.length.bits ++ (x.1.flatMap c.encode ++ x.2) =
        (BinaryEncoding.encodeDigits x.1.length.bits ++ x.1.flatMap c.encode) ++ x.2
      rw [AmplificationProgram.encodeDigits_quote, List.append_assoc]) (by intro x; rfl)

noncomputable def startProgram : Procedure (prefixCode (BinaryEncoding.list c)) (stateCode c)
    (fun x => (x.1, x.2, [])) :=
  ((inputCount c).pair ((inputStream c).pair
    (Procedure.constant (prefixCode (BinaryEncoding.list c)) (listCode c.encode) []))).result
      (by intro x; rfl)

noncomputable def parseProgram (hc : ∀ a, 0 < (c.encode a).length) :
    Procedure (prefixCode (BinaryEncoding.list c)) (stateCode c)
      (fun x => ([], x.2, x.1.reverse)) := by
  let times : Procedure (prefixCode (BinaryEncoding.list c)) unaryCode
      (fun x => (prefixCode (BinaryEncoding.list c) x).length) :=
    Procedure.length.precompose (prefixCode (BinaryEncoding.list c))
  exact ((iterationProgram c pc d hc).comp (times.pair (startProgram c))).congrFun (by
    intro x
    change step^[(prefixCode (BinaryEncoding.list c) x).length] (x.1, x.2, []) = _
    rw [step_iterate, List.drop_eq_nil_of_le (input_length c hc x),
      List.take_of_length_le (input_length c hc x), List.append_nil])

noncomputable def parsedList (hc : ∀ a, 0 < (c.encode a).length) :
    Procedure (prefixCode (BinaryEncoding.list c)) (listCode c.encode) Prod.fst :=
  ((Procedure.listReverse c.encode d).comp ((accProgram c).comp (parseProgram c pc d hc))).congrFun
    (by intro x; exact List.reverse_reverse x.1)

noncomputable def parsedTail (hc : ∀ a, 0 < (c.encode a).length) :
    Procedure (prefixCode (BinaryEncoding.list c)) id Prod.snd :=
  ((streamProgram c).comp (parseProgram c pc d hc)).congrFun (by intro x; rfl)

noncomputable def listSplitter (hc : ∀ a, 0 < (c.encode a).length) : Splitter (BinaryEncoding.list c) :=
  (((listOutput c d).comp (parsedList c pc d hc)).pair (parsedTail c pc d hc)).congrFun (by intro x; rfl)

/-- Actual quoted-list conversion for a complete source field, with no
postulated record-decoding primitive. -/
noncomputable def listInput (hc : ∀ a, 0 < (c.encode a).length) :
    Procedure (BinaryEncoding.list c).encode (listCode c.encode) id :=
  ((parsedList c pc d hc).precompose (fun xs : List α => (xs, []))).congrEncoding
    (by intro xs; exact List.append_nil _) (by intro xs; rfl)

end Parser

end ContinuumCoulomb.PrefixListPrograms

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_SourcePrograms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal finite-stack decoding of every source field, including counted
coordinate/edge lists and noncanonical rational pairs. The resulting
registers use the existing proved machine list and rational arithmetic. -/

namespace ContinuumCoulomb.SourcePrograms
open ExactQuantumFactoring.BitStackProgram PrefixPrograms

noncomputable def equivSplitter {α β : Type} (c : BinaryEncoding.Codec α)
    (e : β ≃ α) (p : Splitter c) : Splitter (BinaryEncoding.equiv c e) :=
  (p.precompose (fun x : β × List Bool => (e x.1, x.2))).result (by intro x; rfl)

noncomputable def pairInput {α β : Type} (c : BinaryEncoding.Codec α)
    (d : BinaryEncoding.Codec β) (p : Splitter c) :
    Procedure (BinaryEncoding.pair c d).encode (prodCode c.encode d.encode) id :=
  (p.precompose (fun x : α × β => (x.1, d.encode x.2))).result (by intro x; rfl)

noncomputable def rationalSplitter : Splitter binaryRationalCodec :=
  equivSplitter _ binaryRationalEquiv
    (PrefixPrograms.pair BinaryEncoding.integer BinaryEncoding.natural integer natural)

noncomputable def coordinateSplitter : Splitter (BinaryEncoding.pair BinaryEncoding.integer BinaryEncoding.integer) :=
  PrefixPrograms.pair _ _ integer integer

noncomputable def edgeSplitter : Splitter binaryHeisenbergEdgeCodec :=
  equivSplitter _ binaryHeisenbergEdgeEquiv
    (PrefixPrograms.pair _ _ natural
      (PrefixPrograms.pair _ _ natural rationalSplitter))

noncomputable def coordinateListSplitter : Splitter coordinateListCodec :=
  PrefixListPrograms.listSplitter coordinateCodec coordinateSplitter (0, 0) coordinate_length_pos

noncomputable def edgeListSplitter : Splitter edgeListCodec :=
  PrefixListPrograms.listSplitter binaryHeisenbergEdgeCodec edgeSplitter ⟨0, 0, ⟨0, 1⟩⟩ edge_length_pos

/-- The rational denominator is parsed and reduced by the actual gcd-based
machine routine, so noncanonical input fractions are handled correctly. -/
noncomputable def rationalValue : Procedure binaryRationalCodec.encode ratCode BinaryRational.value := by
  let p := (pairInput BinaryEncoding.integer BinaryEncoding.natural integer).precompose
    binaryRationalEquiv
  let numerator : Procedure binaryRationalCodec.encode intCode BinaryRational.numerator :=
    EncodingPrograms.integerInput.comp ((Procedure.first _ _).comp p)
  let denominator : Procedure binaryRationalCodec.encode Nat.bits BinaryRational.denominator :=
    EncodingPrograms.naturalInput.comp ((Procedure.second _ _).comp p)
  exact (Procedure.makeRat.comp (numerator.pair denominator)).congrFun (by
    intro q
    exact Rat.mkRat_eq_div q.numerator q.denominator)

noncomputable def sourceTuple : Procedure binaryHeisenbergCodec.encode
    (prodCode coordinateListCodec.encode sourceTailCodec.encode) binaryHeisenbergEquiv :=
  (pairInput coordinateListCodec sourceTailCodec coordinateListSplitter).precompose binaryHeisenbergEquiv

noncomputable def coordinatesRaw : Procedure binaryHeisenbergCodec.encode coordinateListCodec.encode
    BinaryHeisenberg.coordinate := (Procedure.first _ _).comp sourceTuple

noncomputable def tailRaw : Procedure binaryHeisenbergCodec.encode sourceTailCodec.encode
    (fun d => (d.edges, d.lower, d.upper)) := (Procedure.second _ _).comp sourceTuple

noncomputable def tailTuple : Procedure binaryHeisenbergCodec.encode
    (prodCode edgeListCodec.encode thresholdCodec.encode) (fun d => (d.edges, d.lower, d.upper)) :=
  (pairInput edgeListCodec thresholdCodec edgeListSplitter).comp tailRaw

noncomputable def thresholdsRaw : Procedure binaryHeisenbergCodec.encode thresholdCodec.encode
    (fun d => (d.lower, d.upper)) := (Procedure.second _ _).comp tailTuple

noncomputable def thresholdTuple : Procedure binaryHeisenbergCodec.encode
    (prodCode binaryRationalCodec.encode binaryRationalCodec.encode) (fun d => (d.lower, d.upper)) :=
  (pairInput binaryRationalCodec binaryRationalCodec rationalSplitter).comp thresholdsRaw

noncomputable def coordinates : Procedure binaryHeisenbergCodec.encode
    (listCode coordinateCodec.encode) BinaryHeisenberg.coordinate :=
  (PrefixListPrograms.listInput coordinateCodec coordinateSplitter (0, 0) coordinate_length_pos).comp coordinatesRaw

noncomputable def lower : Procedure binaryHeisenbergCodec.encode ratCode
    (fun d => d.lower.value) := rationalValue.comp ((Procedure.first _ _).comp thresholdTuple)

end ContinuumCoulomb.SourcePrograms

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_NuclearCoordinateOutput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Serialization of computed rational triples into the actual nuclear
position codec. The canonical numerator and positive denominator are kept
exactly; no real-coordinate oracle is used. -/

namespace ContinuumCoulomb.NuclearCoordinateOutput
open ExactQuantumFactoring.BitStackProgram
open CappedKernelProgram (Triple tripleCode)

def position (q : Triple) : BinaryPosition :=
  ⟨rational q.1,rational q.2.1,rational q.2.2⟩

noncomputable opaque rationalProgram : Procedure ratCode binaryRationalCodec.encode rational := by
  let num := EncodingPrograms.integerOutput.comp Procedure.ratNum
  let den := EncodingPrograms.naturalOutput.comp Procedure.ratDen
  let p := (EncodingPrograms.appendPair BinaryEncoding.integer BinaryEncoding.natural).comp (num.pair den)
  exact p.result (by intro q; rfl)

noncomputable opaque positionProgram : Procedure tripleCode binaryPositionCodec.encode position := by
  let x := rationalProgram.comp EulerRegisters.tripleFirstProgram
  let y := rationalProgram.comp EulerRegisters.tripleSecondProgram
  let z := rationalProgram.comp EulerRegisters.tripleThirdProgram
  let yz := (EncodingPrograms.appendPair binaryRationalCodec binaryRationalCodec).comp (y.pair z)
  let p := (EncodingPrograms.appendPair binaryRationalCodec
    (BinaryEncoding.pair binaryRationalCodec binaryRationalCodec)).comp (x.pair yz)
  exact p.result (by intro q; rfl)

def positions (qs : List Triple) : List BinaryPosition := qs.map position

noncomputable opaque positionsProgram : Procedure (listCode tripleCode)
    (BinaryEncoding.list binaryPositionCodec).encode positions :=
  (PrefixListPrograms.listOutput binaryPositionCodec UnitBinaryProgram.zeroPosition).comp
    (Procedure.listMap (0,(0,0)) UnitBinaryProgram.zeroPosition positionProgram)

end ContinuumCoulomb.NuclearCoordinateOutput

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_RationalTripleQuadrature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Three-coordinate rational cubature, using the already proved literal
one- and two-coordinate summation programs. -/

namespace ContinuumCoulomb.RationalTripleQuadrature
open ExactQuantumFactoring.BitStackProgram

variable {E : Type}

noncomputable opaque augmentProgram (ce : E → List Bool) :
    Procedure (prodCode (RationalQuadratureProgram.inputCode ce) ratCode)
      (RationalQuadratureProgram.inputCode (prodCode ce ratCode))
      (fun x => augment x.1 x.2) := by
  let x := Procedure.first (RationalQuadratureProgram.inputCode ce) ratCode
  let a := Procedure.second (RationalQuadratureProgram.inputCode ce) ratCode
  let n := (Procedure.first unaryCode (RationalQuadratureProgram.environmentCode ce)).comp x
  let env := (Procedure.second unaryCode (RationalQuadratureProgram.environmentCode ce)).comp x
  let e := (Procedure.first ce (prodCode ratCode ratCode)).comp env
  let mesh := (Procedure.second ce (prodCode ratCode ratCode)).comp env
  exact n.pair ((e.pair a).pair mesh)

noncomputable opaque rememberProgram (ce : E → List Bool) :
    Procedure (RationalQuadratureProgram.inputCode ce)
      (RationalQuadratureProgram.inputCode (RationalQuadratureProgram.inputCode ce)) remember := by
  let n := Procedure.first unaryCode (RationalQuadratureProgram.environmentCode ce)
  let env := Procedure.second unaryCode (RationalQuadratureProgram.environmentCode ce)
  let mesh := (Procedure.second ce (prodCode ratCode ratCode)).comp env
  exact n.pair ((Procedure.identity (RationalQuadratureProgram.inputCode ce)).pair mesh)

noncomputable opaque outerProgram (ce : E → List Bool) (f : Evaluator E)
    (p : Procedure (prodCode (prodCode (prodCode ce ratCode) ratCode) ratCode)
      ratCode (fun x => inner f x.1.1 x.1.2 x.2)) :
    Procedure (prodCode (RationalQuadratureProgram.inputCode ce) ratCode) ratCode
      (fun x => outer f x.1 x.2) :=
  (RationalRectangleProgram.program (prodCode ce ratCode) (inner f) p).comp (augmentProgram ce)

noncomputable opaque program (ce : E → List Bool) (f : Evaluator E)
    (p : Procedure (prodCode (prodCode (prodCode ce ratCode) ratCode) ratCode)
      ratCode (fun x => inner f x.1.1 x.1.2 x.2)) :
    Procedure (RationalQuadratureProgram.inputCode ce) ratCode (value f) :=
  (RationalQuadratureProgram.program (RationalQuadratureProgram.inputCode ce) (outer f)
    (outerProgram ce f p)).comp (rememberProgram ce)

end ContinuumCoulomb.RationalTripleQuadrature

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabOriginValue
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual rational cubature of the scalar slab shift. -/

noncomputable section
namespace ContinuumCoulomb.SlabOriginValue
open ExactQuantumFactoring.BitStackProgram

def parameterCode : Parameters → List Bool :=
  prodCode (prodCode unaryCode ratCode) (prodCode ratCode ratCode)

noncomputable opaque sampleInputProgram :
    Procedure (prodCode (prodCode (prodCode parameterCode ratCode) ratCode) ratCode)
      CappedKernelProgram.inputCode
      (fun q => (q.1.1.1.1,(q.1.1.1.2.1*q.1.1.2,
        (q.1.1.1.2.1*q.1.2,q.1.1.1.2.2*q.2)))) := by
  let xyz := Procedure.first (prodCode (prodCode parameterCode ratCode) ratCode) ratCode
  let ex := (Procedure.first (prodCode parameterCode ratCode) ratCode).comp xyz
  let e := (Procedure.first parameterCode ratCode).comp ex
  let x := (Procedure.second parameterCode ratCode).comp ex
  let y := (Procedure.second (prodCode parameterCode ratCode) ratCode).comp xyz
  let z := Procedure.second (prodCode (prodCode parameterCode ratCode) ratCode) ratCode
  let head := (Procedure.first (prodCode unaryCode ratCode) (prodCode ratCode ratCode)).comp e
  let shape := (Procedure.second (prodCode unaryCode ratCode) (prodCode ratCode ratCode)).comp e
  let H := (Procedure.first ratCode ratCode).comp shape
  let S := (Procedure.second ratCode ratCode).comp shape
  let hx := Procedure.ratMul.comp (H.pair x)
  let hy := Procedure.ratMul.comp (H.pair y)
  let sz := Procedure.ratMul.comp (S.pair z)
  exact head.pair (hx.pair (hy.pair sz))

noncomputable opaque sampleProgram :
    Procedure (prodCode (prodCode (prodCode parameterCode ratCode) ratCode) ratCode)
      ratCode (fun q => sample q.1.1.1 q.1.1.2 q.1.2 q.2) :=
  CappedKernelProgram.program.comp sampleInputProgram

noncomputable opaque program (rho : ℚ) :
    Procedure (RationalQuadratureProgram.inputCode parameterCode) ratCode (value rho) := by
  let env := Procedure.second unaryCode (RationalQuadratureProgram.environmentCode parameterCode)
  let params := (Procedure.first parameterCode (prodCode ratCode ratCode)).comp env
  let shape := (Procedure.second (prodCode unaryCode ratCode) (prodCode ratCode ratCode)).comp params
  let H := (Procedure.first ratCode ratCode).comp shape
  let S := (Procedure.second ratCode ratCode).comp shape
  let hsq := Procedure.ratMul.comp (H.pair H)
  let c := Procedure.constant (RationalQuadratureProgram.inputCode parameterCode) ratCode (-rho)
  let factor := Procedure.ratMul.comp ((Procedure.ratMul.comp (c.pair hsq)).pair S)
  let quad := RationalTripleQuadrature.program parameterCode sample sampleProgram
  exact (Procedure.ratMul.comp (factor.pair quad)).congrFun (by intro x; simp [value,pow_two])

end ContinuumCoulomb.SlabOriginValue

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_SlabOriginProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal polynomial-time program for the slab origin potential. -/

namespace ContinuumCoulomb.SlabOriginSchedule
open ExactQuantumFactoring.BitStackProgram

def inputCode : Input → List Bool := prodCode unaryCode (prodCode unaryCode unaryCode)

noncomputable opaque precisionProgram : Procedure inputCode unaryCode Prod.fst :=
  Procedure.first _ _
noncomputable opaque boxProgram : Procedure inputCode (prodCode unaryCode unaryCode) Prod.snd :=
  Procedure.second _ _
noncomputable opaque horizontalProgram : Procedure inputCode unaryCode (fun x => x.2.1) :=
  (Procedure.first _ _).comp boxProgram
noncomputable opaque verticalProgram : Procedure inputCode unaryCode (fun x => x.2.2) :=
  (Procedure.second _ _).comp boxProgram

noncomputable opaque capDenominatorProgram (rho : ℕ) : Procedure inputCode unaryCode
    (fun x => capDenominator rho x.1) :=
  (ResolventSchedule.mulProgram.comp
    ((Procedure.constant inputCode unaryCode (16*(rho+1))).pair
      (Procedure.unarySuccessor.comp precisionProgram))).congrFun (by intro x; rfl)

noncomputable opaque boxWeightProgram (rho : ℕ) : Procedure inputCode unaryCode
    (fun x => boxWeight rho x.2.1 x.2.2) := by
  let hp := Procedure.unarySuccessor.comp horizontalProgram
  let hs := ResolventSchedule.squareProgram.comp hp
  let sp := Procedure.unarySuccessor.comp verticalProgram
  let total := Procedure.unarySuccessor.comp
    (ResolventSchedule.addProgram.comp (horizontalProgram.pair verticalProgram))
  let first := ResolventSchedule.mulProgram.comp
    ((Procedure.constant inputCode unaryCode (rho+1)).pair hs)
  let second := ResolventSchedule.mulProgram.comp (first.pair sp)
  exact (ResolventSchedule.mulProgram.comp (second.pair total)).congrFun (by intro x; rfl)

noncomputable opaque countProgram (rho : ℕ) : Procedure inputCode unaryCode (count rho) := by
  let first := ResolventSchedule.mulProgram.comp
    ((Procedure.constant inputCode unaryCode 128).pair (boxWeightProgram rho))
  let second := ResolventSchedule.mulProgram.comp
    (first.pair (Procedure.unarySuccessor.comp precisionProgram))
  let sq := ResolventSchedule.squareProgram.comp (capDenominatorProgram rho)
  exact (ResolventSchedule.mulProgram.comp (second.pair sq)).congrFun (by intro x; rfl)

end ContinuumCoulomb.SlabOriginSchedule

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_SlabBoxProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial evaluation of rational-width slabs and of the exact centered
mesh half-widths. Bounds remain unary; the actual widths remain rational. -/

namespace ContinuumCoulomb.SlabBoxSchedule
open ExactQuantumFactoring.BitStackProgram

def inputCode : Input → List Bool :=
  prodCode SlabOriginSchedule.inputCode (prodCode ratCode ratCode)

noncomputable opaque boundsProgram : Procedure inputCode SlabOriginSchedule.inputCode Prod.fst :=
  Procedure.first _ _
noncomputable opaque widthsProgram : Procedure inputCode (prodCode ratCode ratCode) Prod.snd :=
  Procedure.second _ _

noncomputable opaque inputProgram (rho : ℕ) : Procedure inputCode
    (RationalQuadratureProgram.inputCode SlabOriginValue.parameterCode) (input rho) := by
  let n := (SlabOriginSchedule.countProgram rho).comp boundsProgram
  let nq := Procedure.natToRat.comp (Procedure.unaryToBits.comp n)
  let q := Procedure.natToRat.comp (Procedure.unaryToBits.comp
    ((SlabOriginSchedule.capDenominatorProgram rho).comp boundsProgram))
  let cap := Procedure.ratInv.comp q
  let step := Procedure.ratDiv.comp ((Procedure.constant inputCode ratCode (2:ℚ)).pair nq)
  exact n.pair (((n.pair cap).pair widthsProgram).pair
    ((Procedure.constant inputCode ratCode (-1:ℚ)).pair step))

noncomputable opaque program (rho : ℕ) : Procedure inputCode ratCode (value rho) :=
  (SlabOriginValue.program (rho:ℚ)).comp (inputProgram rho)

def centeredCode : (ℕ×(ℕ×(ℕ×ℕ))) → List Bool :=
  prodCode unaryCode (prodCode unaryCode (prodCode unaryCode unaryCode))

noncomputable opaque centeredInputProgram : Procedure centeredCode inputCode
    (fun x => centered x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  let p := Procedure.first unaryCode (prodCode unaryCode (prodCode unaryCode unaryCode))
  let tail := Procedure.second unaryCode (prodCode unaryCode (prodCode unaryCode unaryCode))
  let n := (Procedure.first unaryCode (prodCode unaryCode unaryCode)).comp tail
  let box := (Procedure.second unaryCode (prodCode unaryCode unaryCode)).comp tail
  let h := (Procedure.first unaryCode unaryCode).comp box
  let s := (Procedure.second unaryCode unaryCode).comp box
  let nq := Procedure.natToRat.comp (Procedure.unaryToBits.comp n)
  let hq := Procedure.natToRat.comp (Procedure.unaryToBits.comp h)
  let sq := Procedure.natToRat.comp (Procedure.unaryToBits.comp s)
  let half := Procedure.constant centeredCode ratCode (1/2:ℚ)
  let hw := Procedure.ratDiv.comp ((Procedure.ratAdd.comp (hq.pair half)).pair nq)
  let sw := Procedure.ratDiv.comp ((Procedure.ratAdd.comp (sq.pair half)).pair nq)
  exact (p.pair ((Procedure.unarySuccessor.comp h).pair
    (Procedure.unarySuccessor.comp s))).pair (hw.pair sw)

noncomputable opaque centeredProgram (rho : ℕ) : Procedure centeredCode ratCode
    (fun x => value rho (centered x.1 x.2.1 x.2.2.1 x.2.2.2)) :=
  (program rho).comp centeredInputProgram

end ContinuumCoulomb.SlabBoxSchedule

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CenteredPhysicalThreshold
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical threshold reference for the exact half-cell boundary of the
centered grid. The finite threshold is scaled by lambda and the true rational
slab reference by lambda squared times the electron count. -/

noncomputable section
namespace ContinuumCoulomb.CenteredPhysicalThreshold

def actualReference (rho : ℕ) (g : Geometry) : ℝ :=
  slabPotential (rho:ℝ) (SlabBoxSchedule.centeredWidth g.2.1 g.1:ℝ)
    (SlabBoxSchedule.centeredWidth g.2.2 g.1:ℝ) 0+(GaussianFrequency.frequency rho-1)/2

def actualOffset (rho : ℕ) (x : Input) : ℝ :=
  (amplification rho x.1.1:ℝ)^2*(x.2.1:ℝ)*actualReference rho x.1

end ContinuumCoulomb.CenteredPhysicalThreshold

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_CenteredPhysicalThresholdProgram
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial-time arithmetic for the complete physical threshold pair. -/

namespace ContinuumCoulomb.CenteredPhysicalThreshold
open ExactQuantumFactoring.BitStackProgram

noncomputable opaque endpointsProgram : Procedure inputCode (prodCode ratCode ratCode)
    (fun x => x.2.2.2) := (Procedure.second _ _).comp restProgram

noncomputable opaque precisionProgram : Procedure inputCode unaryCode precision := by
  let c8 := Procedure.constant inputCode unaryCode 8
  let scale := ResolventSchedule.mulProgram.comp (c8.pair meshCubeProgram)
  let sq := ResolventSchedule.squareProgram.comp (Procedure.unarySuccessor.comp scale)
  let first := ResolventSchedule.mulProgram.comp (c8.pair sq)
  let second := ResolventSchedule.mulProgram.comp
    (first.pair (Procedure.unarySuccessor.comp electronsProgram))
  exact (ResolventSchedule.mulProgram.comp
    (second.pair (Procedure.unarySuccessor.comp errorProgram))).congrFun (by intro x; rfl)

noncomputable opaque amplificationProgram (rho : ℕ) : Procedure inputCode ratCode
    (fun x => amplification rho x.1.1) := by
  let cube := Procedure.natToRat.comp (Procedure.unaryToBits.comp meshCubeProgram)
  let num := Procedure.ratMul.comp ((Procedure.constant inputCode ratCode 8).pair cube)
  exact (Procedure.ratDiv.comp
    (num.pair (Procedure.constant inputCode ratCode (rho:ℚ)))).congrFun
      (by intro x; simp [amplification])

noncomputable opaque referenceProgram (rho : ℕ) : Procedure inputCode ratCode (reference rho) := by
  let slab := (SlabBoxSchedule.centeredProgram rho).comp (precisionProgram.pair geometryProgram)
  let freq := (GaussianFrequency.program rho).comp precisionProgram
  let sub := Procedure.ratSub.comp (freq.pair (Procedure.constant inputCode ratCode 1))
  let e0 := Procedure.ratDiv.comp (sub.pair (Procedure.constant inputCode ratCode 2))
  exact (Procedure.ratAdd.comp (slab.pair e0)).congrFun (by intro x; rfl)

noncomputable opaque offsetProgram (rho : ℕ) : Procedure inputCode ratCode (offset rho) := by
  let lambda := amplificationProgram rho
  let square := Procedure.ratMul.comp (lambda.pair lambda)
  let n := Procedure.natToRat.comp (Procedure.unaryToBits.comp electronsProgram)
  let factor := Procedure.ratMul.comp (square.pair n)
  exact (Procedure.ratMul.comp (factor.pair (referenceProgram rho))).congrFun
    (by intro x; simp only [offset,pow_two,Function.comp_apply,id_eq])

noncomputable opaque program (rho : ℕ) : Procedure inputCode (prodCode ratCode ratCode) (value rho) := by
  let endpoints := endpointsProgram
  let a := (Procedure.first ratCode ratCode).comp endpoints
  let b := (Procedure.second ratCode ratCode).comp endpoints
  let lower := Procedure.ratAdd.comp
    ((offsetProgram rho).pair (Procedure.ratMul.comp ((amplificationProgram rho).pair a)))
  let upper := Procedure.ratAdd.comp
    ((offsetProgram rho).pair (Procedure.ratMul.comp ((amplificationProgram rho).pair b)))
  exact lower.pair upper

end ContinuumCoulomb.CenteredPhysicalThreshold

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CoulombPairSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual scalar direct-interaction offset is one half of the
ordered off-diagonal Coulomb sum. The finite list evaluator excludes only
identical coordinates; injectivity identifies that test with the diagonal. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb.CoulombPairSum

def exactTotal (freq : ℝ) {m : ℕ} (u : Fin m → Point) : ℝ :=
  (1/2:ℝ)*∑ i, ∑ j, if i=j then 0 else
    localizedCoulombCoeff freq (PlanarForcingProgram.position (u i))
      (PlanarForcingProgram.position (u j))

end ContinuumCoulomb.CoulombPairSum

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_CoulombPairSumProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The direct-interaction scalar uses two literal finite list traversals;
its precision increases only polynomially with the number of sites. -/

namespace ContinuumCoulomb.CoulombPairSum
open ExactQuantumFactoring.BitStackProgram

noncomputable opaque offsiteProgram (rho : ℕ) :
    Procedure CoulombPairEvaluation.inputCode ratCode
      (fun x => offsite rho x.1 x.2.1 x.2.2) := by
  let pairs := Procedure.second unaryCode CoulombPairEvaluation.pairCode
  let dist := CoulombPairEvaluation.squaredDistanceProgram.comp pairs
  let test := Procedure.binaryZero.comp (Procedure.intAbs.comp (Procedure.ratNum.comp dist))
  let zero := Procedure.constant CoulombPairEvaluation.inputCode ratCode (0:ℚ)
  exact (Procedure.conditional test zero (CoulombPairEvaluation.program rho)).congrFun (by
    intro x
    simp only [Function.comp_apply,decide_eq_true_eq,Int.natAbs_eq_zero,Rat.num_eq_zero,offsite])

noncomputable opaque offsiteEnvironmentProgram (rho : ℕ) :
    Procedure (prodCode (prodCode unaryCode pointCode) pointCode) ratCode
      (fun x => offsite rho x.1.1 x.1.2 x.2) := by
  let env := Procedure.first (prodCode unaryCode pointCode) pointCode
  let p := (Procedure.first unaryCode pointCode).comp env
  let a := (Procedure.second unaryCode pointCode).comp env
  let b := Procedure.second (prodCode unaryCode pointCode) pointCode
  exact (offsiteProgram rho).comp (p.pair (a.pair b))

noncomputable opaque rowProgram (rho : ℕ) : Procedure rowCode ratCode
    (fun x => row rho x.1 x.2.1 x.2.2) := by
  let p := Procedure.first unaryCode (prodCode pointCode (listCode pointCode))
  let tail := Procedure.second unaryCode (prodCode pointCode (listCode pointCode))
  let a := (Procedure.first pointCode (listCode pointCode)).comp tail
  let sites := (Procedure.second pointCode (listCode pointCode)).comp tail
  let mapped := (Procedure.listMapWith (ea := prodCode unaryCode pointCode)
    (eb := pointCode) (ec := ratCode)
    (f := fun env b => offsite rho env.1 env.2 b) (0,0) 0
    (offsiteEnvironmentProgram rho)).comp ((p.pair a).pair sites)
  exact (RationalSumProgram.sumProgram.comp mapped).congrFun (by intro x; rfl)

noncomputable opaque rowEnvironmentProgram (rho : ℕ) :
    Procedure (prodCode inputCode pointCode) ratCode (fun x => row rho x.1.1 x.2 x.1.2) := by
  let env := Procedure.first inputCode pointCode
  let p := (Procedure.first unaryCode (listCode pointCode)).comp env
  let sites := (Procedure.second unaryCode (listCode pointCode)).comp env
  let a := Procedure.second inputCode pointCode
  exact (rowProgram rho).comp (p.pair (a.pair sites))

noncomputable opaque totalProgram (rho : ℕ) : Procedure inputCode ratCode
    (fun x => total rho x.1 x.2) := by
  let sites := Procedure.second unaryCode (listCode pointCode)
  let mapped := (Procedure.listMapWith (ea := inputCode) (eb := pointCode) (ec := ratCode)
    (f := fun env a => row rho env.1 a env.2) (0,0) 0
    (rowEnvironmentProgram rho)).comp ((Procedure.identity inputCode).pair sites)
  let sum := RationalSumProgram.sumProgram.comp mapped
  exact (Procedure.ratDiv.comp (sum.pair (Procedure.constant inputCode ratCode 2))).congrFun
    (by intro x; rfl)

noncomputable opaque program (rho : ℕ) : Procedure inputCode ratCode (value rho) := by
  let p := (totalProgram rho).comp argumentProgram
  exact p.congrFun (by intro x; rfl)

end ContinuumCoulomb.CoulombPairSum

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_AffinePhysicalThreshold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete scalar shift in the unit-charge construction. Input endpoints
already contain the exact mediator offset. The remaining finite shift is the
sum of edge weights and the off-site Coulomb energy; only the latter and the
one-particle reference require numerical approximation. -/

noncomputable section
namespace ContinuumCoulomb.AffinePhysicalThreshold

def exactFinite (x : Input) (v : ℝ) : ℝ×ℝ :=
  ((x.2.1:ℝ)^2*((x.1.2.2.2.1:ℝ)-(x.2.2.2.sum:ℝ))-v,
   (x.2.1:ℝ)^2*((x.1.2.2.2.2:ℝ)-(x.2.2.2.sum:ℝ))-v)

def exactValue (rho : ℕ) (x : Input) (v : ℝ) : ℝ×ℝ :=
  (CenteredPhysicalThreshold.actualOffset rho x.1+
      (CenteredPhysicalThreshold.amplification rho x.1.1.1:ℝ)*(exactFinite x v).1,
   CenteredPhysicalThreshold.actualOffset rho x.1+
      (CenteredPhysicalThreshold.amplification rho x.1.1.1:ℝ)*(exactFinite x v).2)

end ContinuumCoulomb.AffinePhysicalThreshold

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_AffinePhysicalThresholdProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal polynomial-time evaluation of the complete affine threshold shift.
Every precision and loop bound is computed in unary from polynomial metadata. -/

namespace ContinuumCoulomb.AffinePhysicalThreshold
open ExactQuantumFactoring.BitStackProgram

noncomputable opaque tauProgram : Procedure inputCode ratCode (fun x => x.2.1) :=
  (Procedure.first _ _).comp dataProgram
noncomputable opaque weightsProgram : Procedure inputCode (listCode ratCode)
    (fun x => x.2.2.2) := (Procedure.second _ _).comp listsProgram
noncomputable opaque geometryProgram : Procedure inputCode CenteredPhysicalThreshold.geometryCode
    (fun x => x.1.1) := CenteredPhysicalThreshold.geometryProgram.comp numbersProgram

noncomputable opaque pairProgram (rho : ℕ) : Procedure inputCode ratCode (pairValue rho) :=
  (CoulombPairSum.program rho).comp (pairPrecisionProgram.pair sitesProgram)

noncomputable opaque finiteProgram (rho : ℕ) : Procedure inputCode (prodCode ratCode ratCode)
    (finiteValue rho) := by
  let bounds := CenteredPhysicalThreshold.endpointsProgram.comp numbersProgram
  let lower := (Procedure.first ratCode ratCode).comp bounds
  let upper := (Procedure.second ratCode ratCode).comp bounds
  let sum := RationalSumProgram.sumProgram.comp weightsProgram
  let tauSquared := Procedure.ratMul.comp (tauProgram.pair tauProgram)
  let lowerShift := Procedure.ratSub.comp (lower.pair sum)
  let upperShift := Procedure.ratSub.comp (upper.pair sum)
  let lowerScale := Procedure.ratMul.comp (tauSquared.pair lowerShift)
  let upperScale := Procedure.ratMul.comp (tauSquared.pair upperShift)
  exact ((Procedure.ratSub.comp (lowerScale.pair (pairProgram rho))).pair
    (Procedure.ratSub.comp (upperScale.pair (pairProgram rho)))).congrFun
      (by intro x; simp only [finiteValue,pow_two,Function.comp_apply])

noncomputable opaque argumentProgram (rho : ℕ) :
    Procedure inputCode CenteredPhysicalThreshold.inputCode (argument rho) :=
  geometryProgram.pair (electronsProgram.pair (precisionProgram.pair (finiteProgram rho)))

noncomputable opaque program (rho : ℕ) : Procedure inputCode (prodCode ratCode ratCode) (value rho) :=
  (CenteredPhysicalThreshold.program rho).comp (argumentProgram rho)

end ContinuumCoulomb.AffinePhysicalThreshold

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CenteredGaussLabels
attribute [-simp] _root_.OAI.ContinuumCoulomb.CenteredGaussLabels.decode_index _root_.OAI.ContinuumCoulomb.CenteredGaussLabels.index_decode _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete duplicate-free list of all eight Gauss labels in each cell
of the centered rectangular grid, with the exact polynomial count. -/

namespace ContinuumCoulomb.CenteredGaussLabels
open EulerRegisters (Registers)
open RationalGaussNodes (Signs)

def cells (r : Radii) : List Registers :=
  integers r.1 ×ˢ (integers r.2.1 ×ˢ integers r.2.2)
def labels (r : Radii) : List (Registers×Signs) := cells r ×ˢ signs
def radiiVector (r : Radii) : Fin 3 → ℕ := ![r.1,r.2.1,r.2.2]

theorem labels_nodup (r : Radii) : (labels r).Nodup := by
  apply List.Nodup.product
  · exact (integers_nodup r.1).product ((integers_nodup r.2.1).product (integers_nodup r.2.2))
  · decide

theorem labels_length (r : Radii) :
    (labels r).length = 8*((2*r.1+1)*(2*r.2.1+1)*(2*r.2.2+1)) := by
  simp only [labels,cells,signs,integers,List.length_product,List.length_map,List.length_range]
  simp only [List.length_cons,List.length_nil]
  ring

theorem mem_labels (r : Radii) (l : Registers×Signs) :
    l ∈ labels r ↔ (RationalGaussNodes.index l.1 l.2).1 ∈ centeredGridIndices (radiiVector r) := by
  rcases l with ⟨⟨a,b,c⟩,s⟩
  rw [labels,List.mem_product]
  simp only [signs_mem,and_true,cells,List.mem_product,mem_integers]
  rw [mem_centeredGridIndices]
  constructor
  · rintro ⟨h0,h1,h2⟩ i
    fin_cases i
    · simpa [RationalGaussNodes.index,radiiVector] using h0
    · simpa [RationalGaussNodes.index,radiiVector] using h1
    · simpa [RationalGaussNodes.index,radiiVector] using h2
  · intro h
    exact ⟨by simpa [RationalGaussNodes.index,radiiVector] using h 0,
      by simpa [RationalGaussNodes.index,radiiVector] using h 1,
      by simpa [RationalGaussNodes.index,radiiVector] using h 2⟩

end ContinuumCoulomb.CenteredGaussLabels

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_CenteredGaussProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal polynomial generation of the complete rectangular Gauss-label
list. The three integer radii are unary, so the cubic number of output cells
is polynomial in the encoded input size. -/

namespace ContinuumCoulomb.CenteredGaussLabels
open ExactQuantumFactoring.BitStackProgram

theorem flatten_code_bound {α : Type} (ea : α → List Bool) (xs : List (List α)) :
    (listCode ea xs.flatten).length ≤ (listCode (listCode ea) xs).length := by
  induction xs with
  | nil => exact le_rfl
  | cons x xs ih =>
    have h := listCode_length_append ea x xs.flatten
    simp only [List.flatten_cons,listCode_length_cons]
    omega

noncomputable def flattenProgram {α : Type} (ea : α → List Bool) (d : α) :
    Procedure (listCode (listCode ea)) (listCode ea) List.flatten := by
  let step := (Procedure.listAppend ea d).comp (Procedure.swap (listCode ea) (listCode ea))
  let p := Procedure.foldList [] step Polynomial.X (by
    intro xs ys i
    change (listCode ea ((xs.take i).foldl (fun ys x => ys++x) ys)).length ≤ _
    rw [fold_append]
    have h := listCode_length_append ea ys (xs.take i).flatten
    have hf := flatten_code_bound ea (xs.take i)
    have ht := listCode_length_take_le (listCode ea) i xs
    simp only [Polynomial.eval_X]
    omega)
  exact (p.comp ((Procedure.identity (listCode (listCode ea))).pair
    (Procedure.constant (listCode (listCode ea)) (listCode ea) []))).congrFun (by
      intro xs
      change xs.foldl (fun ys x => ys++x) [] = xs.flatten
      simpa only [List.nil_append] using fold_append xs [])

noncomputable def productProgram {α β : Type} (ea : α → List Bool) (eb : β → List Bool)
    (a : α) (b : β) : Procedure (prodCode (listCode ea) (listCode eb))
      (listCode (prodCode ea eb)) (fun x => x.1 ×ˢ x.2) := by
  let row := (Procedure.listMapWith (ea := ea) (eb := eb) (ec := prodCode ea eb)
    (f := fun a b => (a,b)) b (a,b) (Procedure.identity (prodCode ea eb))).comp
      (Procedure.swap (listCode eb) ea)
  let rows := (Procedure.listMapWith (ea := listCode eb) (eb := ea)
    (ec := listCode (prodCode ea eb)) (f := fun ys a => ys.map (fun b => (a,b))) a [] row).comp
      (Procedure.swap (listCode ea) (listCode eb))
  exact ((flattenProgram (prodCode ea eb) (a,b)).comp rows).congrFun (by intro x; rfl)

noncomputable opaque integerStep : Procedure (prodCode unaryCode unaryCode) intCode
    (fun x => (x.1:ℤ)-(x.2:ℤ)) := by
  let cast := Procedure.natToInt.comp Procedure.unaryToBits
  exact Procedure.intSub.comp
    ((cast.comp (Procedure.first unaryCode unaryCode)).pair
      (cast.comp (Procedure.second unaryCode unaryCode)))

noncomputable opaque integersProgram : Procedure unaryCode (listCode intCode) integers := by
  let count := Procedure.unarySuccessor.comp (Procedure.unaryMul.comp
    ((Procedure.constant unaryCode unaryCode 2).pair (Procedure.identity unaryCode)))
  exact ((Procedure.tabulate (ea := unaryCode) (eb := intCode)
    (f := fun R i => (i:ℤ)-(R:ℤ)) 0 integerStep).comp
      (count.pair (Procedure.identity unaryCode))).congrFun (by intro R; rfl)

noncomputable opaque firstRadiusProgram : Procedure radiiCode unaryCode Prod.fst :=
  Procedure.first _ _
noncomputable opaque tailRadiiProgram : Procedure radiiCode (prodCode unaryCode unaryCode) Prod.snd :=
  Procedure.second _ _
noncomputable opaque secondRadiusProgram : Procedure radiiCode unaryCode (fun r => r.2.1) :=
  (Procedure.first _ _).comp tailRadiiProgram
noncomputable opaque thirdRadiusProgram : Procedure radiiCode unaryCode (fun r => r.2.2) :=
  (Procedure.second _ _).comp tailRadiiProgram

noncomputable opaque cellsProgram : Procedure radiiCode (listCode EulerRegisters.registersCode) cells := by
  let yz := (productProgram intCode intCode (0:ℤ) (0:ℤ)).comp
    ((integersProgram.comp secondRadiusProgram).pair (integersProgram.comp thirdRadiusProgram))
  exact (productProgram intCode (prodCode intCode intCode) (0:ℤ) (0,0)).comp
    ((integersProgram.comp firstRadiusProgram).pair yz)

noncomputable opaque labelsProgram : Procedure radiiCode (listCode TransformedGauss.labelCode) labels :=
  (productProgram EulerRegisters.registersCode RationalGaussNodes.signsCode (0,(0,0))
    (false,(false,false))).comp
      (cellsProgram.pair (Procedure.constant radiiCode (listCode RationalGaussNodes.signsCode) signs))

end ContinuumCoulomb.CenteredGaussLabels

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_CenteredNuclearProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete finite rational nucleus list, generated from the actual
rectangular cell bounds, numerically transported, and serialized using the
continuum promise's own position codec. -/

open scoped NNReal
namespace ContinuumCoulomb.CenteredNuclearProgram
open ExactQuantumFactoring.BitStackProgram

noncomputable opaque argumentsProgram : Procedure inputCode TransformedGauss.listInputCode
    (fun x => (x.1,CenteredGaussLabels.labels x.2)) :=
  (Procedure.first _ _).pair (CenteredGaussLabels.labelsProgram.comp (Procedure.second _ _))

end ContinuumCoulomb.CenteredNuclearProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_PhysicalNuclearProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical nuclear coordinates for h=1/N. The exact rational factor is
1/λ=rho/(8N^3), matching the manuscript's y=λx convention. -/

namespace ContinuumCoulomb.PhysicalNuclearProgram
open ExactQuantumFactoring.BitStackProgram
open CappedKernelProgram (Triple tripleCode position)

def scale (a : ℚ) (p : Triple) : Triple := (a*p.1,(a*p.2.1,a*p.2.2))

noncomputable def triples (rho U C K : ℕ) (x : Input) : List Triple :=
  (TransformedGauss.nodes rho U C K (x.1,CenteredGaussLabels.labels x.2)).map
    (scale (factor rho x.1.1.2))
noncomputable def nuclei (rho U C K : ℕ) (x : Input) : List BinaryPosition :=
  NuclearCoordinateOutput.positions (triples rho U C K x)

noncomputable opaque meshProgram : Procedure inputCode Nat.bits (fun x => x.1.1.2) :=
  (Procedure.second unaryCode Nat.bits).comp
    ((Procedure.first _ _).comp (Procedure.first _ _))

noncomputable opaque factorProgram (rho : ℕ) : Procedure inputCode ratCode
    (fun x => factor rho x.1.1.2) := by
  let n := meshProgram
  let n2 := Procedure.binaryMul.comp (n.pair n)
  let n3 := Procedure.binaryMul.comp (n2.pair n)
  let denominator := Procedure.binaryMul.comp
    ((Procedure.constant inputCode Nat.bits 8).pair n3)
  let p := Procedure.ratDiv.comp
    ((Procedure.constant inputCode ratCode (rho:ℚ)).pair (Procedure.natToRat.comp denominator))
  exact p.congrFun (by
    intro x
    change (rho:ℚ)/((8*((x.1.1.2*x.1.1.2)*x.1.1.2):ℕ):ℚ) = factor rho x.1.1.2
    simp only [factor,Nat.cast_mul,Nat.cast_ofNat,pow_succ,pow_zero,one_mul])

noncomputable opaque scaleProgram : Procedure (prodCode ratCode tripleCode) tripleCode
    (fun x => scale x.1 x.2) := by
  let a := Procedure.first ratCode tripleCode
  let p := Procedure.second ratCode tripleCode
  let x := EulerRegisters.tripleFirstProgram.comp p
  let y := EulerRegisters.tripleSecondProgram.comp p
  let z := EulerRegisters.tripleThirdProgram.comp p
  exact (Procedure.ratMul.comp (a.pair x)).pair
    ((Procedure.ratMul.comp (a.pair y)).pair (Procedure.ratMul.comp (a.pair z)))

noncomputable opaque triplesProgram (rho U C K : ℕ) :
    Procedure inputCode (listCode tripleCode) (triples rho U C K) := by
  let raw := (TransformedGauss.listProgram rho U C K).comp CenteredNuclearProgram.argumentsProgram
  exact (Procedure.listMapWith (ea := ratCode) (eb := tripleCode) (ec := tripleCode)
    (f := scale) (0,(0,0)) (0,(0,0)) scaleProgram).comp ((factorProgram rho).pair raw)

noncomputable opaque program (rho U C K : ℕ) :
    Procedure inputCode (BinaryEncoding.list binaryPositionCodec).encode (nuclei rho U C K) :=
  NuclearCoordinateOutput.positionsProgram.comp (triplesProgram rho U C K)

end ContinuumCoulomb.PhysicalNuclearProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_UnitCoulombProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal output codec for a complete unit-charge Coulomb instance.
The electron count is unary, and both rational thresholds are emitted in
canonical numerator/positive-denominator form. -/

namespace ContinuumCoulomb.UnitCoulombProgram
open ExactQuantumFactoring.BitStackProgram

def metadataCode : (ℕ×(ℚ×ℚ)) → List Bool := prodCode unaryCode (prodCode ratCode ratCode)
def inputCode : Input → List Bool := prodCode PhysicalNuclearProgram.inputCode metadataCode

noncomputable def value (rho U C K : ℕ) (x : Input) : UnitCoulomb where
  nuclei := PhysicalNuclearProgram.nuclei rho U C K x.1
  electrons := x.2.1
  lower := NuclearCoordinateOutput.rational x.2.2.1
  upper := NuclearCoordinateOutput.rational x.2.2.2

noncomputable opaque unaryOutput : Procedure unaryCode BinaryEncoding.unary.encode id := by
  let bytes : Procedure unaryCode (id : List Bool → List Bool) unaryCode :=
    (Procedure.identity unaryCode).result (by intro n; rfl)
  let p := Procedure.append.comp
    (bytes.pair (Procedure.constant unaryCode (id : List Bool → List Bool) [false]))
  exact p.result (by intro n; exact (AmplificationProgram.encodeUnary_replicate n).symm)

noncomputable opaque geometryProgram : Procedure inputCode PhysicalNuclearProgram.inputCode Prod.fst :=
  Procedure.first _ _
noncomputable opaque metadataProgram : Procedure inputCode metadataCode Prod.snd := Procedure.second _ _
noncomputable opaque electronsProgram : Procedure inputCode BinaryEncoding.unary.encode (fun x => x.2.1) :=
  unaryOutput.comp ((Procedure.first _ _).comp metadataProgram)
noncomputable opaque thresholdsInputProgram : Procedure inputCode (prodCode ratCode ratCode)
    (fun x => x.2.2) := (Procedure.second _ _).comp metadataProgram

noncomputable opaque thresholdsProgram : Procedure inputCode SourcePrograms.thresholdCodec.encode
    (fun x => (NuclearCoordinateOutput.rational x.2.2.1,NuclearCoordinateOutput.rational x.2.2.2)) :=
  (EncodingPrograms.appendPair binaryRationalCodec binaryRationalCodec).comp
    ((NuclearCoordinateOutput.rationalProgram.comp ((Procedure.first _ _).comp thresholdsInputProgram)).pair
      (NuclearCoordinateOutput.rationalProgram.comp ((Procedure.second _ _).comp thresholdsInputProgram)))

noncomputable opaque tailProgram : Procedure inputCode UnitBinaryProgram.tailCodec.encode
    (fun x => (x.2.1,(NuclearCoordinateOutput.rational x.2.2.1,NuclearCoordinateOutput.rational x.2.2.2))) :=
  (EncodingPrograms.appendPair BinaryEncoding.unary SourcePrograms.thresholdCodec).comp
    (electronsProgram.pair thresholdsProgram)

noncomputable opaque program (rho U C K : ℕ) : Procedure inputCode unitCoulombCodec.encode (value rho U C K) :=
  ((EncodingPrograms.appendPair (BinaryEncoding.list binaryPositionCodec) UnitBinaryProgram.tailCodec).comp
    (((PhysicalNuclearProgram.program rho U C K).comp geometryProgram).pair tailProgram)).result
      (by intro x; rfl)

end ContinuumCoulomb.UnitCoulombProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_AffinePhysicalOutput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A canonical unit-charge instance with the complete physical scalar offset.
The coordinate and threshold metadata remain explicit until the source program
supplies the same fixed polynomial scales to both components. -/

namespace ContinuumCoulomb.AffinePhysicalOutput
open ExactQuantumFactoring.BitStackProgram

noncomputable def value (rho U C K : ℕ) (x : Input) : UnitCoulomb :=
  UnitCoulombProgram.value rho U C K (argument rho x)

noncomputable opaque argumentProgram (rho : ℕ) :
    Procedure inputCode UnitCoulombProgram.inputCode (argument rho) := by
  let geom := Procedure.first PhysicalNuclearProgram.inputCode AffinePhysicalThreshold.inputCode
  let numbers := Procedure.second PhysicalNuclearProgram.inputCode AffinePhysicalThreshold.inputCode
  let count := AffinePhysicalThreshold.electronsProgram.comp numbers
  let endpoints := (AffinePhysicalThreshold.program rho).comp numbers
  exact geom.pair (count.pair endpoints)

noncomputable opaque program (rho U C K : ℕ) :
    Procedure inputCode unitCoulombCodec.encode (value rho U C K) :=
  (UnitCoulombProgram.program rho U C K).comp (argumentProgram rho)

end ContinuumCoulomb.AffinePhysicalOutput

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CalibratedEvaluationParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal scalar function supplied to calibrated-distance bisection.
The displacement/weight bound, amplification and requested accuracy are unary;
the positive target parameters and the queried distance are rational. -/

namespace ContinuumCoulomb.CalibratedEvaluation

noncomputable def gap (rho N P : ℕ) (d : ℚ) : ℚ :=
  max 0 (CoulombEvaluation.approximate rho (coulombPrecision N P) 0 -
    CoulombEvaluation.approximate rho (coulombPrecision N P) d)

noncomputable def root (rho N P : ℕ) (K d : ℚ) : ℚ :=
  RationalSquareRoot.value (rootPrecision P, K * gap rho N P d)

noncomputable def value (rho : ℕ) (e : Environment) (d : ℚ) : ℚ :=
  (e.2.1 : ℚ) * ComputableHopping.approximate
      ((e.1.1, hoppingPrecision e.2.1 e.1.2), d) -
    e.2.2.1 * root rho e.1.1 e.1.2 e.2.2.2 d

end ContinuumCoulomb.CalibratedEvaluation

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CalibratedEvaluationComponents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An actual polynomial TM2 evaluator for the Coulomb-calibrated residual.
This is the numeric callback used by deterministic bisection. -/

namespace ContinuumCoulomb.CalibratedEvaluation
open ExactQuantumFactoring.BitStackProgram

attribute [local irreducible] CoulombEvaluation.approximate

def environmentCode : Environment → List Bool :=
  prodCode (prodCode unaryCode unaryCode) (prodCode unaryCode (prodCode ratCode ratCode))

def inputCode : (Environment × ℚ) → List Bool := prodCode environmentCode ratCode

noncomputable opaque coulombPrecisionProgram :
    Procedure (prodCode unaryCode unaryCode) unaryCode (fun x => coulombPrecision x.1 x.2) := by
  let n := Procedure.unarySuccessor.comp (Procedure.first unaryCode unaryCode)
  let p := ResolventSchedule.squareProgram.comp
    (Procedure.unarySuccessor.comp (Procedure.second unaryCode unaryCode))
  let prod := ResolventSchedule.mulProgram.comp (n.pair p)
  exact ((CoulombEvaluation.scaleProgram 64).comp prod).congrFun (by
    intro x
    simp only [Function.comp_apply, Nat.succ_eq_add_one, coulombPrecision]
    ring)

noncomputable opaque hoppingPrecisionProgram :
    Procedure (prodCode unaryCode unaryCode) unaryCode (fun x => hoppingPrecision x.1 x.2) := by
  let s := Procedure.unarySuccessor.comp (Procedure.first unaryCode unaryCode)
  let p := Procedure.unarySuccessor.comp (Procedure.second unaryCode unaryCode)
  let prod := ResolventSchedule.mulProgram.comp (s.pair p)
  exact ((CoulombEvaluation.scaleProgram 4).comp prod).congrFun (by
    intro x
    simp only [Function.comp_apply, Nat.succ_eq_add_one, hoppingPrecision]
    ring)

noncomputable opaque rootPrecisionProgram : Procedure unaryCode unaryCode rootPrecision :=
  ((CoulombEvaluation.scaleProgram 8).comp Procedure.unarySuccessor).congrFun (by intro x; rfl)

noncomputable opaque environmentProgram : Procedure inputCode environmentCode Prod.fst :=
  Procedure.first environmentCode ratCode
noncomputable opaque distanceProgram : Procedure inputCode ratCode Prod.snd :=
  Procedure.second environmentCode ratCode
noncomputable opaque metadataProgram : Procedure inputCode (prodCode unaryCode unaryCode)
    (fun x => x.1.1) :=
  (Procedure.first (prodCode unaryCode unaryCode)
    (prodCode unaryCode (prodCode ratCode ratCode))).comp environmentProgram
noncomputable opaque boundProgram : Procedure inputCode unaryCode (fun x => x.1.1.1) :=
  (Procedure.first unaryCode unaryCode).comp metadataProgram
noncomputable opaque precisionProgram : Procedure inputCode unaryCode (fun x => x.1.1.2) :=
  (Procedure.second unaryCode unaryCode).comp metadataProgram
noncomputable opaque parametersProgram : Procedure inputCode
    (prodCode unaryCode (prodCode ratCode ratCode)) (fun x => x.1.2) :=
  (Procedure.second (prodCode unaryCode unaryCode)
    (prodCode unaryCode (prodCode ratCode ratCode))).comp environmentProgram
noncomputable opaque scaleProgram : Procedure inputCode unaryCode (fun x => x.1.2.1) :=
  (Procedure.first unaryCode (prodCode ratCode ratCode)).comp parametersProgram
noncomputable opaque scalarParametersProgram : Procedure inputCode (prodCode ratCode ratCode)
    (fun x => x.1.2.2) :=
  (Procedure.second unaryCode (prodCode ratCode ratCode)).comp parametersProgram
noncomputable opaque tauProgram : Procedure inputCode ratCode (fun x => x.1.2.2.1) :=
  (Procedure.first ratCode ratCode).comp scalarParametersProgram
noncomputable opaque weightProgram : Procedure inputCode ratCode (fun x => x.1.2.2.2) :=
  (Procedure.second ratCode ratCode).comp scalarParametersProgram
noncomputable opaque coulombAccuracyProgram : Procedure inputCode unaryCode
    (fun x => coulombPrecision x.1.1.1 x.1.1.2) :=
  coulombPrecisionProgram.comp metadataProgram
noncomputable def onsiteArgument (x : Environment × ℚ) : CoulombEvaluation.Input :=
  (coulombPrecision x.1.1.1 x.1.1.2, 0)
noncomputable def separatedArgument (x : Environment × ℚ) : CoulombEvaluation.Input :=
  (coulombPrecision x.1.1.1 x.1.1.2, x.2)

noncomputable opaque onsiteArgumentProgram :
    Procedure inputCode CoulombEvaluation.inputCode onsiteArgument :=
  coulombAccuracyProgram.pair (Procedure.constant inputCode ratCode 0)
noncomputable opaque separatedArgumentProgram :
    Procedure inputCode CoulombEvaluation.inputCode separatedArgument :=
  coulombAccuracyProgram.pair distanceProgram

noncomputable opaque onsiteRawProgram (rho : ℕ) : Procedure inputCode ratCode
    ((fun q : CoulombEvaluation.Input => CoulombEvaluation.approximate rho q.1 q.2) ∘ onsiteArgument) :=
  (CoulombEvaluation.program rho).comp onsiteArgumentProgram
noncomputable opaque separatedRawProgram (rho : ℕ) : Procedure inputCode ratCode
    ((fun q : CoulombEvaluation.Input => CoulombEvaluation.approximate rho q.1 q.2) ∘ separatedArgument) :=
  (CoulombEvaluation.program rho).comp separatedArgumentProgram

noncomputable opaque onsiteProgram (rho : ℕ) : Procedure inputCode ratCode
    (fun x => CoulombEvaluation.approximate rho (coulombPrecision x.1.1.1 x.1.1.2) 0) :=
  (onsiteRawProgram rho).congrFun (by intro x; simp only [Function.comp_apply, onsiteArgument])
noncomputable opaque separatedProgram (rho : ℕ) : Procedure inputCode ratCode
    (fun x => CoulombEvaluation.approximate rho (coulombPrecision x.1.1.1 x.1.1.2) x.2) :=
  (separatedRawProgram rho).congrFun (by intro x; simp only [Function.comp_apply, separatedArgument])

noncomputable def gapCompBeta {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool}
    {ec : γ → List Bool} {f : α → β} {g : β → γ} (q : Procedure eb ec g)
    (p : Procedure ea eb f) : Procedure ea ec (fun a => g (f a)) :=
  q.comp p

noncomputable opaque gapProgram (rho : ℕ) : Procedure inputCode ratCode
    (fun x => gap rho x.1.1.1 x.1.1.2 x.2) :=
  (gapCompBeta CappedKernelProgram.maximumProgram ((Procedure.constant inputCode ratCode 0).pair
    (gapCompBeta Procedure.ratSub ((onsiteProgram rho).pair (separatedProgram rho))))).congrFun
      (by intro x; rfl)
noncomputable opaque radicandProgram (rho : ℕ) : Procedure inputCode ratCode
    (fun x => x.1.2.2.2 * gap rho x.1.1.1 x.1.1.2 x.2) :=
  Procedure.ratMul.comp (weightProgram.pair (gapProgram rho))
noncomputable opaque rootProgram (rho : ℕ) : Procedure inputCode ratCode
    (fun x => root rho x.1.1.1 x.1.1.2 x.1.2.2.2 x.2) :=
  (RationalSquareRoot.program.comp
    ((rootPrecisionProgram.comp precisionProgram).pair (radicandProgram rho))).congrFun
      (by intro x; rfl)
noncomputable opaque hoppingAccuracyProgram : Procedure inputCode unaryCode
    (fun x => hoppingPrecision x.1.2.1 x.1.1.2) :=
  hoppingPrecisionProgram.comp (scaleProgram.pair precisionProgram)
noncomputable opaque hoppingProgram : Procedure inputCode ratCode
    (fun x => ComputableHopping.approximate ((x.1.1.1, hoppingPrecision x.1.2.1 x.1.1.2), x.2)) :=
  ComputableHopping.program.comp ((boundProgram.pair hoppingAccuracyProgram).pair distanceProgram)
noncomputable opaque scaledHoppingProgram : Procedure inputCode ratCode
    (fun x => (x.1.2.1 : ℚ) *
      ComputableHopping.approximate ((x.1.1.1, hoppingPrecision x.1.2.1 x.1.1.2), x.2)) :=
  Procedure.ratMul.comp ((Procedure.natToRat.comp
    (Procedure.unaryToBits.comp scaleProgram)).pair hoppingProgram)
noncomputable opaque targetProgram (rho : ℕ) : Procedure inputCode ratCode
    (fun x => x.1.2.2.1 * root rho x.1.1.1 x.1.1.2 x.1.2.2.2 x.2) :=
  Procedure.ratMul.comp (tauProgram.pair (rootProgram rho))

end ContinuumCoulomb.CalibratedEvaluation

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CalibratedBisection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Deterministic bisection with the concrete hopping/Coulomb evaluator.
The premises are endpoint signs and the already proved separated-site gap;
there is no numeric evaluator assumption. -/

noncomputable section
namespace ContinuumCoulomb.CalibratedEvaluation
open ExactQuantumFactoring.BitStackProgram

def bisectionInputCode : BisectionInput → List Bool :=
  prodCode unaryCode (prodCode environmentCode (prodCode ratCode ratCode))

def bisect (rho : ℕ) (x : BisectionInput) : ℚ :=
  BisectionProgram.approximate (value rho) (bisectionArgument x)

noncomputable opaque bisectionArgumentProgram : Procedure bisectionInputCode
    (BisectionProgram.inputCode environmentCode) bisectionArgument := by
  let n := Procedure.first unaryCode (prodCode environmentCode (prodCode ratCode ratCode))
  let tail := Procedure.second unaryCode (prodCode environmentCode (prodCode ratCode ratCode))
  let env := (Procedure.first environmentCode (prodCode ratCode ratCode)).comp tail
  let ends := (Procedure.second environmentCode (prodCode ratCode ratCode)).comp tail
  let np := (Procedure.first (prodCode unaryCode unaryCode)
    (prodCode unaryCode (prodCode ratCode ratCode))).comp env
  let p := (Procedure.second unaryCode unaryCode).comp np
  let p1 := Procedure.natToRat.comp (Procedure.unaryToBits.comp
    (Procedure.unarySuccessor.comp p))
  let delta := Procedure.ratInv.comp p1
  exact (n.pair (env.pair (delta.pair ends))).congrFun (by
    intro x
    simp only [Function.comp_apply, id_eq, Nat.succ_eq_add_one, bisectionArgument,
      tolerance, one_div, Nat.cast_add, Nat.cast_one]
    )

def residual (rho : ℕ) (e : Environment) (d : ℝ) : ℝ :=
  (e.2.1 : ℝ) * planarHopping d -
    coulombHoppingTarget (GaussianFrequency.frequency rho) e.2.2.1 e.2.2.2 d

def residualLipschitz (rho : ℕ) (e : Environment) : ℝ :=
  (e.2.1 : ℝ) * planarHoppingLipschitzConstant +
    coulombTargetLipschitzConstant (GaussianFrequency.frequency rho) e.2.2.1 e.2.2.2

end ContinuumCoulomb.CalibratedEvaluation

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_CalibratedEvaluationProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The final polynomial TM2 composition for the actual calibrated residual. -/

namespace ContinuumCoulomb.CalibratedEvaluation
open ExactQuantumFactoring.BitStackProgram

attribute [local irreducible] CoulombEvaluation.approximate

noncomputable def evaluatedExpression (rho : ℕ) (x : Environment × ℚ) : ℚ :=
  (x.1.2.1 : ℚ) *
    ComputableHopping.approximate ((x.1.1.1, hoppingPrecision x.1.2.1 x.1.1.2), x.2) -
      x.1.2.2.1 * root rho x.1.1.1 x.1.1.2 x.1.2.2.2 x.2

theorem evaluatedExpression_eq (rho : ℕ) (x : Environment × ℚ) :
    evaluatedExpression rho x = value rho x.1 x.2 := rfl

noncomputable opaque valuesProgram (rho : ℕ) : Procedure inputCode (prodCode ratCode ratCode)
    (fun x => ((x.1.2.1 : ℚ) *
      ComputableHopping.approximate ((x.1.1.1, hoppingPrecision x.1.2.1 x.1.1.2), x.2),
        x.1.2.2.1 * root rho x.1.1.1 x.1.1.2 x.1.2.2.2 x.2)) :=
  scaledHoppingProgram.pair (targetProgram rho)

noncomputable opaque subtractValuesProgram (rho : ℕ) : Procedure inputCode ratCode
    ((fun q : ℚ × ℚ => q.1 - q.2) ∘ (fun x : Environment × ℚ => ((x.1.2.1 : ℚ) *
      ComputableHopping.approximate ((x.1.1.1, hoppingPrecision x.1.2.1 x.1.1.2), x.2),
        x.1.2.2.1 * root rho x.1.1.1 x.1.1.2 x.1.2.2.2 x.2))) :=
  Procedure.ratSub.comp (valuesProgram rho)

theorem subtractValues_function (rho : ℕ) :
    ((fun q : ℚ × ℚ => q.1 - q.2) ∘ (fun x : Environment × ℚ => ((x.1.2.1 : ℚ) *
      ComputableHopping.approximate ((x.1.1.1, hoppingPrecision x.1.2.1 x.1.1.2), x.2),
        x.1.2.2.1 * root rho x.1.1.1 x.1.1.2 x.1.2.2.2 x.2))) = evaluatedExpression rho := by
  exact subtract_pair_function _ _

noncomputable opaque rawProgram (rho : ℕ) : Procedure inputCode ratCode (evaluatedExpression rho) :=
  cast (congrArg (fun f : Environment × ℚ → ℚ => Procedure inputCode ratCode f)
    (subtractValues_function rho)) (subtractValuesProgram rho)

noncomputable opaque program (rho : ℕ) : Procedure inputCode ratCode
    (fun x => value rho x.1 x.2) :=
  cast (congrArg (fun f : Environment × ℚ → ℚ => Procedure inputCode ratCode f)
    (funext (evaluatedExpression_eq rho))) (rawProgram rho)

end ContinuumCoulomb.CalibratedEvaluation

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CalibratedBisectionMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal bisection with the certified calibrated-residual machine. -/

noncomputable section
namespace ContinuumCoulomb.CalibratedEvaluation
open ExactQuantumFactoring.BitStackProgram

noncomputable opaque bisectionProgram (rho : ℕ) : Procedure bisectionInputCode ratCode (bisect rho) :=
  ((BisectionProgram.program (program rho)).comp bisectionArgumentProgram).congrFun
    (by intro x; rfl)


end ContinuumCoulomb.CalibratedEvaluation

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CalibratedLipschitzBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed unary guard bounds the actual residual modulus by a polynomial
in the displacement/weight bound and the amplification. -/

noncomputable section
namespace ContinuumCoulomb.CalibratedEvaluation

def targetModulusBase (rho : ℕ) : ℝ :=
  localizedCoulombLipschitzConstant (GaussianFrequency.frequency rho) /
    (2 * Real.sqrt (localizedGramConstant (GaussianFrequency.frequency rho)))

def lipschitzGuard (rho : ℕ) : ℕ :=
  ⌈(planarHoppingLipschitzConstant : ℝ) + targetModulusBase rho⌉₊ + 1

end ContinuumCoulomb.CalibratedEvaluation

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CalibratedBisectionSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial unary iteration and evaluation-precision choices for the
actual calibrated bisection. -/

noncomputable section
namespace ContinuumCoulomb.CalibratedEvaluation

def iterations (rho : ℕ) (e : Environment) : ℕ :=
  16 * lipschitzGuard rho * (e.2.1 + e.1.1 + 1) * (e.1.1 + 1) * (e.1.2 + 1)

def scheduledValue (rho : ℕ) (e : Environment) (a b : ℚ) : ℚ :=
  bisect rho (iterations rho e, (refinedEnvironment e, (a, b)))

end ContinuumCoulomb.CalibratedEvaluation

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactHeightEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete rational evaluator for the one-dimensional height residual.
There are exactly four dyadic square-root calls; all other terms are exact. -/

noncomputable section
namespace ContinuumCoulomb.ContactHeightEvaluation

def rootSample (e : Environment) (h : ℚ) (k : ℕ) : ℚ :=
  RationalSquareRoot.value (CalibratedEvaluation.rootPrecision e.1, (lengthAt e k) ^ 2 - h ^ 2)

def value (e : Environment) (h : ℚ) : ℚ :=
  lengthAt e 0 + lengthAt e 1 + lengthAt e 4 + lengthAt e 7 + lengthAt e 8 +
    rootSample e h 2 + rootSample e h 3 + rootSample e h 5 + rootSample e h 6 - e.2.2

end ContinuumCoulomb.ContactHeightEvaluation

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactHeightBisection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The height search uses fixed rational endpoints, its concrete evaluator,
and a linear unary precision schedule. The reference height is supplied by
the already proved contact intermediate-value theorem. -/

noncomputable section
namespace ContinuumCoulomb.ContactHeightEvaluation

def bisect (e : Environment) (n : ℕ) : ℚ :=
  BisectionProgram.approximate value (argument e n)

def scheduledValue (e : Environment) : ℚ := bisect (refinedEnvironment e) (iterations e)

end ContinuumCoulomb.ContactHeightEvaluation

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactRationalCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational contact vertices approximate the same exact height witness as
the deterministic height solve. This estimate preserves separation margins
when the requested precision is increased. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb.ContactHeightEvaluation

def stepX (e : Environment) (h : ℚ) (k : ℕ) : ℚ :=
  if k = 2 ∨ k = 3 ∨ k = 5 ∨ k = 6 then rootSample e h k else lengthAt e k

def vertex (e : Environment) (k : ℕ) : ℚ × ℚ :=
  (∑ j ∈ Finset.range k, stepX e (scheduledValue e) j,
    ∑ j ∈ Finset.range k, stepY (scheduledValue e) j)

def vertexPoint (e : Environment) (k : ℕ) : ContactPoint :=
  contactPoint (vertex e k).1 (vertex e k).2

end ContinuumCoulomb.ContactHeightEvaluation

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_ContactHeightProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal rational height-residual program. It reads nine input lengths
and executes four already-certified rational square-root subprograms. -/

namespace ContinuumCoulomb.ContactHeightEvaluation
open ExactQuantumFactoring.BitStackProgram

def environmentCode : Environment → List Bool :=
  prodCode unaryCode (prodCode (listCode ratCode) ratCode)

def inputCode : (Environment × ℚ) → List Bool := prodCode environmentCode ratCode

noncomputable opaque environmentProgram : Procedure inputCode environmentCode Prod.fst :=
  Procedure.first environmentCode ratCode

noncomputable opaque heightProgram : Procedure inputCode ratCode Prod.snd :=
  Procedure.second environmentCode ratCode

noncomputable opaque precisionProgram : Procedure inputCode unaryCode (fun x => x.1.1) :=
  (Procedure.first unaryCode (prodCode (listCode ratCode) ratCode)).comp environmentProgram

noncomputable opaque dataProgram : Procedure inputCode (prodCode (listCode ratCode) ratCode)
    (fun x => x.1.2) :=
  (Procedure.second unaryCode (prodCode (listCode ratCode) ratCode)).comp environmentProgram

noncomputable opaque lengthsProgram : Procedure inputCode (listCode ratCode)
    (fun x => x.1.2.1) :=
  (Procedure.first (listCode ratCode) ratCode).comp dataProgram

noncomputable opaque targetProgram : Procedure inputCode ratCode (fun x => x.1.2.2) :=
  (Procedure.second (listCode ratCode) ratCode).comp dataProgram

noncomputable opaque lengthProgram (k : ℕ) : Procedure inputCode ratCode
    (fun x => lengthAt x.1 k) :=
  (Procedure.listGet ratCode 1).comp
    ((Procedure.constant inputCode Nat.bits k).pair lengthsProgram)

noncomputable opaque squareLengthProgram (k : ℕ) : Procedure inputCode ratCode
    (fun x => (lengthAt x.1 k) ^ 2) :=
  (Procedure.ratMul.comp ((lengthProgram k).pair (lengthProgram k))).congrFun
    (by intro x; simp only [Function.comp_apply, pow_two])

noncomputable opaque squareHeightProgram : Procedure inputCode ratCode
    (fun x => x.2 ^ 2) :=
  (Procedure.ratMul.comp (heightProgram.pair heightProgram)).congrFun
    (by intro x; simp only [Function.comp_apply, pow_two])

noncomputable opaque radicandProgram (k : ℕ) : Procedure inputCode ratCode
    (fun x => (lengthAt x.1 k) ^ 2 - x.2 ^ 2) :=
  Procedure.ratSub.comp ((squareLengthProgram k).pair squareHeightProgram)

noncomputable opaque rootPrecisionProgram : Procedure inputCode unaryCode
    (fun x => CalibratedEvaluation.rootPrecision x.1.1) :=
  CalibratedEvaluation.rootPrecisionProgram.comp precisionProgram

noncomputable opaque rootProgram (k : ℕ) : Procedure inputCode ratCode
    (fun x => rootSample x.1 x.2 k) :=
  RationalSquareRoot.program.comp (rootPrecisionProgram.pair (radicandProgram k))

noncomputable opaque axial01Program : Procedure inputCode ratCode
    (fun x => lengthAt x.1 0 + lengthAt x.1 1) :=
  Procedure.ratAdd.comp ((lengthProgram 0).pair (lengthProgram 1))

noncomputable opaque axial014Program : Procedure inputCode ratCode
    (fun x => lengthAt x.1 0 + lengthAt x.1 1 + lengthAt x.1 4) :=
  Procedure.ratAdd.comp (axial01Program.pair (lengthProgram 4))

noncomputable opaque axial0147Program : Procedure inputCode ratCode
    (fun x => lengthAt x.1 0 + lengthAt x.1 1 + lengthAt x.1 4 + lengthAt x.1 7) :=
  Procedure.ratAdd.comp (axial014Program.pair (lengthProgram 7))

noncomputable opaque axialProgram : Procedure inputCode ratCode
    (fun x => lengthAt x.1 0 + lengthAt x.1 1 + lengthAt x.1 4 + lengthAt x.1 7 + lengthAt x.1 8) :=
  Procedure.ratAdd.comp (axial0147Program.pair (lengthProgram 8))

noncomputable opaque firstRootProgram : Procedure inputCode ratCode
    (fun x => lengthAt x.1 0 + lengthAt x.1 1 + lengthAt x.1 4 + lengthAt x.1 7 + lengthAt x.1 8 +
      rootSample x.1 x.2 2) := Procedure.ratAdd.comp (axialProgram.pair (rootProgram 2))

noncomputable opaque secondRootProgram : Procedure inputCode ratCode
    (fun x => lengthAt x.1 0 + lengthAt x.1 1 + lengthAt x.1 4 + lengthAt x.1 7 + lengthAt x.1 8 +
      rootSample x.1 x.2 2 + rootSample x.1 x.2 3) :=
  Procedure.ratAdd.comp (firstRootProgram.pair (rootProgram 3))

noncomputable opaque thirdRootProgram : Procedure inputCode ratCode
    (fun x => lengthAt x.1 0 + lengthAt x.1 1 + lengthAt x.1 4 + lengthAt x.1 7 + lengthAt x.1 8 +
      rootSample x.1 x.2 2 + rootSample x.1 x.2 3 + rootSample x.1 x.2 5) :=
  Procedure.ratAdd.comp (secondRootProgram.pair (rootProgram 5))

noncomputable opaque spanProgram : Procedure inputCode ratCode
    (fun x => lengthAt x.1 0 + lengthAt x.1 1 + lengthAt x.1 4 + lengthAt x.1 7 + lengthAt x.1 8 +
      rootSample x.1 x.2 2 + rootSample x.1 x.2 3 + rootSample x.1 x.2 5 + rootSample x.1 x.2 6) :=
  Procedure.ratAdd.comp (thirdRootProgram.pair (rootProgram 6))

noncomputable opaque program : Procedure inputCode ratCode (fun x => value x.1 x.2) :=
  Procedure.ratSub.comp (spanProgram.pair targetProgram)

end ContinuumCoulomb.ContactHeightEvaluation

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_ContactHeightScheduleProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial-time execution of the concrete contact-height search. All
precision and iteration counts are unary linear functions of the request. -/

namespace ContinuumCoulomb.ContactHeightEvaluation
open ExactQuantumFactoring.BitStackProgram

noncomputable opaque envPrecisionProgram : Procedure environmentCode unaryCode Prod.fst :=
  Procedure.first unaryCode (prodCode (listCode ratCode) ratCode)

noncomputable opaque envDataProgram : Procedure environmentCode
    (prodCode (listCode ratCode) ratCode) Prod.snd :=
  Procedure.second unaryCode (prodCode (listCode ratCode) ratCode)

noncomputable opaque refinedPrecisionProgram : Procedure environmentCode unaryCode
    (fun e => 16 * (e.1 + 1)) :=
  ((CoulombEvaluation.scaleProgram 16).comp Procedure.unarySuccessor).comp envPrecisionProgram

noncomputable opaque refinedProgram : Procedure environmentCode environmentCode
    refinedEnvironment := refinedPrecisionProgram.pair envDataProgram

noncomputable opaque iterationProgram : Procedure environmentCode unaryCode iterations :=
  ((CoulombEvaluation.scaleProgram 64).comp Procedure.unarySuccessor).comp envPrecisionProgram

noncomputable opaque toleranceProgram : Procedure environmentCode ratCode
    (fun e => tolerance (refinedEnvironment e)) := by
  let successor := Procedure.unarySuccessor.comp refinedPrecisionProgram
  let rational := Procedure.natToRat.comp (Procedure.unaryToBits.comp successor)
  exact (Procedure.ratInv.comp rational).congrFun (by
    intro e
    simp only [Function.comp_apply, id_eq, tolerance, refinedEnvironment,
      Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, one_div])

noncomputable opaque scheduledArgumentProgram : Procedure environmentCode
    (BisectionProgram.inputCode environmentCode)
    (fun e => argument (refinedEnvironment e) (iterations e)) :=
  iterationProgram.pair (refinedProgram.pair
    (toleranceProgram.pair (Procedure.constant environmentCode
      (prodCode ratCode ratCode) ((2 / 5 : ℚ), (3 / 4 : ℚ)))))

noncomputable opaque scheduledProgram : Procedure environmentCode ratCode scheduledValue :=
  ((BisectionProgram.program program).comp scheduledArgumentProgram).congrFun
    (by intro e; rfl)

end ContinuumCoulomb.ContactHeightEvaluation

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_ContactVertexProgram
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal polynomial-time rational coordinates for a fixed nine-link
contact path. The height program is followed by four dyadic root evaluations
and the fixed finite prefix sums. -/

namespace ContinuumCoulomb.ContactHeightEvaluation
open scoped BigOperators
open ExactQuantumFactoring.BitStackProgram

noncomputable opaque stepXProgram (k : ℕ) : Procedure inputCode ratCode
    (fun x => stepX x.1 x.2 k) := by
  by_cases hs : k = 2 ∨ k = 3 ∨ k = 5 ∨ k = 6
  · exact (rootProgram k).congrFun (by intro x; simp only [stepX, ite_eq_left hs])
  · exact (lengthProgram k).congrFun (by intro x; simp only [stepX, ite_eq_right hs])

noncomputable opaque stepYProgram (k : ℕ) : Procedure inputCode ratCode
    (fun x => stepY x.2 k) := by
  by_cases hs : k = 2 ∨ k = 3
  · exact heightProgram.congrFun (by intro x; simp only [stepY, ite_eq_left hs])
  · by_cases hs' : k = 5 ∨ k = 6
    · exact (Procedure.ratNeg.comp heightProgram).congrFun (by
        intro x
        simp only [Function.comp_apply, stepY, ite_eq_right hs, ite_eq_left hs'])
    · exact (Procedure.constant inputCode ratCode 0).congrFun (by
        intro x
        simp only [stepY, ite_eq_right hs, ite_eq_right hs'])

noncomputable def prefixXProgram : (k : ℕ) → Procedure inputCode ratCode
    (fun x => ∑ j ∈ Finset.range k, stepX x.1 x.2 j)
  | 0 => (Procedure.constant inputCode ratCode 0).congrFun (by intro x; simp)
  | k + 1 => (Procedure.ratAdd.comp ((prefixXProgram k).pair (stepXProgram k))).congrFun
      (by intro x; simp only [Function.comp_apply, Finset.sum_range_succ])

noncomputable def prefixYProgram : (k : ℕ) → Procedure inputCode ratCode
    (fun x => ∑ j ∈ Finset.range k, stepY x.2 j)
  | 0 => (Procedure.constant inputCode ratCode 0).congrFun (by intro x; simp)
  | k + 1 => (Procedure.ratAdd.comp ((prefixYProgram k).pair (stepYProgram k))).congrFun
      (by intro x; simp only [Function.comp_apply, Finset.sum_range_succ])

noncomputable opaque coordinateInputProgram : Procedure environmentCode inputCode
    (fun e => (e, scheduledValue e)) :=
  (Procedure.identity environmentCode).pair scheduledProgram

noncomputable opaque vertexProgram (k : ℕ) : Procedure environmentCode
    (prodCode ratCode ratCode) (fun e => vertex e k) :=
  (((prefixXProgram k).pair (prefixYProgram k)).comp coordinateInputProgram).congrFun
    (by intro e; rfl)

end ContinuumCoulomb.ContactHeightEvaluation

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactClosedCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The rational path keeps both original endpoints exact. Replacing its
last approximate prefix sum by the prescribed span improves its distance
to the exact reference path and does not change the polynomial program. -/

noncomputable section
namespace ContinuumCoulomb.ContactHeightEvaluation
open ExactQuantumFactoring.BitStackProgram

def closedVertex (e : Environment) (k : ℕ) : ℚ × ℚ :=
  if k = 9 then (e.2.2, 0) else vertex e k

def closedVertexPoint (e : Environment) (k : ℕ) : ContactPoint :=
  contactPoint (closedVertex e k).1 (closedVertex e k).2

noncomputable opaque closedVertexProgram (k : ℕ) : Procedure environmentCode
    (prodCode ratCode ratCode) (fun e => closedVertex e k) := by
  by_cases hk : k = 9
  · let data := Procedure.second unaryCode (prodCode (listCode ratCode) ratCode)
    let target := (Procedure.second (listCode ratCode) ratCode).comp data
    exact (target.pair (Procedure.constant environmentCode ratCode 0)).congrFun (by
      intro e
      simp only [closedVertex, ite_eq_left hk, Function.comp_apply])
  · exact (vertexProgram k).congrFun (by
      intro e
      simp only [closedVertex, ite_eq_right hk])

end ContinuumCoulomb.ContactHeightEvaluation

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactRationalGadget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete rational twenty-site gadget. The two paths share the same
rational prescribed span; their outer endpoints are exact and their
internal vertices approximate the original independent-length gadget. -/

noncomputable section
namespace ContinuumCoulomb.ContactRationalGadget
open ContactHeightEvaluation

def position (x : Input) : ContactGadgetSite → ℚ × ℚ :=
  Sum.elim (fun k => closedVertex (leftEnvironment x) k.val)
    (Sum.elim (fun k =>
      (origin x.2.1 x.2.2.1 + (closedVertex (rightEnvironment x) (k.val + 1)).1,
        (closedVertex (rightEnvironment x) (k.val + 1)).2))
      (fun _ => if x.2.1 then (17 / 2, x.2.2.1) else (origin x.2.1 x.2.2.1, 0)))

def point (x : Input) (s : ContactGadgetSite) : ContactPoint :=
  contactPoint (position x s).1 (position x s).2

end ContinuumCoulomb.ContactRationalGadget

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactRationalLocal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational contact coordinates indexed by the actual nineteen local
mediator edges. Every link has a quantitative error and the nonedge margin
survives with a fixed minimum requested precision. -/

noncomputable section
namespace ContinuumCoulomb.ContactRationalLocal
open ContactMediator ContactRationalGadget

def position (P : ℕ) (negative : Bool) (ℓ : LocalEdge → ℚ) (s : LocalSite) : ℚ × ℚ :=
  ContactRationalGadget.position (input P negative ℓ) (localToContact s)

def point (P : ℕ) (negative : Bool) (ℓ : LocalEdge → ℚ) (s : LocalSite) : ContactPoint :=
  ContactRationalGadget.point (input P negative ℓ) (localToContact s)

end ContinuumCoulomb.ContactRationalLocal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactGlobalSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform all-site and nonedge separation for the actual final graph. -/

noncomputable section
namespace ContinuumCoulomb.ContactMediator
open MediatorIteration

def Nonedge (d : SquareLatticeHeisenberg) (W G : ℕ) (x y : GlobalSite d) : Prop :=
  ¬∃ a, samePair ((finalGraph d.bonds W G).left a) ((finalGraph d.bonds W G).right a) x y

end ContinuumCoulomb.ContactMediator

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactRationalGlobal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The rational local gadgets are glued through the exact final-graph
permutation. All old lattice sites remain fixed; all nineteen edges per
source edge retain a controlled error and all nonedges retain the margin. -/

noncomputable section
namespace ContinuumCoulomb.ContactRationalGlobal
open ContactMediator MediatorIteration

def localPoints (d : SquareLatticeHeisenberg) (P : ℕ) (ℓ : GlobalEdge d → ℚ)
    (e : Fin d.edges) : LocalSite → ContactPoint :=
  ContactRationalLocal.point P (edgeNegative d.bonds e) (fun a => ℓ (encodeEdge d.edges e a))

def point (d : SquareLatticeHeisenberg) (P : ℕ) (ℓ : GlobalEdge d → ℚ) :
    GlobalSite d → ContactPoint := globalPosition d (localPoints d P ℓ)

def position (d : SquareLatticeHeisenberg) (P : ℕ) (ℓ : GlobalEdge d → ℚ)
    (x : GlobalSite d) : ℚ × ℚ :=
  match (siteEquiv d.vertices d.edges).symm x with
  | Sum.inl i => (17 * (d.coordinate i).1, 17 * (d.coordinate i).2)
  | Sum.inr (e, u) => rationalPlace (d.contactEdge e)
      (ContactRationalLocal.position P (edgeNegative d.bonds e)
        (fun a => ℓ (encodeEdge d.edges e a)) (Sum.inr u))

end ContinuumCoulomb.ContactRationalGlobal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactCalibratedGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scaled rational contact coordinates retain the actual Coulomb
calibration, with the coordinate and scalar-evaluation errors added
explicitly. The gap follows from the proved separated-density estimate. -/

noncomputable section
namespace ContinuumCoulomb.ContactCalibratedGeometry
open ContactMediator MediatorIteration
open scoped BigOperators

def position (d : SquareLatticeHeisenberg) (P : ℕ) (q : ℚ)
    (ℓ : GlobalEdge d → ℚ) (x : GlobalSite d) : ℚ × ℚ :=
  (q * (ContactRationalGlobal.position d P ℓ x).1,
    q * (ContactRationalGlobal.position d P ℓ x).2)

def point (d : SquareLatticeHeisenberg) (P : ℕ) (q : ℚ)
    (ℓ : GlobalEdge d → ℚ) (x : GlobalSite d) : ContactPoint :=
  (q : ℝ) • ContactRationalGlobal.point d P ℓ x

end ContinuumCoulomb.ContactCalibratedGeometry

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_MediatorListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual TM2 programs which emit the central and spoke bond lists of one
simultaneous mediator stage. The index arithmetic follows the same
`n + 2e + spin` vertex enumeration as the proved finite-spin construction. -/

namespace ContinuumCoulomb.MediatorListProgram
open ExactQuantumFactoring.BitStackProgram

def bondCode : Bond → List Bool := prodCode Nat.bits (prodCode Nat.bits ratCode)

end ContinuumCoulomb.MediatorListProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_ContactCanonicalEdgeProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The canonical lattice strip is computed by integer comparisons. -/

namespace ContinuumCoulomb.ContactCanonicalEdgeProgram
open ExactQuantumFactoring.BitStackProgram

def latticeCode : (ℤ × ℤ) → List Bool := prodCode intCode intCode
def inputCode : ((ℤ × ℤ) × (ℤ × ℤ)) → List Bool := prodCode latticeCode latticeCode
def edgeCode (e : ContactGridEdge) : List Bool :=
  prodCode Procedure.boolCode (prodCode latticeCode Procedure.boolCode)
    (e.vertical, (e.anchor, e.reversed))

noncomputable opaque integerEqual : Procedure (prodCode intCode intCode)
    Procedure.boolCode (fun x => decide (x.1 = x.2)) :=
  (Procedure.binaryZero.comp (Procedure.intAbs.comp Procedure.intSub)).congrFun (by
    intro x
    simp only [Function.comp_apply, Int.natAbs_eq_zero, sub_eq_zero])

noncomputable opaque integerLess : Procedure (prodCode intCode intCode)
    Procedure.boolCode (fun x => decide (x.1 < x.2)) :=
  (Procedure.intSign.comp Procedure.intSub).congrFun (by
    intro x
    simp only [Function.comp_apply, sub_neg])

noncomputable opaque leftProgram : Procedure inputCode latticeCode Prod.fst :=
  Procedure.first latticeCode latticeCode
noncomputable opaque rightProgram : Procedure inputCode latticeCode Prod.snd :=
  Procedure.second latticeCode latticeCode
noncomputable opaque leftXProgram : Procedure inputCode intCode (fun x => x.1.1) :=
  (Procedure.first intCode intCode).comp leftProgram
noncomputable opaque leftYProgram : Procedure inputCode intCode (fun x => x.1.2) :=
  (Procedure.second intCode intCode).comp leftProgram
noncomputable opaque rightXProgram : Procedure inputCode intCode (fun x => x.2.1) :=
  (Procedure.first intCode intCode).comp rightProgram
noncomputable opaque rightYProgram : Procedure inputCode intCode (fun x => x.2.2) :=
  (Procedure.second intCode intCode).comp rightProgram

noncomputable opaque verticalProgram : Procedure inputCode Procedure.boolCode
    (fun x => decide (x.1.1 = x.2.1)) := integerEqual.comp (leftXProgram.pair rightXProgram)

noncomputable opaque forwardProgram : Procedure inputCode Procedure.boolCode
    (fun x => if decide (x.1.1 = x.2.1) then decide (x.1.2 < x.2.2) else decide (x.1.1 < x.2.1)) :=
  Procedure.conditional verticalProgram (integerLess.comp (leftYProgram.pair rightYProgram))
    (integerLess.comp (leftXProgram.pair rightXProgram))

noncomputable opaque anchorProgram : Procedure inputCode latticeCode
    (fun x => if (if decide (x.1.1 = x.2.1) then decide (x.1.2 < x.2.2)
      else decide (x.1.1 < x.2.1)) then x.1 else x.2) :=
  Procedure.conditional forwardProgram leftProgram rightProgram

noncomputable opaque reverseProgram : Procedure inputCode Procedure.boolCode
    (fun x => !(if decide (x.1.1 = x.2.1) then decide (x.1.2 < x.2.2)
      else decide (x.1.1 < x.2.1))) := Procedure.boolNot.comp forwardProgram

noncomputable opaque program : Procedure inputCode edgeCode
    (fun x => canonicalContactEdge x.1 x.2) :=
  (verticalProgram.pair (anchorProgram.pair reverseProgram)).result (by intro x; rfl)

end ContinuumCoulomb.ContactCanonicalEdgeProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_ContactRationalGadgetProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal polynomial-time computation of the twenty rational gadget
positions, including the two exact outer endpoints. -/

namespace ContinuumCoulomb.ContactRationalGadget
open ExactQuantumFactoring.BitStackProgram

def inputCode : Input → List Bool :=
  prodCode unaryCode (prodCode Procedure.boolCode
    (prodCode ratCode (prodCode (listCode ratCode) (listCode ratCode))))

def pointCode : (ℚ × ℚ) → List Bool := prodCode ratCode ratCode

noncomputable opaque precisionProgram : Procedure inputCode unaryCode Prod.fst :=
  Procedure.first unaryCode _

noncomputable opaque restProgram : Procedure inputCode
    (prodCode Procedure.boolCode (prodCode ratCode (prodCode (listCode ratCode) (listCode ratCode))))
      Prod.snd := Procedure.second unaryCode _

noncomputable opaque signProgram : Procedure inputCode Procedure.boolCode (fun x => x.2.1) :=
  (Procedure.first Procedure.boolCode _).comp restProgram

noncomputable opaque dataProgram : Procedure inputCode
    (prodCode ratCode (prodCode (listCode ratCode) (listCode ratCode))) (fun x => x.2.2) :=
  (Procedure.second Procedure.boolCode _).comp restProgram

noncomputable opaque centralProgram : Procedure inputCode ratCode (fun x => x.2.2.1) :=
  (Procedure.first ratCode _).comp dataProgram

noncomputable opaque listsProgram : Procedure inputCode
    (prodCode (listCode ratCode) (listCode ratCode)) (fun x => x.2.2.2) :=
  (Procedure.second ratCode _).comp dataProgram

noncomputable opaque leftListProgram : Procedure inputCode (listCode ratCode)
    (fun x => x.2.2.2.1) := (Procedure.first (listCode ratCode) (listCode ratCode)).comp listsProgram

noncomputable opaque rightListProgram : Procedure inputCode (listCode ratCode)
    (fun x => x.2.2.2.2) := (Procedure.second (listCode ratCode) (listCode ratCode)).comp listsProgram

noncomputable opaque positiveSpanProgram : Procedure inputCode ratCode
    (fun x => (17 - x.2.2.1) / 2) :=
  (Procedure.ratMul.comp
    ((Procedure.constant inputCode ratCode (1 / 2)).pair
      (Procedure.ratSub.comp ((Procedure.constant inputCode ratCode 17).pair centralProgram)))).congrFun
        (by intro x; simp only [Function.comp_apply]; ring)

noncomputable opaque positiveOriginProgram : Procedure inputCode ratCode
    (fun x => (17 + x.2.2.1) / 2) :=
  (Procedure.ratMul.comp
    ((Procedure.constant inputCode ratCode (1 / 2)).pair
      (Procedure.ratAdd.comp ((Procedure.constant inputCode ratCode 17).pair centralProgram)))).congrFun
        (by intro x; simp only [Function.comp_apply]; ring)

noncomputable opaque spanProgram : Procedure inputCode ratCode
    (fun x => span x.2.1 x.2.2.1) :=
  Procedure.conditional signProgram (Procedure.constant inputCode ratCode (17 / 2)) positiveSpanProgram

noncomputable opaque originProgram : Procedure inputCode ratCode
    (fun x => origin x.2.1 x.2.2.1) :=
  Procedure.conditional signProgram (Procedure.constant inputCode ratCode (17 / 2)) positiveOriginProgram

noncomputable opaque leftEnvironmentProgram : Procedure inputCode ContactHeightEvaluation.environmentCode
    leftEnvironment := precisionProgram.pair (leftListProgram.pair spanProgram)

noncomputable opaque rightEnvironmentProgram : Procedure inputCode ContactHeightEvaluation.environmentCode
    rightEnvironment := precisionProgram.pair (rightListProgram.pair spanProgram)

noncomputable opaque leftVertexProgram (k : ℕ) : Procedure inputCode pointCode
    (fun x => ContactHeightEvaluation.closedVertex (leftEnvironment x) k) :=
  (ContactHeightEvaluation.closedVertexProgram k).comp leftEnvironmentProgram

noncomputable opaque rightVertexProgram (k : ℕ) : Procedure inputCode pointCode
    (fun x => ContactHeightEvaluation.closedVertex (rightEnvironment x) k) :=
  (ContactHeightEvaluation.closedVertexProgram k).comp rightEnvironmentProgram

noncomputable opaque rightShiftProgram (k : ℕ) : Procedure inputCode pointCode
    (fun x => (origin x.2.1 x.2.2.1 +
      (ContactHeightEvaluation.closedVertex (rightEnvironment x) k).1,
        (ContactHeightEvaluation.closedVertex (rightEnvironment x) k).2)) := by
  let qx := (Procedure.first ratCode ratCode).comp (rightVertexProgram k)
  let qy := (Procedure.second ratCode ratCode).comp (rightVertexProgram k)
  exact (Procedure.ratAdd.comp (originProgram.pair qx)).pair qy

noncomputable opaque sideProgram : Procedure inputCode pointCode
    (fun x => if x.2.1 then (17 / 2, x.2.2.1) else (origin x.2.1 x.2.2.1, 0)) :=
  Procedure.conditional signProgram
    ((Procedure.constant inputCode ratCode (17 / 2)).pair centralProgram)
    (originProgram.pair (Procedure.constant inputCode ratCode 0))

noncomputable def positionProgram : (s : ContactGadgetSite) →
    Procedure inputCode pointCode (fun x => position x s)
  | Sum.inl k => leftVertexProgram k.val
  | Sum.inr (Sum.inl k) => rightShiftProgram (k.val + 1)
  | Sum.inr (Sum.inr _) => sideProgram

end ContinuumCoulomb.ContactRationalGadget

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_ContactRationalPlaceProgram
attribute [-simp] _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact strip placement uses only rational arithmetic and the two
computed orientation bits. It preserves the original lattice endpoints. -/

namespace ContinuumCoulomb.ContactRationalPlaceProgram
open ExactQuantumFactoring.BitStackProgram

def inputCode : Input → List Bool :=
  prodCode ContactCanonicalEdgeProgram.edgeCode ContactRationalGadget.pointCode

noncomputable opaque edgeProgram : Procedure inputCode ContactCanonicalEdgeProgram.edgeCode
    Prod.fst := Procedure.first _ _

noncomputable opaque pointProgram : Procedure inputCode ContactRationalGadget.pointCode
    Prod.snd := Procedure.second _ _

noncomputable opaque verticalProgram : Procedure inputCode Procedure.boolCode
    (fun x => x.1.vertical) :=
  ((Procedure.first Procedure.boolCode
    (prodCode ContactCanonicalEdgeProgram.latticeCode Procedure.boolCode)).precompose
      (fun e : ContactGridEdge => (e.vertical, (e.anchor, e.reversed)))).comp edgeProgram

noncomputable opaque edgeTailProgram : Procedure inputCode
    (prodCode ContactCanonicalEdgeProgram.latticeCode Procedure.boolCode)
    (fun x => (x.1.anchor, x.1.reversed)) :=
  ((Procedure.second Procedure.boolCode
    (prodCode ContactCanonicalEdgeProgram.latticeCode Procedure.boolCode)).precompose
      (fun e : ContactGridEdge => (e.vertical, (e.anchor, e.reversed)))).comp edgeProgram

noncomputable opaque reverseProgram : Procedure inputCode Procedure.boolCode
    (fun x => x.1.reversed) :=
  (Procedure.second ContactCanonicalEdgeProgram.latticeCode Procedure.boolCode).comp edgeTailProgram

noncomputable opaque anchorProgram : Procedure inputCode ContactCanonicalEdgeProgram.latticeCode
    (fun x => x.1.anchor) :=
  (Procedure.first ContactCanonicalEdgeProgram.latticeCode Procedure.boolCode).comp edgeTailProgram

noncomputable opaque anchorXProgram : Procedure inputCode ratCode
    (fun x => (x.1.anchor.1 : ℚ)) :=
  Procedure.intToRat.comp ((Procedure.first intCode intCode).comp anchorProgram)

noncomputable opaque anchorYProgram : Procedure inputCode ratCode
    (fun x => (x.1.anchor.2 : ℚ)) :=
  Procedure.intToRat.comp ((Procedure.second intCode intCode).comp anchorProgram)

noncomputable opaque rawXProgram : Procedure inputCode ratCode (fun x => x.2.1) :=
  (Procedure.first ratCode ratCode).comp pointProgram

noncomputable opaque rawYProgram : Procedure inputCode ratCode (fun x => x.2.2) :=
  (Procedure.second ratCode ratCode).comp pointProgram

noncomputable opaque reflectedXProgram : Procedure inputCode ratCode
    (fun x => if x.1.reversed then 17 - x.2.1 else x.2.1) :=
  Procedure.conditional reverseProgram
    (Procedure.ratSub.comp ((Procedure.constant inputCode ratCode 17).pair rawXProgram)) rawXProgram

noncomputable opaque baseXProgram : Procedure inputCode ratCode
    (fun x => 17 * (x.1.anchor.1 : ℚ)) :=
  Procedure.ratMul.comp ((Procedure.constant inputCode ratCode 17).pair anchorXProgram)

noncomputable opaque baseYProgram : Procedure inputCode ratCode
    (fun x => 17 * (x.1.anchor.2 : ℚ)) :=
  Procedure.ratMul.comp ((Procedure.constant inputCode ratCode 17).pair anchorYProgram)

noncomputable opaque xProgram : Procedure inputCode ratCode
    (fun x => if x.1.vertical then 17 * (x.1.anchor.1 : ℚ) - x.2.2
      else 17 * (x.1.anchor.1 : ℚ) + (if x.1.reversed then 17 - x.2.1 else x.2.1)) :=
  Procedure.conditional verticalProgram
    (Procedure.ratSub.comp (baseXProgram.pair rawYProgram))
    (Procedure.ratAdd.comp (baseXProgram.pair reflectedXProgram))

noncomputable opaque yProgram : Procedure inputCode ratCode
    (fun x => if x.1.vertical then 17 * (x.1.anchor.2 : ℚ) +
      (if x.1.reversed then 17 - x.2.1 else x.2.1)
      else 17 * (x.1.anchor.2 : ℚ) + x.2.2) :=
  Procedure.conditional verticalProgram
    (Procedure.ratAdd.comp (baseYProgram.pair reflectedXProgram))
    (Procedure.ratAdd.comp (baseYProgram.pair rawYProgram))

noncomputable opaque program : Procedure inputCode ContactRationalGadget.pointCode
    (fun x => ContactRationalGlobal.rationalPlace x.1 x.2) :=
  (xProgram.pair yProgram).congrFun (by
    intro x
    cases hv : x.1.vertical <;> cases hr : x.1.reversed <;>
      simp [ContactRationalGlobal.rationalPlace, hv, hr])

end ContinuumCoulomb.ContactRationalPlaceProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_ContactPlacedGadgetProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A source-edge record contains the original integer endpoints and the
nineteen calibrated lengths. The whole local coordinate list is computed
by the same orientation and height routines used in the geometric proof. -/

noncomputable section
namespace ContinuumCoulomb.ContactPlacedGadgetProgram
open ExactQuantumFactoring.BitStackProgram

def inputCode : Input → List Bool :=
  prodCode ContactCanonicalEdgeProgram.inputCode ContactRationalGadget.inputCode

def position (x : Input) (s : ContactGadgetSite) : ℚ × ℚ :=
  ContactRationalGlobal.rationalPlace (placement x) (ContactRationalGadget.position x.2 s)

noncomputable opaque placementProgram : Procedure inputCode ContactCanonicalEdgeProgram.edgeCode
    placement := ContactCanonicalEdgeProgram.program.comp
      (Procedure.first ContactCanonicalEdgeProgram.inputCode ContactRationalGadget.inputCode)

noncomputable opaque gadgetProgram : Procedure inputCode ContactRationalGadget.inputCode Prod.snd :=
  Procedure.second ContactCanonicalEdgeProgram.inputCode ContactRationalGadget.inputCode

noncomputable opaque positionProgram (s : ContactGadgetSite) :
    Procedure inputCode ContactRationalGadget.pointCode (fun x => position x s) :=
  ContactRationalPlaceProgram.program.comp
    (placementProgram.pair ((ContactRationalGadget.positionProgram s).comp gadgetProgram))

noncomputable def pointListProgram : (ss : List ContactGadgetSite) →
    Procedure inputCode (listCode ContactRationalGadget.pointCode)
      (fun x => ss.map (position x))
  | [] => (Procedure.constant inputCode (listCode ContactRationalGadget.pointCode) []).congrFun
      (by intro x; rfl)
  | s :: ss => ((Procedure.listCons ContactRationalGadget.pointCode).comp
      ((positionProgram s).pair (pointListProgram ss))).congrFun (by intro x; rfl)

end ContinuumCoulomb.ContactPlacedGadgetProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_ContactGeometryBlockProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform polynomial-time serialization of the actual mediator vertex
blocks: old vertices, first sites, second sites, and the two third-site
blocks. The static local labels agree with `ContactMediator.encodeSite`. -/

noncomputable section
namespace ContinuumCoulomb.ContactGeometryBlockProgram
open ExactQuantumFactoring.BitStackProgram ContactMediator

def pointCode : (ℚ × ℚ) → List Bool := ContactRationalGadget.pointCode

def block (ss : List ContactGadgetSite) (xs : List EdgeInput) : List (ℚ × ℚ) :=
  (List.range (ss.length * xs.length)).map fun i =>
    ((ss.map (ContactPlacedGadgetProgram.position
      ((xs.drop (i / ss.length)).headD defaultEdge))).drop (i % ss.length)).headD (0, 0)

def loopCode : LoopInput → List Bool :=
  prodCode unaryCode (listCode ContactPlacedGadgetProgram.inputCode)

noncomputable opaque indexProgram : Procedure loopCode Nat.bits (fun x => x.1) :=
  Procedure.unaryToBits.comp (Procedure.first unaryCode _)

noncomputable opaque edgesProgram : Procedure loopCode
    (listCode ContactPlacedGadgetProgram.inputCode) Prod.snd := Procedure.second unaryCode _

noncomputable opaque quotientProgram (n : ℕ) : Procedure loopCode Nat.bits
    (fun x => x.1 / n) := Procedure.binaryDiv.comp
      (indexProgram.pair (Procedure.constant loopCode Nat.bits n))

noncomputable opaque remainderProgram (n : ℕ) : Procedure loopCode Nat.bits
    (fun x => x.1 % n) := Procedure.binaryMod.comp
      (indexProgram.pair (Procedure.constant loopCode Nat.bits n))

noncomputable opaque edgeProgram (n : ℕ) : Procedure loopCode ContactPlacedGadgetProgram.inputCode
    (fun x => (x.2.drop (x.1 / n)).headD defaultEdge) :=
  (Procedure.listGet ContactPlacedGadgetProgram.inputCode defaultEdge).comp
    ((quotientProgram n).pair edgesProgram)

noncomputable opaque pointListProgram (ss : List ContactGadgetSite) : Procedure loopCode
    (listCode pointCode) (fun x => ss.map (ContactPlacedGadgetProgram.position
      ((x.2.drop (x.1 / ss.length)).headD defaultEdge))) :=
  (ContactPlacedGadgetProgram.pointListProgram ss).comp (edgeProgram ss.length)

noncomputable opaque stepProgram (ss : List ContactGadgetSite) : Procedure loopCode pointCode
    (fun x => ((ss.map (ContactPlacedGadgetProgram.position
      ((x.2.drop (x.1 / ss.length)).headD defaultEdge))).drop (x.1 % ss.length)).headD (0, 0)) :=
  (Procedure.listGet pointCode (0, 0)).comp
    ((remainderProgram ss.length).pair (pointListProgram ss))

noncomputable opaque blockProgram (ss : List ContactGadgetSite) :
    Procedure (listCode ContactPlacedGadgetProgram.inputCode) (listCode pointCode) (block ss) := by
  let len := ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength
    ContactPlacedGadgetProgram.inputCode defaultEdge
  let count := (CoulombEvaluation.scaleProgram ss.length).comp len
  exact ((Procedure.tabulate (ea := listCode ContactPlacedGadgetProgram.inputCode)
    (eb := pointCode) (f := fun xs i =>
      ((ss.map (ContactPlacedGadgetProgram.position
        ((xs.drop (i / ss.length)).headD defaultEdge))).drop (i % ss.length)).headD (0, 0))
      (0, 0) (stepProgram ss)).comp
        (count.pair (Procedure.identity (listCode ContactPlacedGadgetProgram.inputCode)))).congrFun
          (by intro xs; rfl)

noncomputable opaque oldPointProgram : Procedure ContactCanonicalEdgeProgram.latticeCode
    pointCode oldPoint := by
  let x := Procedure.intToRat.comp (Procedure.first intCode intCode)
  let y := Procedure.intToRat.comp (Procedure.second intCode intCode)
  exact (Procedure.ratMul.comp
    ((Procedure.constant ContactCanonicalEdgeProgram.latticeCode ratCode 17).pair x)).pair
      (Procedure.ratMul.comp
        ((Procedure.constant ContactCanonicalEdgeProgram.latticeCode ratCode 17).pair y))

def inputCode : Input → List Bool :=
  prodCode (listCode ContactCanonicalEdgeProgram.latticeCode)
    (listCode ContactPlacedGadgetProgram.inputCode)

def positions (x : Input) : List (ℚ × ℚ) :=
  x.1.map oldPoint ++ block firstSites x.2 ++ block secondSites x.2 ++
    block thirdFirstSites x.2 ++ block thirdSecondSites x.2

noncomputable opaque oldProgram : Procedure inputCode (listCode pointCode)
    (fun x => x.1.map oldPoint) :=
  (Procedure.listMap (0, 0) (0, 0) oldPointProgram).comp (Procedure.first _ _)

noncomputable opaque listProgram (ss : List ContactGadgetSite) :
    Procedure inputCode (listCode pointCode) (fun x => block ss x.2) :=
  (blockProgram ss).comp (Procedure.second _ _)

noncomputable opaque program : Procedure inputCode (listCode pointCode) positions := by
  let append := Procedure.listAppend pointCode (0, 0)
  let a := append.comp (oldProgram.pair (listProgram firstSites))
  let b := append.comp (a.pair (listProgram secondSites))
  let c := append.comp (b.pair (listProgram thirdFirstSites))
  exact (append.comp (c.pair (listProgram thirdSecondSites))).congrFun
    (by intro x; simp only [positions, Function.comp_apply, List.append_assoc])

end ContinuumCoulomb.ContactGeometryBlockProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_ContactEdgeNumberProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Each fixed local edge has an explicit polynomial-time global lookup
index, with the original source edge index retained. -/

namespace ContinuumCoulomb.ContactEdgeNumberProgram
open ExactQuantumFactoring.BitStackProgram ContactMediator

def inputCode : Input → List Bool := prodCode unaryCode unaryCode

noncomputable opaque rProgram : Procedure inputCode Nat.bits Prod.fst :=
  Procedure.unaryToBits.comp (Procedure.first unaryCode unaryCode)

noncomputable opaque eProgram : Procedure inputCode Nat.bits Prod.snd :=
  Procedure.unaryToBits.comp (Procedure.second unaryCode unaryCode)

noncomputable opaque twiceRProgram : Procedure inputCode Nat.bits (fun x => x.1 * 2) :=
  Procedure.binaryMul.comp (rProgram.pair (Procedure.constant inputCode Nat.bits 2))

noncomputable opaque twiceEProgram : Procedure inputCode Nat.bits (fun x => x.2 * 2) :=
  Procedure.binaryMul.comp (eProgram.pair (Procedure.constant inputCode Nat.bits 2))

noncomputable def pathProgram : (p : LocalPath) →
    Procedure inputCode Nat.bits (fun x => pathNumber x.1 x.2 p)
  | Sum.inl s => Procedure.binaryAdd.comp
      (twiceEProgram.pair (Procedure.constant inputCode Nat.bits s.val))
  | Sum.inr (s, t) =>
      let a := Procedure.binaryAdd.comp
        (twiceEProgram.pair (Procedure.constant inputCode Nat.bits s.val))
      let b := Procedure.binaryMul.comp (a.pair (Procedure.constant inputCode Nat.bits 2))
      let c := Procedure.binaryAdd.comp (twiceRProgram.pair b)
      Procedure.binaryAdd.comp (c.pair (Procedure.constant inputCode Nat.bits t.val))

noncomputable opaque pathCountProgram : Procedure inputCode Nat.bits
    (fun x => x.1 * 2 + x.1 * 2 * 2) :=
  Procedure.binaryAdd.comp (twiceRProgram.pair
    (Procedure.binaryMul.comp (twiceRProgram.pair (Procedure.constant inputCode Nat.bits 2))))

noncomputable def edgeProgram : (a : LocalEdge) →
    Procedure inputCode Nat.bits (fun x => edgeNumber x.1 x.2 a)
  | Sum.inl _ => eProgram
  | Sum.inr (Sum.inl p) => Procedure.binaryAdd.comp (rProgram.pair (pathProgram p))
  | Sum.inr (Sum.inr (p, t)) =>
      let base := Procedure.binaryAdd.comp (rProgram.pair pathCountProgram)
      let twice := Procedure.binaryMul.comp
        ((pathProgram p).pair (Procedure.constant inputCode Nat.bits 2))
      let b := Procedure.binaryAdd.comp (base.pair twice)
      Procedure.binaryAdd.comp (b.pair (Procedure.constant inputCode Nat.bits t.val))

end ContinuumCoulomb.ContactEdgeNumberProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_ContactLocalInputProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extract the exact nineteen local lengths from the calibrated final-edge
array. Runtime indices are the proved natural formulas for `encodeEdge`. -/

namespace ContinuumCoulomb.ContactLocalInputProgram
open ExactQuantumFactoring.BitStackProgram ContactMediator

def inputCode : Input → List Bool := prodCode unaryCode
  (prodCode unaryCode (prodCode unaryCode (prodCode Procedure.boolCode (listCode ratCode))))

noncomputable opaque precisionProgram : Procedure inputCode unaryCode Prod.fst :=
  Procedure.first unaryCode _

noncomputable opaque tailProgram : Procedure inputCode
    (prodCode unaryCode (prodCode unaryCode (prodCode Procedure.boolCode (listCode ratCode))))
    Prod.snd := Procedure.second unaryCode _

noncomputable opaque countProgram : Procedure inputCode unaryCode (fun x => x.2.1) :=
  (Procedure.first unaryCode _).comp tailProgram

noncomputable opaque restProgram : Procedure inputCode
    (prodCode unaryCode (prodCode Procedure.boolCode (listCode ratCode))) (fun x => x.2.2) :=
  (Procedure.second unaryCode _).comp tailProgram

noncomputable opaque indexProgram : Procedure inputCode unaryCode (fun x => x.2.2.1) :=
  (Procedure.first unaryCode _).comp restProgram

noncomputable opaque lastProgram : Procedure inputCode
    (prodCode Procedure.boolCode (listCode ratCode)) (fun x => x.2.2.2) :=
  (Procedure.second unaryCode _).comp restProgram

noncomputable opaque signProgram : Procedure inputCode Procedure.boolCode (fun x => x.2.2.2.1) :=
  (Procedure.first Procedure.boolCode (listCode ratCode)).comp lastProgram

noncomputable opaque valuesProgram : Procedure inputCode (listCode ratCode) (fun x => x.2.2.2.2) :=
  (Procedure.second Procedure.boolCode (listCode ratCode)).comp lastProgram

noncomputable opaque lookupProgram (a : LocalEdge) : Procedure inputCode ratCode (fun x => lookup x a) :=
  (Procedure.listGet ratCode 1).comp
    (((ContactEdgeNumberProgram.edgeProgram a).comp (countProgram.pair indexProgram)).pair valuesProgram)

noncomputable def valuesListProgram : (as : List LocalEdge) →
    Procedure inputCode (listCode ratCode) (fun x => as.map (lookup x))
  | [] => (Procedure.constant inputCode (listCode ratCode) []).congrFun (by intro x; rfl)
  | a :: as => ((Procedure.listCons ratCode).comp
      ((lookupProgram a).pair (valuesListProgram as))).congrFun (by intro x; rfl)

noncomputable opaque leftProgram : Procedure inputCode (listCode ratCode)
    (fun x => List.ofFn (fun k : Fin 9 => lookup x (leftEdge k))) :=
  (valuesListProgram (List.ofFn leftEdge)).congrFun (by
    intro x
    simp only [List.map_ofFn, Function.comp_def])

noncomputable opaque rightProgram : Procedure inputCode (listCode ratCode)
    (fun x => List.ofFn (fun k : Fin 9 => lookup x (rightEdge k))) :=
  (valuesListProgram (List.ofFn rightEdge)).congrFun (by
    intro x
    simp only [List.map_ofFn, Function.comp_def])

noncomputable opaque program : Procedure inputCode ContactRationalGadget.inputCode record :=
  precisionProgram.pair (signProgram.pair
    ((lookupProgram (Sum.inl ())).pair (leftProgram.pair rightProgram)))

end ContinuumCoulomb.ContactLocalInputProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_ContactSourceInputProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal polynomial-time program turns the source coordinate/bond
lists and calibrated final-edge lengths into all rational contact sites. -/

noncomputable section
namespace ContinuumCoulomb.ContactSourceInputProgram
open ExactQuantumFactoring.BitStackProgram

def inputCode : Input → List Bool := prodCode unaryCode
  (prodCode (listCode ContactCanonicalEdgeProgram.latticeCode)
    (prodCode (listCode MediatorListProgram.bondCode) (listCode ratCode)))

def loopCode : LoopInput → List Bool := prodCode unaryCode inputCode

def positions (x : Input) : List (ℚ × ℚ) :=
  ContactGeometryBlockProgram.positions (x.2.1, edges x)

noncomputable opaque indexProgram : Procedure loopCode unaryCode Prod.fst :=
  Procedure.first unaryCode inputCode

noncomputable opaque inputProgram : Procedure loopCode inputCode Prod.snd :=
  Procedure.second unaryCode inputCode

noncomputable opaque precisionProgram : Procedure loopCode unaryCode (fun x => x.2.1) :=
  (Procedure.first unaryCode _).comp inputProgram

noncomputable opaque dataProgram : Procedure loopCode
    (prodCode (listCode ContactCanonicalEdgeProgram.latticeCode)
      (prodCode (listCode MediatorListProgram.bondCode) (listCode ratCode))) (fun x => x.2.2) :=
  (Procedure.second unaryCode _).comp inputProgram

noncomputable opaque coordinatesProgram : Procedure loopCode
    (listCode ContactCanonicalEdgeProgram.latticeCode) (fun x => x.2.2.1) :=
  (Procedure.first _ _).comp dataProgram

noncomputable opaque listsProgram : Procedure loopCode
    (prodCode (listCode MediatorListProgram.bondCode) (listCode ratCode)) (fun x => x.2.2.2) :=
  (Procedure.second _ _).comp dataProgram

noncomputable opaque bondsProgram : Procedure loopCode
    (listCode MediatorListProgram.bondCode) (fun x => x.2.2.2.1) :=
  (Procedure.first _ _).comp listsProgram

noncomputable opaque lengthsProgram : Procedure loopCode (listCode ratCode) (fun x => x.2.2.2.2) :=
  (Procedure.second _ _).comp listsProgram

noncomputable opaque countProgram : Procedure loopCode unaryCode (fun x => x.2.2.2.1.length) :=
  (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength
    MediatorListProgram.bondCode MediatorListProgram.zeroBond).comp bondsProgram

noncomputable opaque bondProgram : Procedure loopCode MediatorListProgram.bondCode bond :=
  (Procedure.listGet MediatorListProgram.bondCode MediatorListProgram.zeroBond).comp
    ((Procedure.unaryToBits.comp indexProgram).pair bondsProgram)

noncomputable opaque leftIndexProgram : Procedure loopCode Nat.bits (fun x => (bond x).1) :=
  (Procedure.first Nat.bits (prodCode Nat.bits ratCode)).comp bondProgram

noncomputable opaque bondTailProgram : Procedure loopCode (prodCode Nat.bits ratCode)
    (fun x => (bond x).2) := (Procedure.second Nat.bits _).comp bondProgram

noncomputable opaque rightIndexProgram : Procedure loopCode Nat.bits (fun x => (bond x).2.1) :=
  (Procedure.first Nat.bits ratCode).comp bondTailProgram

noncomputable opaque weightProgram : Procedure loopCode ratCode (fun x => (bond x).2.2) :=
  (Procedure.second Nat.bits ratCode).comp bondTailProgram

noncomputable opaque signProgram : Procedure loopCode Procedure.boolCode
    (fun x => decide ((bond x).2.2 < 0)) :=
  (Procedure.intSign.comp (Procedure.ratNum.comp weightProgram)).congrFun (by
    intro x
    simp only [Function.comp_apply, Rat.num_neg])

noncomputable opaque leftProgram : Procedure loopCode ContactCanonicalEdgeProgram.latticeCode
    (fun x => (x.2.2.1.drop (bond x).1).headD (0, 0)) :=
  (Procedure.listGet ContactCanonicalEdgeProgram.latticeCode (0, 0)).comp
    (leftIndexProgram.pair coordinatesProgram)

noncomputable opaque rightProgram : Procedure loopCode ContactCanonicalEdgeProgram.latticeCode
    (fun x => (x.2.2.1.drop (bond x).2.1).headD (0, 0)) :=
  (Procedure.listGet ContactCanonicalEdgeProgram.latticeCode (0, 0)).comp
    (rightIndexProgram.pair coordinatesProgram)

noncomputable opaque localProgram : Procedure loopCode ContactRationalGadget.inputCode
    (fun x => ContactLocalInputProgram.record (x.2.1, (x.2.2.2.1.length,
      (x.1, (decide ((bond x).2.2 < 0), x.2.2.2.2))))) :=
  ContactLocalInputProgram.program.comp (precisionProgram.pair
    (countProgram.pair (indexProgram.pair (signProgram.pair lengthsProgram))))

noncomputable opaque edgeProgram : Procedure loopCode ContactPlacedGadgetProgram.inputCode edge :=
  (leftProgram.pair rightProgram).pair localProgram

noncomputable opaque edgesProgram : Procedure inputCode
    (listCode ContactPlacedGadgetProgram.inputCode) edges := by
  let lists : Procedure inputCode
      (prodCode (listCode MediatorListProgram.bondCode) (listCode ratCode))
      (fun x => x.2.2) := (Procedure.second _ _).comp (Procedure.second unaryCode _)
  let bonds := (Procedure.first (listCode MediatorListProgram.bondCode) (listCode ratCode)).comp lists
  let count := (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength
    MediatorListProgram.bondCode MediatorListProgram.zeroBond).comp bonds
  exact ((Procedure.tabulate (ea := inputCode) (eb := ContactPlacedGadgetProgram.inputCode)
    (f := fun x i => edge (i, x)) ContactGeometryBlockProgram.defaultEdge edgeProgram).comp
      (count.pair (Procedure.identity inputCode))).congrFun (by intro x; rfl)

noncomputable opaque program : Procedure inputCode
    (listCode ContactRationalGadget.pointCode) positions :=
  ContactGeometryBlockProgram.program.comp
    (((Procedure.first _ _).comp (Procedure.second unaryCode _)).pair edgesProgram)

def scaledInputCode : (ℚ × Input) → List Bool := prodCode ratCode inputCode

noncomputable opaque scalePointProgram : Procedure
    (prodCode ratCode ContactRationalGadget.pointCode) ContactRationalGadget.pointCode scalePoint := by
  let q := Procedure.first ratCode ContactRationalGadget.pointCode
  let p := Procedure.second ratCode ContactRationalGadget.pointCode
  let a := (Procedure.first ratCode ratCode).comp p
  let b := (Procedure.second ratCode ratCode).comp p
  exact (Procedure.ratMul.comp (q.pair a)).pair (Procedure.ratMul.comp (q.pair b))

def scaledPositions (x : ℚ × Input) : List (ℚ × ℚ) :=
  (positions x.2).map (fun p => (x.1 * p.1, x.1 * p.2))

noncomputable opaque scaledProgram : Procedure scaledInputCode
    (listCode ContactRationalGadget.pointCode) scaledPositions :=
  (Procedure.listMapWith (ea := ratCode) (eb := ContactRationalGadget.pointCode)
    (ec := ContactRationalGadget.pointCode) (f := fun q p => (q * p.1, q * p.2))
      (0, 0) (0, 0) scalePointProgram).comp
        ((Procedure.first ratCode inputCode).pair
          (program.comp (Procedure.second ratCode inputCode)))

end ContinuumCoulomb.ContactSourceInputProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_CalibratedBisectionProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One polynomial TM2 program selects both the internal precision and
the iteration count and runs the actual calibrated bisection. -/

namespace ContinuumCoulomb.CalibratedEvaluation
open ExactQuantumFactoring.BitStackProgram

def scheduledInputCode : ScheduledInput → List Bool :=
  prodCode environmentCode (prodCode ratCode ratCode)

noncomputable opaque envMetadataProgram : Procedure environmentCode
    (prodCode unaryCode unaryCode) Prod.fst :=
  Procedure.first (prodCode unaryCode unaryCode) (prodCode unaryCode (prodCode ratCode ratCode))
noncomputable opaque envParametersProgram : Procedure environmentCode
    (prodCode unaryCode (prodCode ratCode ratCode)) Prod.snd :=
  Procedure.second (prodCode unaryCode unaryCode) (prodCode unaryCode (prodCode ratCode ratCode))
noncomputable opaque envBoundProgram : Procedure environmentCode unaryCode (fun e => e.1.1) :=
  (Procedure.first unaryCode unaryCode).comp envMetadataProgram
noncomputable opaque envPrecisionProgram : Procedure environmentCode unaryCode (fun e => e.1.2) :=
  (Procedure.second unaryCode unaryCode).comp envMetadataProgram
noncomputable opaque envScaleProgram : Procedure environmentCode unaryCode (fun e => e.2.1) :=
  (Procedure.first unaryCode (prodCode ratCode ratCode)).comp envParametersProgram

noncomputable opaque refinedEnvironmentProgram : Procedure environmentCode environmentCode
    refinedEnvironment :=
  (envBoundProgram.pair
    (((CoulombEvaluation.scaleProgram 8).comp Procedure.unarySuccessor).comp envPrecisionProgram)).pair
      envParametersProgram

noncomputable opaque firstIterationFactorProgram (rho : ℕ) : Procedure environmentCode unaryCode
    (fun e => 16 * lipschitzGuard rho * (e.2.1 + e.1.1 + 1)) := by
  let sum := ResolventSchedule.addProgram.comp (envScaleProgram.pair envBoundProgram)
  let suc := Procedure.unarySuccessor.comp sum
  exact ((CoulombEvaluation.scaleProgram (16 * lipschitzGuard rho)).comp suc).congrFun
    (by intro e; rfl)

noncomputable opaque secondIterationFactorProgram (rho : ℕ) : Procedure environmentCode unaryCode
    (fun e => 16 * lipschitzGuard rho * (e.2.1 + e.1.1 + 1) * (e.1.1 + 1)) :=
  (ResolventSchedule.mulProgram.comp ((firstIterationFactorProgram rho).pair
    (Procedure.unarySuccessor.comp envBoundProgram))).congrFun (by intro e; rfl)

noncomputable opaque iterationsProgram (rho : ℕ) : Procedure environmentCode unaryCode
    (iterations rho) :=
  (ResolventSchedule.mulProgram.comp ((secondIterationFactorProgram rho).pair
    (Procedure.unarySuccessor.comp envPrecisionProgram))).congrFun (by intro e; rfl)

noncomputable opaque scheduledArgumentProgram (rho : ℕ) : Procedure scheduledInputCode
    bisectionInputCode (fun x => (iterations rho x.1, (refinedEnvironment x.1, x.2))) := by
  let e := Procedure.first environmentCode (prodCode ratCode ratCode)
  let ends := Procedure.second environmentCode (prodCode ratCode ratCode)
  exact ((iterationsProgram rho).comp e).pair
    ((refinedEnvironmentProgram.comp e).pair ends)

noncomputable opaque scheduledProgram (rho : ℕ) : Procedure scheduledInputCode ratCode
    (fun x => scheduledValue rho x.1 x.2.1 x.2.2) :=
  ((bisectionProgram rho).comp (scheduledArgumentProgram rho)).congrFun (by intro x; rfl)

end ContinuumCoulomb.CalibratedEvaluation

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_RationalLogScaleProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The logarithmic scale is computed from a binary power and a literal
bit-counting machine. Its fixed rational multiplier is independent of the
input instance. -/

namespace ContinuumCoulomb.RationalLogScale
open ExactQuantumFactoring.BitStackProgram

noncomputable opaque powerProgram (k : ℕ) : Procedure unaryCode Nat.bits
    (fun N => N ^ k) :=
  Procedure.binaryPow.comp
    ((Procedure.constant unaryCode unaryCode k).pair Procedure.unaryToBits)

noncomputable opaque bitLengthProgram (k : ℕ) : Procedure unaryCode unaryCode
    (fun N => (N ^ k).bits.length) :=
  (Procedure.length.precompose Nat.bits).comp (powerProgram k)

noncomputable opaque bitLengthRationalProgram (k : ℕ) : Procedure unaryCode ratCode
    (fun N => ((N ^ k).bits.length : ℚ)) :=
  Procedure.natToRat.comp (Procedure.unaryToBits.comp (bitLengthProgram k))

noncomputable opaque program (c : ℚ) (k : ℕ) : Procedure unaryCode ratCode (value c k) :=
  Procedure.ratMul.comp
    ((Procedure.constant unaryCode ratCode c).pair (bitLengthRationalProgram k))

end ContinuumCoulomb.RationalLogScale

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_CalibrationRationalBracketProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal polynomial-time program returns both rational contact-search
endpoints from the unary instance-size parameter. -/

namespace ContinuumCoulomb.CalibrationRationalBracket
open ExactQuantumFactoring.BitStackProgram

noncomputable opaque leftProgram (ε c : ℚ) (k : ℕ) : Procedure unaryCode ratCode
    (fun N => (endpoints ε (RationalLogScale.value c k N)).1) :=
  Procedure.ratMul.comp
    ((Procedure.constant unaryCode ratCode (1 - ε / 2)).pair (RationalLogScale.program c k))

noncomputable opaque rightProgram (ε c : ℚ) (k : ℕ) : Procedure unaryCode ratCode
    (fun N => (endpoints ε (RationalLogScale.value c k N)).2) :=
  Procedure.ratMul.comp
    ((Procedure.constant unaryCode ratCode (1 + ε / 2)).pair (RationalLogScale.program c k))

noncomputable opaque program (ε c : ℚ) (k : ℕ) : Procedure unaryCode
    (prodCode ratCode ratCode) (fun N => endpoints ε (RationalLogScale.value c k N)) :=
  (leftProgram ε c k).pair (rightProgram ε c k)

end ContinuumCoulomb.CalibrationRationalBracket

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_AutomaticCalibrationParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Input and query bounds for the automatic calibrated-distance program.
The unary evaluator range is a fixed polynomial in the source size. -/

noncomputable section
namespace ContinuumCoulomb.AutomaticCalibration

def value (rho : ℕ) (ε c : ℚ) (k A B : ℕ) (x : Input) : ℚ :=
  CalibratedEvaluation.scheduledValue rho (environment k A B x)
    (interval ε c k x.1).1 (interval ε c k x.1).2

end ContinuumCoulomb.AutomaticCalibration

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_AutomaticCalibrationProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The automatic distance program computes its polynomial query bounds,
scale and inverse-power target from unary source size, then runs the
certified rational-interval calibrated bisection. -/

namespace ContinuumCoulomb.AutomaticCalibration
open ExactQuantumFactoring.BitStackProgram

def inputCode : Input → List Bool := prodCode unaryCode (prodCode unaryCode ratCode)

noncomputable def unaryPowerProgram : (k : ℕ) → Procedure unaryCode unaryCode (fun n => n ^ k)
  | 0 => Procedure.constant unaryCode unaryCode 1
  | k + 1 => (ResolventSchedule.mulProgram.comp
      ((unaryPowerProgram k).pair (Procedure.identity unaryCode))).congrFun
        (by intro n; simp only [Function.comp_apply, id_eq, pow_succ])

noncomputable opaque baseProgram : Procedure inputCode unaryCode Prod.fst :=
  Procedure.first unaryCode (prodCode unaryCode ratCode)

noncomputable opaque tailProgram : Procedure inputCode (prodCode unaryCode ratCode) Prod.snd :=
  Procedure.second unaryCode (prodCode unaryCode ratCode)

noncomputable opaque precisionProgram : Procedure inputCode unaryCode (fun x => x.2.1) :=
  (Procedure.first unaryCode ratCode).comp tailProgram

noncomputable opaque coefficientProgram : Procedure inputCode ratCode (fun x => x.2.2) :=
  (Procedure.second unaryCode ratCode).comp tailProgram

noncomputable opaque scaledSizeProgram (k : ℕ) : Procedure inputCode unaryCode
    (fun x => 2 * k * x.1) := (CoulombEvaluation.scaleProgram (2 * k)).comp baseProgram

noncomputable opaque queryProgram (k A : ℕ) : Procedure inputCode unaryCode
    (fun x => queryBound k A x.1) :=
  Procedure.unarySuccessor.comp (ResolventSchedule.addProgram.comp
    ((scaledSizeProgram k).pair ((unaryPowerProgram A).comp baseProgram)))

noncomputable opaque scaleProgram (k : ℕ) : Procedure inputCode unaryCode
    (fun x => x.1 ^ k) := (unaryPowerProgram k).comp baseProgram

noncomputable opaque targetScaleProgram (B : ℕ) : Procedure inputCode ratCode
    (fun x => ((x.1 ^ B : ℕ) : ℚ)⁻¹) :=
  Procedure.ratInv.comp (Procedure.natToRat.comp
    (Procedure.unaryToBits.comp ((unaryPowerProgram B).comp baseProgram)))

noncomputable opaque environmentProgram (k A B : ℕ) : Procedure inputCode
    CalibratedEvaluation.environmentCode (environment k A B) :=
  ((queryProgram k A).pair precisionProgram).pair
    ((scaleProgram k).pair ((targetScaleProgram B).pair coefficientProgram))

noncomputable opaque intervalProgram (ε c : ℚ) (k : ℕ) : Procedure inputCode
    (prodCode ratCode ratCode) (fun x => interval ε c k x.1) :=
  (CalibrationRationalBracket.program ε c k).comp baseProgram

noncomputable opaque argumentProgram (ε c : ℚ) (k A B : ℕ) : Procedure inputCode
    CalibratedEvaluation.scheduledInputCode
      (fun x => (environment k A B x, interval ε c k x.1)) :=
  (environmentProgram k A B).pair (intervalProgram ε c k)

noncomputable opaque program (rho : ℕ) (ε c : ℚ) (k A B : ℕ) : Procedure inputCode ratCode
    (value rho ε c k A B) :=
  ((CalibratedEvaluation.scheduledProgram rho).comp (argumentProgram ε c k A B)).congrFun
    (by intro x; rfl)

end ContinuumCoulomb.AutomaticCalibration

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_AutomaticCalibrationNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The very same rational scale used by the search gives the rational
near-unit lengths supplied to the contact-coordinate program. -/

noncomputable section
namespace ContinuumCoulomb.AutomaticCalibration
open ExactQuantumFactoring.BitStackProgram

def normalizedValue (rho : ℕ) (ε c : ℚ) (k A B : ℕ) (x : Input) : ℚ :=
  value rho ε c k A B x / spacing c k x.1

noncomputable opaque spacingProgram (c : ℚ) (k : ℕ) : Procedure inputCode ratCode
    (fun x => spacing c k x.1) := (RationalLogScale.program c k).comp baseProgram

noncomputable opaque normalizedProgram (rho : ℕ) (ε c : ℚ) (k A B : ℕ) :
    Procedure inputCode ratCode (normalizedValue rho ε c k A B) :=
  (Procedure.ratMul.comp ((program rho ε c k A B).pair
    (Procedure.ratInv.comp (spacingProgram c k)))).congrFun
      (by intro x; simp only [Function.comp_apply, normalizedValue, div_eq_mul_inv])

end ContinuumCoulomb.AutomaticCalibration

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_AutomaticCalibrationList
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! All edges share one fixed calibration program and one rational
spacing. Mapping that program over the edge coefficients retains a
polynomial running time in the complete encoded input. -/

noncomputable section
namespace ContinuumCoulomb.AutomaticCalibrationList
open ExactQuantumFactoring.BitStackProgram

def environmentCode : Environment → List Bool := prodCode unaryCode unaryCode

def inputCode : Input → List Bool := prodCode environmentCode (listCode ratCode)

def value (rho : ℕ) (ε c : ℚ) (k A B : ℕ) (x : Input) : List ℚ :=
  x.2.map (fun K => AutomaticCalibration.normalizedValue rho ε c k A B (x.1.1, (x.1.2, K)))

noncomputable opaque elementProgram (rho : ℕ) (ε c : ℚ) (k A B : ℕ) :
    Procedure (prodCode environmentCode ratCode) ratCode
      (fun x => AutomaticCalibration.normalizedValue rho ε c k A B (x.1.1, (x.1.2, x.2))) := by
  let env := Procedure.first environmentCode ratCode
  let n := (Procedure.first unaryCode unaryCode).comp env
  let p := (Procedure.second unaryCode unaryCode).comp env
  let coefficient := Procedure.second environmentCode ratCode
  exact (AutomaticCalibration.normalizedProgram rho ε c k A B).comp
    (n.pair (p.pair coefficient))

noncomputable opaque program (rho : ℕ) (ε c : ℚ) (k A B : ℕ) :
    Procedure inputCode (listCode ratCode) (value rho ε c k A B) :=
  Procedure.listMapWith (ea := environmentCode) (eb := ratCode) (ec := ratCode)
    (f := fun e K => AutomaticCalibration.normalizedValue rho ε c k A B (e.1, (e.2, K)))
      0 0 (elementProgram rho ε c k A B)

end ContinuumCoulomb.AutomaticCalibrationList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_CalibratedContactProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One literal polynomial-time map from source arrays and target edge
coefficients to the physically scaled rational contact coordinates. -/

noncomputable section
namespace ContinuumCoulomb.CalibratedContactProgram
open ExactQuantumFactoring.BitStackProgram

def dataCode : Data → List Bool :=
  prodCode (listCode ContactCanonicalEdgeProgram.latticeCode)
    (prodCode (listCode MediatorListProgram.bondCode) (listCode ratCode))

def inputCode : Input → List Bool :=
  prodCode unaryCode (prodCode AutomaticCalibrationList.environmentCode dataCode)

def rawInput (rho : ℕ) (ε c : ℚ) (k A B : ℕ) (x : Input) : ContactSourceInputProgram.Input :=
  (x.1, (x.2.2.1, (x.2.2.2.1,
    AutomaticCalibrationList.value rho ε c k A B (x.2.1, x.2.2.2.2))))

def value (rho : ℕ) (ε c : ℚ) (k A B : ℕ) (x : Input) : List (ℚ × ℚ) :=
  ContactSourceInputProgram.scaledPositions
    (AutomaticCalibration.spacing c k x.2.1.1, rawInput rho ε c k A B x)

noncomputable opaque precisionProgram : Procedure inputCode unaryCode Prod.fst :=
  Procedure.first unaryCode _

noncomputable opaque restProgram : Procedure inputCode
    (prodCode AutomaticCalibrationList.environmentCode dataCode) Prod.snd := Procedure.second unaryCode _

noncomputable opaque environmentProgram : Procedure inputCode
    AutomaticCalibrationList.environmentCode (fun x => x.2.1) :=
  (Procedure.first AutomaticCalibrationList.environmentCode dataCode).comp restProgram

noncomputable opaque dataProgram : Procedure inputCode dataCode (fun x => x.2.2) :=
  (Procedure.second AutomaticCalibrationList.environmentCode dataCode).comp restProgram

noncomputable opaque coordinatesProgram : Procedure inputCode
    (listCode ContactCanonicalEdgeProgram.latticeCode) (fun x => x.2.2.1) :=
  (Procedure.first _ _).comp dataProgram

noncomputable opaque listsProgram : Procedure inputCode
    (prodCode (listCode MediatorListProgram.bondCode) (listCode ratCode)) (fun x => x.2.2.2) :=
  (Procedure.second _ _).comp dataProgram

noncomputable opaque bondsProgram : Procedure inputCode
    (listCode MediatorListProgram.bondCode) (fun x => x.2.2.2.1) :=
  (Procedure.first _ _).comp listsProgram

noncomputable opaque coefficientsProgram : Procedure inputCode (listCode ratCode)
    (fun x => x.2.2.2.2) := (Procedure.second _ _).comp listsProgram

noncomputable opaque lengthsProgram (rho : ℕ) (ε c : ℚ) (k A B : ℕ) :
    Procedure inputCode (listCode ratCode)
      (fun x => AutomaticCalibrationList.value rho ε c k A B (x.2.1, x.2.2.2.2)) :=
  (AutomaticCalibrationList.program rho ε c k A B).comp
    (environmentProgram.pair coefficientsProgram)

noncomputable opaque rawProgram (rho : ℕ) (ε c : ℚ) (k A B : ℕ) :
    Procedure inputCode ContactSourceInputProgram.inputCode (rawInput rho ε c k A B) :=
  precisionProgram.pair (coordinatesProgram.pair
    (bondsProgram.pair (lengthsProgram rho ε c k A B)))

noncomputable opaque spacingProgram (c : ℚ) (k : ℕ) : Procedure inputCode ratCode
    (fun x => AutomaticCalibration.spacing c k x.2.1.1) :=
  (RationalLogScale.program c k).comp
    ((Procedure.first unaryCode unaryCode).comp environmentProgram)

noncomputable opaque program (rho : ℕ) (ε c : ℚ) (k A B : ℕ) :
    Procedure inputCode (listCode ContactRationalGadget.pointCode) (value rho ε c k A B) :=
  ContactSourceInputProgram.scaledProgram.comp
    ((spacingProgram c k).pair (rawProgram rho ε c k A B))

end ContinuumCoulomb.CalibratedContactProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CalibratedContactCorrectness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The composed numerical program outputs the actual rational geometric
realization of the final mediator graph, in its original vertex order. -/

noncomputable section
namespace ContinuumCoulomb.CalibratedContactProgram
open ContactMediator

def graphLengths (rho : ℕ) (ε c : ℚ) (k A B N P : ℕ)
    (d : SquareLatticeHeisenberg) (K : GlobalEdge d → ℚ) : GlobalEdge d → ℚ :=
  fun a => AutomaticCalibration.normalizedValue rho ε c k A B (N, (P, K a))

end ContinuumCoulomb.CalibratedContactProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CenteredGaussEquiv
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The emitted centered label list is exactly the finite cell-by-eight-node
grid used by the Coulomb quadrature theorems. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb.CenteredGaussLabels

abbrev Grid (r : Radii) :=
  {k // k ∈ centeredGridIndices (radiiVector r)} × (Fin 3 → Fin 2)

def restrictedEquiv (r : Radii) : {l // l ∈ labels r} ≃ Grid r where
  toFun l := (⟨(indexEquiv l.val).1,(mem_labels r l.val).mp l.property⟩,(indexEquiv l.val).2)
  invFun kv := ⟨decode (kv.1.val,kv.2),(mem_labels r _).mpr (by
    rw [index_decode]
    exact kv.1.property)⟩
  left_inv l := Subtype.ext (decode_index l.val)
  right_inv kv := by
    have he := index_decode (kv.1.val,kv.2)
    have h1 : (indexEquiv (decode (kv.1.val,kv.2))).1 = kv.1.val :=
      congrArg (fun p : GaussLatticeIndex => p.1) he
    have h2 : (indexEquiv (decode (kv.1.val,kv.2))).2 = kv.2 :=
      congrArg (fun p : GaussLatticeIndex => p.2) he
    exact Prod.ext (Subtype.ext h1) h2

def enumerationEquiv (r : Radii) : Fin (labels r).length ≃ Grid r :=
  (List.Nodup.getEquiv (labels r) (labels_nodup r)).trans (restrictedEquiv r)

@[simp] theorem enumeration_first (r : Radii) (a : Fin (labels r).length) :
    (enumerationEquiv r a).1.val = (RationalGaussNodes.index ((labels r).get a).1 ((labels r).get a).2).1 := rfl

@[simp] theorem enumeration_second (r : Radii) (a : Fin (labels r).length) :
    (enumerationEquiv r a).2 = (RationalGaussNodes.index ((labels r).get a).1 ((labels r).get a).2).2 := rfl

end ContinuumCoulomb.CenteredGaussLabels

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_EnumeratedGridNuclei
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The centered label list and the analytic finite grid describe the same
nuclear cloud, including after physical dilation. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

namespace CenteredGaussLabels

def nuclei (r : Radii) (G : Position → Position) (hG : Function.Injective G)
    {h : ℝ} (hh : 0 < h) : Coulomb.Nuclei (labels r).length where
  nonempty := by rw [labels_length]; positivity
  position a := G (gaussLatticePoint h (RationalGaussNodes.index ((labels r).get a).1 ((labels r).get a).2))
  distinct := by
    intro a b hab
    have he := gauss_point_injective hh (hG hab)
    apply (enumerationEquiv r).injective
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg (fun x : GaussLatticeIndex => x.1) he
    · exact congrArg (fun x : GaussLatticeIndex => x.2) he
  charge _ := 1
  charge_ge_one _ := le_rfl

end CenteredGaussLabels
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_SourceNormalizationProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual polynomial-time normalization of a literal source-bond list.
The input coefficient bound and inverse precision are unary metadata; the
rounding denominator uses the actual list length, and zero bonds are deleted. -/

namespace ContinuumCoulomb.SourceNormalizationProgram
open ExactQuantumFactoring.BitStackProgram MediatorListProgram

noncomputable opaque mul : Procedure (prodCode unaryCode unaryCode) unaryCode
    (fun x => x.1 * x.2) := Procedure.unaryMul

end ContinuumCoulomb.SourceNormalizationProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_SourceMetadataProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual source parser computes unary polynomial bounds from the raw
encoding length. No polynomial bound is supplied as an unverified oracle. -/

namespace ContinuumCoulomb.SourceMetadataProgram
open ExactQuantumFactoring.BitStackProgram MediatorListProgram

noncomputable opaque vertexCount : Procedure binaryHeisenbergCodec.encode unaryCode
    (fun d => d.coordinate.length) :=
  (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength
    SourcePrograms.coordinateCodec.encode (0, 0)).comp SourcePrograms.coordinates

end ContinuumCoulomb.SourceMetadataProgram

end OAI
end


