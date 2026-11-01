-- Prove2me | Definitions.Def_OAIQ092A001
-- name    : OAIQ092A001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T19:46:24.162005+00:00
-- url     : https://prove2.me/theorems/b1a2d3ef-c910-4f6b-89eb-abc6176c121e
-- title:
--   Definitions bundle OAIQ092A001 of the split of OpenAI, QMA-hardness of continuum Coulomb energy (result family 275)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ContinuumCoulomb.binary_coulomb_qmaHard` and `OAI.ContinuumCoulomb.unit_coulomb_qmaHard`, carved from OpenAI's openai/math development (OpenAI, *QMA-hardness of continuum Coulomb energy (result family 275)*, OpenAI Math Release, September 24, 2026, result family 275, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1116 declarations of OpenAI's Lean: 695 definitions, 23 inductive types or structures, 2 instances and 396 theorems. The definitions and types are `OAI.ContinuumCoulomb.ApproximateBisection.Interval`, `OAI.ContinuumCoulomb.ApproximateBisection.Invariant`, `OAI.ContinuumCoulomb.ApproximateBisection.initial`, `OAI.ContinuumCoulomb.ApproximateBisection.midpoint`, `OAI.ContinuumCoulomb.ApproximateBisection.run`, `OAI.ContinuumCoulomb.ApproximateBisection.step`, `OAI.ContinuumCoulomb.ApproximateBisection.width`, `OAI.ContinuumCoulomb.AutomaticCalibration.Input`, `OAI.ContinuumCoulomb.AutomaticCalibration.environment`, `OAI.ContinuumCoulomb.AutomaticCalibration.interval`, `OAI.ContinuumCoulomb.AutomaticCalibration.queryBound`, `OAI.ContinuumCoulomb.AutomaticCalibration.spacing`, `OAI.ContinuumCoulomb.AutomaticCalibrationList.Environment`, `OAI.ContinuumCoulomb.AutomaticCalibrationList.Input`, `OAI.ContinuumCoulomb.BinaryHeisenberg`, `OAI.ContinuumCoulomb.BinaryHeisenberg.PolynomialPromise`, `OAI.ContinuumCoulomb.BinaryHeisenberg.Valid`, `OAI.ContinuumCoulomb.BinaryHeisenberg.toSource`, `OAI.ContinuumCoulomb.BinaryHeisenbergEdge`, `OAI.ContinuumCoulomb.BinaryRational.ofRat`, `OAI.ContinuumCoulomb.BisectionProgram.Config`, `OAI.ContinuumCoulomb.BisectionProgram.Input`, `OAI.ContinuumCoulomb.BisectionProgram.advance`, `OAI.ContinuumCoulomb.BisectionProgram.approximate`, `OAI.ContinuumCoulomb.BisectionRegisters.Registers`, `OAI.ContinuumCoulomb.BisectionRegisters.bits`, `OAI.ContinuumCoulomb.BisectionRegisters.initial`, `OAI.ContinuumCoulomb.BisectionRegisters.interval`, `OAI.ContinuumCoulomb.BisectionRegisters.left`, `OAI.ContinuumCoulomb.BisectionRegisters.middle`, `OAI.ContinuumCoulomb.BisectionRegisters.right`, `OAI.ContinuumCoulomb.BisectionRegisters.step`, `OAI.ContinuumCoulomb.BoundedPotential.linear`, `OAI.ContinuumCoulomb.BoundedPotential.operator`, `OAI.ContinuumCoulomb.BoundedPotential.value`, `OAI.ContinuumCoulomb.CalibratedContactProgram.Data`, `OAI.ContinuumCoulomb.CalibratedContactProgram.Input`, `OAI.ContinuumCoulomb.CalibratedContactProgram.graphInput`, `OAI.ContinuumCoulomb.CalibratedEvaluation.BisectionInput`, `OAI.ContinuumCoulomb.CalibratedEvaluation.Environment` and 678 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, lean/OAI/Computability, lean/OAI/MathematicalPhysics, in whole or in part: `Analysis_FunctionalSpaces_Sobolev_Euclidean_H1`, `Analysis_FunctionalSpaces_Sobolev_Euclidean_Rellich`, `BiholderTransport_Regularity_UnitTime`, `ContinuumCoulomb_ManyBody_ChargePenalty`, `ContinuumCoulomb_ManyBody_FiniteSourceBranch`, `ContinuumCoulomb_ManyBody_FockBlocks`, `ContinuumCoulomb_ManyBody_FockChargePolynomial`, `ContinuumCoulomb_ManyBody_FockCoefficientNorm`, `ContinuumCoulomb_ManyBody_FockHubbardForm`, `ContinuumCoulomb_ManyBody_FockNorm`, `ContinuumCoulomb_ManyBody_FockSector`, `ContinuumCoulomb_ManyBody_FockSiteOneBody`, `ContinuumCoulomb_ManyBody_FockSlaterTensor`, `ContinuumCoulomb_ManyBody_FockTwoBodyContraction`, `ContinuumCoulomb_ManyBody_GlobalSinglet`, `ContinuumCoulomb_ManyBody_GlobalSuperexchange`, `ContinuumCoulomb_ManyBody_GramCorrection`, `ContinuumCoulomb_ManyBody_HalfFilledSector`, `ContinuumCoulomb_ManyBody_HubbardExcitation`, `ContinuumCoulomb_ManyBody_HubbardFermionSpectrum`, `ContinuumCoulomb_ManyBody_HubbardGlobal`, `ContinuumCoulomb_ManyBody_HubbardOccupation`, `ContinuumCoulomb_ManyBody_HubbardReduction`, `ContinuumCoulomb_ManyBody_HubbardSpin`, `ContinuumCoulomb_ManyBody_MediatorBlocks`, `ContinuumCoulomb_ManyBody_MediatorEffective`, `ContinuumCoulomb_ManyBody_MediatorForms`, `ContinuumCoulomb_ManyBody_MediatorFullListCorrectness`, `ContinuumCoulomb_ManyBody_MediatorGraph`, `ContinuumCoulomb_ManyBody_MediatorIteration`, `ContinuumCoulomb_ManyBody_MediatorListCorrectness`, `ContinuumCoulomb_ManyBody_MediatorParameters`, `ContinuumCoulomb_ManyBody_MediatorScaleBounds`, `ContinuumCoulomb_ManyBody_MediatorSector`, `ContinuumCoulomb_ManyBody_MediatorSimple`, `ContinuumCoulomb_ManyBody_MediatorUnaryPrimitives`, `ContinuumCoulomb_ManyBody_MediatorUnarySecond`, `ContinuumCoulomb_ManyBody_MediatorUnaryThird`, `ContinuumCoulomb_ManyBody_OccupationFock`, `ContinuumCoulomb_ManyBody_OccupationSector`, `ContinuumCoulomb_ManyBody_OrthogonalBlockDecomposition`, `ContinuumCoulomb_ManyBody_SlaterOccupation`, `ContinuumCoulomb_ManyBody_SpinEmbedding`, `ContinuumCoulomb_ManyBody_SpinMatrixNorm`, `ContinuumCoulomb_ManyBody_SuperexchangeSpectrum`, `ContinuumCoulomb_Nuclei_Cubature`, `ContinuumCoulomb_Nuclei_DensitySynthesis`, `ContinuumCoulomb_Nuclei_EulerRegisters`, `ContinuumCoulomb_Nuclei_EulerSchedule`, `ContinuumCoulomb_Nuclei_EulerTrajectory`, `ContinuumCoulomb_Nuclei_FlowImplicit`, `ContinuumCoulomb_Nuclei_NuclearCoordinateOutput`, `ContinuumCoulomb_Nuclei_TransportedNodes`, `ContinuumCoulomb_OneParticle_ApproximateBisection`, `ContinuumCoulomb_OneParticle_BoundedPotentialOperator`, `ContinuumCoulomb_OneParticle_CalibratedBisection`, `ContinuumCoulomb_OneParticle_CalibratedBisectionSchedule`, `ContinuumCoulomb_OneParticle_CalibratedContactCorrectness`, `ContinuumCoulomb_OneParticle_CalibratedEvaluationParameters`, `ContinuumCoulomb_OneParticle_CalibrationMesh`, `ContinuumCoulomb_OneParticle_CalibrationRationalBracket`, `ContinuumCoulomb_OneParticle_CenteredGaussEquiv`, `ContinuumCoulomb_OneParticle_CenteredGaussLabels`, `ContinuumCoulomb_OneParticle_CenteredGrid`, `ContinuumCoulomb_OneParticle_ClassicalH1`, `ContinuumCoulomb_OneParticle_ContactAdjustment`, `ContinuumCoulomb_OneParticle_ContactCanonicalEdge`, `ContinuumCoulomb_OneParticle_ContactEdgeNumber`, `ContinuumCoulomb_OneParticle_ContactGadgets`, `ContinuumCoulomb_OneParticle_ContactGeometryBlockSemantics`, `ContinuumCoulomb_OneParticle_ContactGlobal`, `ContinuumCoulomb_OneParticle_ContactGlobalSeparation`, `ContinuumCoulomb_OneParticle_ContactGrid`, `ContinuumCoulomb_OneParticle_ContactHeightBisection`, `ContinuumCoulomb_OneParticle_ContactHeightEvaluation`, `ContinuumCoulomb_OneParticle_ContactMediator`, `ContinuumCoulomb_OneParticle_ContactMediatorGeometry`, `ContinuumCoulomb_OneParticle_ContactMediatorLinks`, `ContinuumCoulomb_OneParticle_ContactRationalCoordinates`, `ContinuumCoulomb_OneParticle_ContactRationalGadget`, `ContinuumCoulomb_OneParticle_ContactRationalGlobal`, `ContinuumCoulomb_OneParticle_ContactRationalLocal`, `ContinuumCoulomb_OneParticle_ContactSourceGrid`, `ContinuumCoulomb_OneParticle_ContactSourceInputCorrectness`, `ContinuumCoulomb_OneParticle_ContactStrips`, `ContinuumCoulomb_OneParticle_ContactTemplates`, `ContinuumCoulomb_OneParticle_CoulombPacketTests`, `ContinuumCoulomb_OneParticle_CoulombPackets`, `ContinuumCoulomb_OneParticle_DiagonalPenalty`, `ContinuumCoulomb_OneParticle_ExplicitVerticalCutoff`, `ContinuumCoulomb_OneParticle_H1BoundedForm`, `ContinuumCoulomb_OneParticle_H1GraphCore`, `ContinuumCoulomb_OneParticle_HeatKernelModulus`, `ContinuumCoulomb_OneParticle_HoppingQuadrature`, `ContinuumCoulomb_OneParticle_HoppingSchedule`, `ContinuumCoulomb_OneParticle_LocalizedDualMatrix`, `ContinuumCoulomb_OneParticle_ManufacturedEuler`, `ContinuumCoulomb_OneParticle_ManufacturedFieldEvaluation`, `ContinuumCoulomb_OneParticle_PlanarModeH1`, `ContinuumCoulomb_OneParticle_PlanarWellNumerics`, `ContinuumCoulomb_OneParticle_PrefactorCalibration`, `ContinuumCoulomb_OneParticle_RationalBoxRound`, `ContinuumCoulomb_OneParticle_RationalGaussNodes`, `ContinuumCoulomb_OneParticle_RationalLogScale`, `ContinuumCoulomb_OneParticle_RationalTaylorRegisters`, `ContinuumCoulomb_OneParticle_SingleSpinSource`, `ContinuumCoulomb_OneParticle_SobolevDensityInput`, `ContinuumCoulomb_OneParticle_TM2Composition`, `ContinuumCoulomb_OneParticle_ThirdOrderBottom`, `ContinuumCoulomb_OneParticle_ThirdOrderPerturbation`, `ContinuumCoulomb_OneParticle_TransformedGauss`, `ContinuumCoulomb_OneParticle_TransformedGaussList`, `ContinuumCoulomb_OneParticle_TransformedGaussSeparation`, `ContinuumCoulomb_OneParticle_VerticalEnergy`, `ContinuumCoulomb_Programs_AmplificationProgram`, `ContinuumCoulomb_Programs_BisectionProgram`, `ContinuumCoulomb_Programs_BisectionRegisters`, `ContinuumCoulomb_Programs_CalibratedBisectionProgram`, `ContinuumCoulomb_Programs_CalibratedContactProgram`, `ContinuumCoulomb_Programs_CalibratedEvaluationProgram`, `ContinuumCoulomb_Programs_CenteredGaussProgram`, `ContinuumCoulomb_Programs_ContactEdgeNumberProgram`, `ContinuumCoulomb_Programs_ContactGeometryBlockProgram`, `ContinuumCoulomb_Programs_ContactLocalInputProgram`, `ContinuumCoulomb_Programs_ContactPlacedGadgetProgram`, `ContinuumCoulomb_Programs_ContactRationalPlaceProgram`, `ContinuumCoulomb_Programs_ContactSourceInputProgram`, `ContinuumCoulomb_Programs_CountertermProgram`, `ContinuumCoulomb_Programs_DyadicRootProgram`, `ContinuumCoulomb_Programs_EncodingPrograms`, `ContinuumCoulomb_Programs_EnumeratedGridNuclei`, `ContinuumCoulomb_Programs_GaussNodeProgram`, `ContinuumCoulomb_Programs_ManufacturedFieldProgram`, `ContinuumCoulomb_Programs_ManufacturedVelocityProgram`, `ContinuumCoulomb_Programs_MediatorListProgram`, `ContinuumCoulomb_Programs_MediatorOffsetProgram`, `ContinuumCoulomb_Programs_MediatorProgram`, `ContinuumCoulomb_Programs_PhysicalNuclearProgram`, `ContinuumCoulomb_Programs_PlanarWellProgram`, `ContinuumCoulomb_Programs_PrefixListPrograms`, `ContinuumCoulomb_Programs_PrefixPrograms`, `ContinuumCoulomb_Programs_RationalSumProgram`, `ContinuumCoulomb_Programs_SmoothTransitionProgram`, `ContinuumCoulomb_Programs_SourceContactProgram`, `ContinuumCoulomb_Programs_SourceMetadataProgram`, `ContinuumCoulomb_Programs_SourceNormalizationProgram`, `ContinuumCoulomb_Programs_SourcePositiveProgram`, `ContinuumCoulomb_Programs_SourcePrograms`, `ContinuumCoulomb_Programs_SquareRootProgram`, `ContinuumCoulomb_Programs_TransformedGaussProgram`, `ContinuumCoulomb_Programs_UnitBinaryProgram`, `ContinuumCoulomb_Programs_VerticalCutoffProgram`, `ContinuumCoulomb_Quantum_QuantumAncilla`, `ContinuumCoulomb_Quantum_QuantumBlockEdges`, `ContinuumCoulomb_Quantum_QuantumCellCorridor`, `ContinuumCoulomb_Quantum_QuantumCellPathTemplates`, `ContinuumCoulomb_Quantum_QuantumCellRouteCatalog`, `ContinuumCoulomb_Quantum_QuantumCellRouteSupport`, `ContinuumCoulomb_Quantum_QuantumCellTranslate`, `ContinuumCoulomb_Quantum_QuantumChosenSlots`, `ContinuumCoulomb_Quantum_QuantumClockCells`, `ContinuumCoulomb_Quantum_QuantumClockTransition`, `ContinuumCoulomb_Quantum_QuantumCrossingPatch`, `ContinuumCoulomb_Quantum_QuantumEntryParity`, `ContinuumCoulomb_Quantum_QuantumEvenRouteData`, `ContinuumCoulomb_Quantum_QuantumEvenRoutePlacement`, `ContinuumCoulomb_Quantum_QuantumEvenRouteRealization`, `ContinuumCoulomb_Quantum_QuantumEvolution`, `ContinuumCoulomb_Quantum_QuantumFineRoute`, `ContinuumCoulomb_Quantum_QuantumFiniteHistory`, `ContinuumCoulomb_Quantum_QuantumForkDegreeBound`, `ContinuumCoulomb_Quantum_QuantumForkPorts`, `ContinuumCoulomb_Quantum_QuantumForkRounds`, `ContinuumCoulomb_Quantum_QuantumForkState`, `ContinuumCoulomb_Quantum_QuantumForkStateDegree`, `ContinuumCoulomb_Quantum_QuantumGraphDegree`, `ContinuumCoulomb_Quantum_QuantumGridNeighborsFour`, `ContinuumCoulomb_Quantum_QuantumGridPorts`, `ContinuumCoulomb_Quantum_QuantumGridSlots`, `ContinuumCoulomb_Quantum_QuantumGridWalk`, `ContinuumCoulomb_Quantum_QuantumHalfCorridor`, `ContinuumCoulomb_Quantum_QuantumHistoryEnumeration`, `ContinuumCoulomb_Quantum_QuantumInnerPorts`, `ContinuumCoulomb_Quantum_QuantumInternalRouteSeparation`, `ContinuumCoulomb_Quantum_QuantumLocalEnlarge`, `ContinuumCoulomb_Quantum_QuantumLocalFamily`, `ContinuumCoulomb_Quantum_QuantumLocalLift`, `ContinuumCoulomb_Quantum_QuantumLocalPathClearance`, `ContinuumCoulomb_Quantum_QuantumLocalPropagation`, `ContinuumCoulomb_Quantum_QuantumLocalTensor`, `ContinuumCoulomb_Quantum_QuantumManhattanRoute`, `ContinuumCoulomb_Quantum_QuantumMask`, `ContinuumCoulomb_Quantum_QuantumMergedEndpointPairs`, `ContinuumCoulomb_Quantum_QuantumMergedOutputRoutes`, `ContinuumCoulomb_Quantum_QuantumNearestGate`, `ContinuumCoulomb_Quantum_QuantumOrdinalSpatial`, `ContinuumCoulomb_Quantum_QuantumParallelGraph`, `ContinuumCoulomb_Quantum_QuantumPartialPaths`, `ContinuumCoulomb_Quantum_QuantumPatchSeparation`, `ContinuumCoulomb_Quantum_QuantumPathEmbedding`, `ContinuumCoulomb_Quantum_QuantumPathProgram`, `ContinuumCoulomb_Quantum_QuantumPathSchedule`, `ContinuumCoulomb_Quantum_QuantumPathSubdivision`, `ContinuumCoulomb_Quantum_QuantumPermittedRouteSeparation`, `ContinuumCoulomb_Quantum_QuantumPinnedClock`, `ContinuumCoulomb_Quantum_QuantumPortCellPositive`, `ContinuumCoulomb_Quantum_QuantumPortChain`, `ContinuumCoulomb_Quantum_QuantumPrefix`, `ContinuumCoulomb_Quantum_QuantumRationalPathStep`, `ContinuumCoulomb_Quantum_QuantumReferenceBasis`, `ContinuumCoulomb_Quantum_QuantumReferenceHistory`, `ContinuumCoulomb_Quantum_QuantumReferenceLocal`, `ContinuumCoulomb_Quantum_QuantumRouteEnumeration`, `ContinuumCoulomb_Quantum_QuantumRouteProgram`, `ContinuumCoulomb_Quantum_QuantumRoutingSize`, `ContinuumCoulomb_Quantum_QuantumRoutingTable`, `ContinuumCoulomb_Quantum_QuantumSpatialExchange`, `ContinuumCoulomb_Quantum_QuantumStagePath`, `ContinuumCoulomb_Quantum_QuantumStageStep`, `ContinuumCoulomb_Quantum_QuantumTaggedSweep`, `ContinuumCoulomb_Quantum_QuantumTranslatedPatch`, `ContinuumCoulomb_Reduction_AutomaticCalibrationList`, `ContinuumCoulomb_Reduction_AutomaticCalibrationNormalization`, `ContinuumCoulomb_Reduction_AutomaticCalibrationParameters`, `ContinuumCoulomb_Reduction_BinaryEncoding`, `ContinuumCoulomb_Reduction_ComputableHopping`, `ContinuumCoulomb_Reduction_HardnessComposition`, `ContinuumCoulomb_Reduction_Perturbation`, `ContinuumCoulomb_Reduction_PublishedFlowInput`, `ContinuumCoulomb_Reduction_SourceBondLists`, `ContinuumCoulomb_Reduction_SourceCoefficientRounding`, `ContinuumCoulomb_Reduction_SourceFinalGraph`, `ContinuumCoulomb_Reduction_SourceGeometryBounds`, `ContinuumCoulomb_Reduction_SourceHamiltonian`, `ContinuumCoulomb_Reduction_SourceMatrix`, `ContinuumCoulomb_Reduction_SourceNormalizationCorrectness`, `ContinuumCoulomb_Reduction_SourceNormalizedLattice`, `ContinuumCoulomb_Reduction_SourceNormalizedPromise`, `ContinuumCoulomb_Reduction_SourceNormalizedSpectrum`, `ContinuumCoulomb_Reduction_SourcePauli`, `ContinuumCoulomb_Reduction_SourcePositiveCorrectness`, `ContinuumCoulomb_Reduction_SourcePromise`, `ContinuumCoulomb_Reduction_SourceSpectrum`, `ContinuumCoulomb_Reduction_SourceZeroFilter`, `CoulombRadii_FieldAnalysis_DeterminantWave`, `CoulombRadii_Packets_ComplexWindow`, `Laughlin_Exterior_OccupationDiagonal`, `Laughlin_Model`, `Laughlin_Operators_CAR`, `MinUncut_Machines_MachineCompare`, `MinUncut_Machines_MachineSubstitution`, `MinUncut_Machines_Runtime`, `QuantumFactoring_BitStackIntegers`, `QuantumFactoring_BitStackListIndex`, `QuantumFactoring_BitStackListMapWith`, `QuantumFactoring_BitStackListOps`, `QuantumFactoring_BitStackListWords`, `QuantumFactoring_BitStackMultiplier`, `QuantumFactoring_BitStackPowers`, `QuantumFactoring_BitStackPrograms`, `QuantumFactoring_BitStackTabulate`, `QuantumFactoring_BitStackUnary`, `QuantumFactoring_NativeAIGBounds`.
--
--   **Imports.** It imports the published bundle `Def_ContinuumCoulombHardness`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ092A004`, `OAIQ092A005`, `OAIQ092A006`, `OAIQ092A007` and `OAIQ092A011`; the statements `OAI_ContinuumCoulomb_HubbardGlobal_hubbardFermionBottom_Gram_Heisenberg`, `OAI.ContinuumCoulomb.publishedCMPHardness` and `OAI.ContinuumCoulomb.qmaXZSubdivision_accuracy`.
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
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.NatAbs
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Chain
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.TakeDrop
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
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ToLin
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
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.UpperLower.Basic
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

section
-- module Solutions.OAIQ092_CC.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ092_CC.Analysis_FunctionalSpaces_Sobolev_Euclidean_H1
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
# `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.H1`

An upstream-friendly **definition** of a Euclidean `H¹`-type energy space built from `L²`.

At the current Mathlib pin, we do not have a ready-made Sobolev-space development for domains or
manifolds. For the Laplace–Beltrami compact-resolvent discharge, we mainly need:

1. a Hilbert space `H¹` equipped with a continuous embedding into `L²`;
2. a continuous “gradient” map `H¹ → L²(E)`; and later
3. a compactness theorem for the inclusion on bounded domains / compact manifolds (Rellich).

This file defines `H¹` as the closed submodule of `L² × L²(E)` generated by `C¹`-functions with
compact support and their gradients (expressed using the Riesz representation `toDual`).

## Main definitions

- `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.C1c`:
  the `ℝ`-submodule of `C¹` compactly supported functions `E → ℝ`.
- `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1`:
  the (closed) `H¹` submodule of `L²(E) × L²(E,E)`.
- `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1ToL2`:
  the continuous embedding `H¹ → L²`.
- `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1ToL2Grad`:
  the continuous gradient map `H¹ → L²(E)`.

No analytic “Sobolev theorems” are proved here; those are tracked separately (Rellich / elliptic
regularity beads).
-/

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean

open scoped ENNReal MeasureTheory
open MeasureTheory

section

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local instance instMeasurableSpace_solutions : MeasurableSpace E := borel E
local instance instBorelSpace_solutions : BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpace_solutions : OpensMeasurableSpace E := by infer_instance

variable (μ : Measure E) [IsFiniteMeasureOnCompacts μ]

abbrev L2ℝ : Type _ := ↥(E →₂[μ] ℝ)
abbrev L2E : Type _ := ↥(E →₂[μ] E)
abbrev H1Target : Type _ := L2ℝ (μ := μ) × L2E (μ := μ)

/-- `C¹` real-valued functions on `E` with compact support, as a submodule of `E → ℝ`. -/
def C1c : Submodule ℝ (E → ℝ) where
  carrier := {f | ContDiff ℝ 1 f ∧ HasCompactSupport f}
  zero_mem' := by
    refine ⟨contDiff_const, ?_⟩
    simpa using (HasCompactSupport.zero : HasCompactSupport (fun _ : E => (0 : ℝ)))
  add_mem' := by
    intro f g hf hg
    refine ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  smul_mem' := by
    intro c f hf
    refine ⟨hf.1.const_smul c, ?_⟩
    -- `HasCompactSupport` is stable under pointwise scalar multiplication.
    exact (HasCompactSupport.smul_left (f := fun _ : E => c) hf.2)

/-- The pointwise gradient (as an `E`-valued function), via Riesz representation. -/
noncomputable def grad (f : E → ℝ) : E → E :=
  fun x => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x)

lemma continuous_grad {f : E → ℝ} (hf : ContDiff ℝ 1 f) : Continuous (grad (E := E) f) := by
  have hcont : Continuous (fderiv ℝ f) := hf.continuous_fderiv one_ne_zero
  have : Continuous fun x => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x) :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.comp hcont
  exact this

lemma hasCompactSupport_grad {f : E → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (grad (E := E) f) := by
  -- Outside the support of `f`, `fderiv` is identically `0`, hence so is `grad`.
  have hf' : HasCompactSupport (fderiv ℝ f) := hf.fderiv ℝ
  -- `grad` is composition with a linear map sending `0` to `0`.
  exact
    (HasCompactSupport.comp_left (f := fderiv ℝ f) (g := (InnerProductSpace.toDual ℝ E).symm)
      hf' (by simp))

omit [CompleteSpace E] in
lemma memLp_of_mem_C1c {f : E → ℝ} (hf : f ∈ C1c (E := E)) : MemLp f 2 μ := by
  exact (hf.1.continuous.memLp_of_hasCompactSupport (μ := μ) (p := (2 : ℝ≥0∞)) hf.2)

lemma memLp_grad_of_mem_C1c {f : E → ℝ} (hf : f ∈ C1c (E := E)) :
    MemLp (grad (E := E) f) 2 μ := by
  have hcont : Continuous (grad (E := E) f) := continuous_grad (E := E) (f := f) hf.1
  have hcs : HasCompactSupport (grad (E := E) f) := hasCompactSupport_grad (E := E) (f := f) hf.2
  exact hcont.memLp_of_hasCompactSupport (μ := μ) (p := (2 : ℝ≥0∞)) hcs

/-- The `L²` class of a `C¹` compactly supported function. -/
noncomputable def toL2 (f : ↥(C1c (E := E))) : L2ℝ (μ := μ) :=
  (memLp_of_mem_C1c (μ := μ) (E := E) f.2).toLp f.1

/-- The `L²` class of the gradient of a `C¹` compactly supported function. -/
noncomputable def toL2Grad (f : ↥(C1c (E := E))) : L2E (μ := μ) :=
  (memLp_grad_of_mem_C1c (μ := μ) (E := E) f.2).toLp (grad (E := E) f.1)

omit [CompleteSpace E] in
lemma toL2_add (f g : ↥(C1c (E := E))) :
    toL2 (μ := μ) (E := E) (f + g) =
      toL2 (μ := μ) (E := E) f + toL2 (μ := μ) (E := E) g := by
  apply Lp.ext
  have hf : (toL2 (μ := μ) (E := E) f : E → ℝ) =ᵐ[μ] f.1 :=
    (memLp_of_mem_C1c (μ := μ) (E := E) f.2).coeFn_toLp
  have hg : (toL2 (μ := μ) (E := E) g : E → ℝ) =ᵐ[μ] g.1 :=
    (memLp_of_mem_C1c (μ := μ) (E := E) g.2).coeFn_toLp
  have hfg : (toL2 (μ := μ) (E := E) (f + g) : E → ℝ) =ᵐ[μ] (f.1 + g.1) :=
    (memLp_of_mem_C1c (μ := μ) (E := E) (f + g).2).coeFn_toLp
  -- Both sides agree a.e. with `f + g`.
  refine hfg.trans ?_
  filter_upwards [Lp.coeFn_add (toL2 (μ := μ) (E := E) f) (toL2 (μ := μ) (E := E) g), hf, hg]
    with x hxadd hxf hxg
  -- Rewrite both sides in terms of pointwise evaluation.
  calc
    f.1 x + g.1 x =
        (toL2 (μ := μ) (E := E) f : E → ℝ) x +
          (toL2 (μ := μ) (E := E) g : E → ℝ) x := by
      simp [hxf, hxg]
    _ = ((toL2 (μ := μ) (E := E) f + toL2 (μ := μ) (E := E) g : L2ℝ (μ := μ)) : E → ℝ) x := by
      simpa [Pi.add_apply] using hxadd.symm

omit [CompleteSpace E] in
lemma toL2_smul (c : ℝ) (f : ↥(C1c (E := E))) :
    toL2 (μ := μ) (E := E) (c • f) = c • toL2 (μ := μ) (E := E) f := by
  apply Lp.ext
  have hf : (toL2 (μ := μ) (E := E) f : E → ℝ) =ᵐ[μ] f.1 :=
    (memLp_of_mem_C1c (μ := μ) (E := E) f.2).coeFn_toLp
  have hcf : (toL2 (μ := μ) (E := E) (c • f) : E → ℝ) =ᵐ[μ] (c • f.1) :=
    (memLp_of_mem_C1c (μ := μ) (E := E) (c • f).2).coeFn_toLp
  refine hcf.trans ?_
  filter_upwards [Lp.coeFn_smul c (toL2 (μ := μ) (E := E) f), hf] with x hxsmul hxf
  simp [Pi.smul_apply, hxsmul, hxf]

/-- Linear map sending `C¹_c` functions to their `L²` classes. -/
noncomputable def toL2Linear : ↥(C1c (E := E)) →ₗ[ℝ] L2ℝ (μ := μ) where
  toFun := toL2 (μ := μ) (E := E)
  map_add' := toL2_add (μ := μ) (E := E)
  map_smul' := toL2_smul (μ := μ) (E := E)

lemma toL2Grad_add (f g : ↥(C1c (E := E))) :
    toL2Grad (μ := μ) (E := E) (f + g) =
      toL2Grad (μ := μ) (E := E) f + toL2Grad (μ := μ) (E := E) g := by
  apply Lp.ext
  have hf : (toL2Grad (μ := μ) (E := E) f : E → E) =ᵐ[μ] grad (E := E) f.1 :=
    (memLp_grad_of_mem_C1c (μ := μ) (E := E) f.2).coeFn_toLp
  have hg : (toL2Grad (μ := μ) (E := E) g : E → E) =ᵐ[μ] grad (E := E) g.1 :=
    (memLp_grad_of_mem_C1c (μ := μ) (E := E) g.2).coeFn_toLp
  have hfg :
      (toL2Grad (μ := μ) (E := E) (f + g) : E → E) =ᵐ[μ] grad (E := E) (f.1 + g.1) :=
    (memLp_grad_of_mem_C1c (μ := μ) (E := E) (f + g).2).coeFn_toLp
  refine hfg.trans ?_
  filter_upwards [Lp.coeFn_add (toL2Grad (μ := μ) (E := E) f) (toL2Grad (μ := μ) (E := E) g), hf,
    hg] with x hxadd hxf hxg
  have hdf : DifferentiableAt ℝ f.1 x :=
    (f.2.1.differentiable one_ne_zero).differentiableAt
  have hdg : DifferentiableAt ℝ g.1 x :=
    (g.2.1.differentiable one_ne_zero).differentiableAt
  -- Rewrite in terms of pointwise evaluation and use linearity of `grad`.
  have hgrad :
      grad (E := E) (f.1 + g.1) x = grad (E := E) f.1 x + grad (E := E) g.1 x := by
    simp [grad, fderiv_add hdf hdg, map_add]
  calc
    grad (E := E) (f.1 + g.1) x = grad (E := E) f.1 x + grad (E := E) g.1 x := hgrad
    _ =
        (toL2Grad (μ := μ) (E := E) f : E → E) x +
          (toL2Grad (μ := μ) (E := E) g : E → E) x := by
        simp [hxf, hxg]
    _ = ((toL2Grad (μ := μ) (E := E) f +
            toL2Grad (μ := μ) (E := E) g : L2E (μ := μ)) :
            E → E) x := by
        simpa [Pi.add_apply] using hxadd.symm

lemma toL2Grad_smul (c : ℝ) (f : ↥(C1c (E := E))) :
    toL2Grad (μ := μ) (E := E) (c • f) = c • toL2Grad (μ := μ) (E := E) f := by
  apply Lp.ext
  have hf : (toL2Grad (μ := μ) (E := E) f : E → E) =ᵐ[μ] grad (E := E) f.1 :=
    (memLp_grad_of_mem_C1c (μ := μ) (E := E) f.2).coeFn_toLp
  have hcf :
      (toL2Grad (μ := μ) (E := E) (c • f) : E → E) =ᵐ[μ] grad (E := E) (c • f.1) :=
    (memLp_grad_of_mem_C1c (μ := μ) (E := E) (c • f).2).coeFn_toLp
  refine hcf.trans ?_
  filter_upwards [Lp.coeFn_smul c (toL2Grad (μ := μ) (E := E) f), hf] with x hxsmul hxf
  have hdf : DifferentiableAt ℝ f.1 x :=
    (f.2.1.differentiable one_ne_zero).differentiableAt
  have hgrad : grad (E := E) (c • f.1) x = c • grad (E := E) f.1 x := by
    simp [grad, fderiv_const_smul hdf, map_smul]
  calc
    grad (E := E) (c • f.1) x = c • grad (E := E) f.1 x := hgrad
    _ = c • (toL2Grad (μ := μ) (E := E) f : E → E) x := by
      simp [hxf]
    _ = ((c • toL2Grad (μ := μ) (E := E) f : L2E (μ := μ)) : E → E) x := by
      -- `Lp.coeFn_smul` gives the pointwise evaluation of `c • f` in `L²`.
      simpa [Pi.smul_apply] using hxsmul.symm

/-- Linear map sending `C¹_c` functions to the `L²` class of their gradient. -/
noncomputable def toL2GradLinear : ↥(C1c (E := E)) →ₗ[ℝ] L2E (μ := μ) where
  toFun := toL2Grad (μ := μ) (E := E)
  map_add' := toL2Grad_add (μ := μ) (E := E)
  map_smul' := toL2Grad_smul (μ := μ) (E := E)

/-- The graph map `f ↦ (f, ∇f)` into `L² × L²(E)`. -/
noncomputable def graph : ↥(C1c (E := E)) →ₗ[ℝ] H1Target (μ := μ) :=
  (toL2Linear (μ := μ) (E := E)).prod (toL2GradLinear (μ := μ) (E := E))

/-- The Euclidean `H¹` space (as a closed submodule of `L² × L²(E)`). -/
noncomputable def h1 : Submodule ℝ (H1Target (μ := μ)) :=
  (LinearMap.range (graph (μ := μ) (E := E))).topologicalClosure

/-- The Euclidean `H¹` submodule is closed by construction. -/
theorem isClosed_h1 : IsClosed (h1 (μ := μ) (E := E) : Set (H1Target (μ := μ))) := by
  delta h1
  exact Submodule.isClosed_topologicalClosure (LinearMap.range (graph (μ := μ) (E := E)))

/-- The continuous embedding `H¹ → L²`. -/
noncomputable def h1ToL2 : (↥(h1 (μ := μ) (E := E))) →L[ℝ] L2ℝ (μ := μ) :=
  (ContinuousLinearMap.fst ℝ (L2ℝ (μ := μ)) (L2E (μ := μ))).comp
    (Submodule.subtypeL (h1 (μ := μ) (E := E)))

end

end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov
end

section
-- module Solutions.OAIQ092_CC.Analysis_FunctionalSpaces_Sobolev_Euclidean_Rellich
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.Rellich`

Euclidean Rellich–Kondrachov compactness for fixed compact support (Lebesgue `volume`).

This file discharges the “Euclidean heart” needed by the manifold Rellich glue:
for a fixed compact set `K ⊆ E`, the inclusion `H¹ → L²` is compact when restricted to the closed
subspace of `H¹` whose `L²` component is supported in `K` (a.e.).

The proof uses:

1. the Euclidean `H¹` translation estimate
   `‖τ_a u - u‖₂ ≤ ‖a‖ · ‖∇u‖₂` (`TranslationEstimateH1`);
2. the Fréchet–Kolmogorov / smoothing-based `L²` compactness criterion
   (`L2CompactnessCriterion`).

## Main definitions / results

- `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1On`:
  the closed subspace of `H¹(volume)` whose `L²` component is supported in `K` (a.e.).
- `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1OnToL2`:
  the restricted inclusion map `h1On K →L[ℝ] L²(volume)`.
- `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.isCompactOperator_h1OnToL2`:
  compactness of the inclusion.

Tracking: Beads `lean-103.5.2.26.5.3.2.1`.
-/

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean

open scoped ENNReal MeasureTheory Topology
open MeasureTheory Set

noncomputable section

section Volume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]

local instance instMeasurableSpaceE_SobolevEuclideanRellich : MeasurableSpace E := borel E
local instance instBorelSpaceE_SobolevEuclideanRellich : BorelSpace E := ⟨rfl⟩
local instance instFactOneLeTwo_SobolevEuclideanRellich : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

/-! ### Supported `H¹` subspace -/

/-! ### Euclidean Rellich on fixed compact support -/

/-!
### Codomain restriction and a compact map into `L²(volume.restrict K)`

The definition of `h1On` forces the image of `h1OnToL2` to lie in the (closed) range of the
extension-by-zero map from `volume.restrict K`. We record a codomain-restricted version and a
convenient compact map to the restricted `L²` space.
-/

end Volume

end

end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov
end

section
-- module Solutions.OAIQ092_CC.BiholderTransport_Regularity_UnitTime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
abbrev UnitTime := Icc (0:ℝ) 1
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance instFactLeRealOfNat_solutions : Fact ((0:ℝ) ≤ 1) := ⟨zero_le_one⟩

def extendUnitPath (u : C(UnitTime,E)) : C(ℝ,E) :=
  u.comp (ContinuousMap.projIccCM (a := (0:ℝ)) (b := 1))

omit [NormedSpace ℝ E] in
@[simp] lemma extendUnitPath_coe (u : C(UnitTime,E)) (t : UnitTime) :
    extendUnitPath u t = u t := by
  change u (projIcc 0 1 (by positivity) t) = u t
  rw [projIcc_of_mem _ t.property]

omit [NormedSpace ℝ E] in
@[simp] lemma extendUnitPath_add (u v : C(UnitTime,E)) :
    extendUnitPath (u+v) = extendUnitPath u + extendUnitPath v := rfl

@[simp] lemma extendUnitPath_smul (c : ℝ) (u : C(UnitTime,E)) :
    extendUnitPath (c • u) = c • extendUnitPath u := rfl

def unitPathPrimitive (u : C(UnitTime,E)) : C(UnitTime,E) :=
  ⟨fun t => ∫ s in (0:ℝ)..t.val, extendUnitPath u s,
   (intervalIntegral.continuous_primitive
      (fun a b => (extendUnitPath u).continuous.intervalIntegrable a b) 0).comp
      continuous_subtype_val⟩

lemma unitPathPrimitive_bound (u : C(UnitTime,E)) : ‖unitPathPrimitive u‖ ≤ ‖u‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg u)).mpr
  intro t
  change ‖∫ s in (0:ℝ)..t.val, extendUnitPath u s‖ ≤ ‖u‖
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := t.val) (f := extendUnitPath u)
    (C := ‖u‖) (fun s _ => u.norm_coe_le_norm (projIcc 0 1 (by positivity) s))
  apply h.trans
  rw [sub_zero,abs_of_nonneg t.property.1]
  exact mul_le_of_le_one_right (norm_nonneg u) t.property.2

def unitPathIntegral : C(UnitTime,E) →L[ℝ] C(UnitTime,E) := by
  let L : C(UnitTime,E) →ₗ[ℝ] C(UnitTime,E) :=
    { toFun := unitPathPrimitive
      map_add' := by
        intro u v; ext t
        change (∫ s in (0:ℝ)..t.val, extendUnitPath (u+v) s) =
          (∫ s in (0:ℝ)..t.val, extendUnitPath u s) +
          (∫ s in (0:ℝ)..t.val, extendUnitPath v s)
        rw [extendUnitPath_add]
        exact intervalIntegral.integral_add
          ((extendUnitPath u).continuous.intervalIntegrable _ _)
          ((extendUnitPath v).continuous.intervalIntegrable _ _)
      map_smul' := by
        intro c u; ext t
        change (∫ s in (0:ℝ)..t.val, extendUnitPath (c • u) s) =
          c • (∫ s in (0:ℝ)..t.val, extendUnitPath u s)
        rw [extendUnitPath_smul]
        exact intervalIntegral.integral_smul c (extendUnitPath u) }
  exact L.mkContinuous 1 (by
    intro u
    change ‖unitPathPrimitive (u : C(UnitTime,E))‖ ≤ 1 * ‖u‖
    simpa only [one_mul] using unitPathPrimitive_bound u)

@[simp] lemma unitPathIntegral_apply (u : C(UnitTime,E)) (t : UnitTime) :
    unitPathIntegral u t = ∫ s in (0:ℝ)..t.val, extendUnitPath u s := rfl

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_ChargePenalty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Charge-transfer penalty at half filling

The diagonal part of the finite fermion model keeps long-range direct
Coulomb interactions. A symmetric interaction matrix with bounded absolute
row sums gives a gap against every nonsingly occupied configuration.
-/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

def occupationDeviation {m : ℕ} (occupation : Fin m → Fin 3) (i : Fin m) : ℝ :=
  (occupation i : ℕ) - 1

def chargePenalty {m : ℕ} (U : ℝ) (V : Fin m → Fin m → ℝ)
    (occupation : Fin m → Fin 3) : ℝ :=
  U / 2 * ∑ i, occupationDeviation occupation i ^ 2 +
    (1 / 2 : ℝ) * ∑ i, ∑ j,
      V i j * occupationDeviation occupation i * occupationDeviation occupation j

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_DiagonalPenalty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The concrete inverse of a charge-sector penalty

The high block of the Hubbard penalty is diagonal in the occupation basis.
That block and its inverse are continuous linear maps satisfying the
positivity, symmetry and inverse-norm hypotheses of the second-order
perturbation theorem.
-/

noncomputable section
open scoped BigOperators InnerProductSpace
namespace ContinuumCoulomb

variable {Basis : Type*} [Fintype Basis]

def diagonalPenaltyLinear (weight : Basis → ℝ) :
    EuclideanSpace ℂ Basis →ₗ[ℝ] EuclideanSpace ℂ Basis where
  toFun x := WithLp.toLp 2 (fun s => weight s • x s)
  map_add' x y := by ext s; simp [smul_add]
  map_smul' c x := by
    ext s
    change (weight s : ℂ) * ((c : ℂ) * x s) = (c : ℂ) * ((weight s : ℂ) * x s)
    ring

def diagonalPenalty (weight : Basis → ℝ) :
    EuclideanSpace ℂ Basis →L[ℝ] EuclideanSpace ℂ Basis :=
  (diagonalPenaltyLinear weight).toContinuousLinearMap

@[simp] theorem diagonalPenalty_apply (weight : Basis → ℝ)
    (x : EuclideanSpace ℂ Basis) (s : Basis) :
    diagonalPenalty weight x s = weight s • x s := rfl

/-- High occupations exclude the singly occupied spin subspace. -/
abbrev ChargeHighBasis {m : ℕ} (occupation : Basis → Fin m → Fin 3) :=
  {s : Basis // ¬ ∀ i, occupation s i = 1}

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_Perturbation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Second-order block estimates

The finite reductions use the bottom-energy estimate from the binary
manuscript's `lem:second-order` and the unit manuscript's `lem:perturbation`.
Explicit positivity and operator norm bounds give vector and variational
estimates for the penalty, inverse, coupling and high perturbation blocks.

Real inner products also express the real quadratic forms of complex spin
Hilbert spaces by restriction of scalars.
-/

noncomputable section

open scoped InnerProductSpace

namespace ContinuumCoulomb
namespace Perturbation

variable {L H : Type*}
variable [NormedAddCommGroup L] [InnerProductSpace ℝ L]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def penaltyForm (A : H →L[ℝ] H) (q : H) : ℝ := ⟪q, A q⟫_ℝ

def inverseForm (T : H →L[ℝ] H) (B : L →L[ℝ] H) (p : L) : ℝ :=
  ⟪B p, T (B p)⟫_ℝ

/-- Full block energy when the low-low perturbation block vanishes. -/
def blockEnergy (A D : H →L[ℝ] H) (B : L →L[ℝ] H) (p : L) (q : H) : ℝ :=
  penaltyForm A q + 2 * ⟪q, B p⟫_ℝ + ⟪q, D q⟫_ℝ

def blockRayleigh (A D : H →L[ℝ] H) (B : L →L[ℝ] H) (p : L) (q : H) : ℝ :=
  blockEnergy A D B p q / (‖p‖ ^ 2 + ‖q‖ ^ 2)

def blockBottom (A D : H →L[ℝ] H) (B : L →L[ℝ] H) : ℝ :=
  sInf {e | ∃ (p : L) (q : H), 0 < ‖p‖ ^ 2 + ‖q‖ ^ 2 ∧
    e = blockRayleigh A D B p q}

/-- First-order low compression together with its second-order inverse term. -/
def effectiveForm (C : L →L[ℝ] L) (T : H →L[ℝ] H) (B : L →L[ℝ] H)
    (p : L) : ℝ := ⟪p, C p⟫_ℝ - inverseForm T B p

def effectiveBottom (C : L →L[ℝ] L) (T : H →L[ℝ] H) (B : L →L[ℝ] H) : ℝ :=
  sInf {e | ∃ p : L, ‖p‖ = 1 ∧ e = effectiveForm C T B p}

def lowBlockEnergy (C : L →L[ℝ] L) (A D : H →L[ℝ] H)
    (B : L →L[ℝ] H) (p : L) (q : H) : ℝ :=
  ⟪p, C p⟫_ℝ + blockEnergy A D B p q

def lowBlockRayleigh (C : L →L[ℝ] L) (A D : H →L[ℝ] H)
    (B : L →L[ℝ] H) (p : L) (q : H) : ℝ :=
  lowBlockEnergy C A D B p q / (‖p‖ ^ 2 + ‖q‖ ^ 2)

def lowBlockBottom (C : L →L[ℝ] L) (A D : H →L[ℝ] H)
    (B : L →L[ℝ] H) : ℝ :=
  sInf {e | ∃ (p : L) (q : H), 0 < ‖p‖ ^ 2 + ‖q‖ ^ 2 ∧
    e = lowBlockRayleigh C A D B p q}

end Perturbation
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_GlobalSinglet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Canonical singlet/triplet coordinates for simultaneous fresh mediator pairs. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators InnerProductSpace

abbrev MediatorBasis (r : ℕ) := Fin r → Fin 4

def mediatorVacuum (r : ℕ) : MediatorBasis r := fun _ => 0

abbrev MediatorHighBasis (r : ℕ) := {a : MediatorBasis r // a ≠ mediatorVacuum r}

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_BinaryEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit prefix-free binary encodings for finite source and circuit data.
Natural numbers use their binary digits, with one marker bit per digit.
Pairs concatenate; lists have a binary length header. In particular, list
serialization does not repeatedly pair large natural-number codes. -/

namespace ContinuumCoulomb
namespace BinaryEncoding

theorem encodeDigits_length (digits : BitString) :
    (encodeDigits digits).length = 2 * digits.length + 1 := by
  induction digits with
  | nil => rfl
  | cons b digits ih => simp only [encodeDigits, List.length_cons, ih]; omega

/-- The code of a natural has linear overhead in its binary bit length. -/
theorem natural_length (n : ℕ) : (natural.encode n).length = 2 * n.size + 1 := by
  change (encodeDigits n.bits).length = _
  rw [encodeDigits_length, Nat.size_eq_bits_len]

theorem pair_length {α β : Type*} (a : Codec α) (b : Codec β) (x : α × β) :
    ((pair a b).encode x).length = (a.encode x.1).length + (b.encode x.2).length :=
  List.length_append

end BinaryEncoding
end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceHamiltonian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Signed square-lattice Heisenberg source

The finite source is the field-free Heisenberg problem of
Cubitt–Montanaro–Piddock, *Universal quantum Hamiltonians*,
arXiv:1701.05182v4, Theorem 48, Lemma 47 and Section 10.1.
The coordinate-swap action realizes `2 SWAP - I`. Coefficient-rounding
estimates hold for arbitrary many-spin states, including entangled states.
-/

noncomputable section

namespace ContinuumCoulomb

open scoped BigOperators

abbrev SourceSpinVector (n : ℕ) := SourceSpinBasis n → ℂ

def sourceSpinMass {n : ℕ} (u : SourceSpinVector n) : ℝ :=
  ∑ s, Complex.normSq (u s)

/-- Swap the two selected spin coordinates, leaving every spectator fixed. -/
def sourceSpinSwap {n : ℕ} (i j : Fin n) :
    SourceSpinBasis n ≃ SourceSpinBasis n :=
  Equiv.arrowCongr (Equiv.swap i j) (Equiv.refl (Fin 2))

theorem sourceSpinMass_nonneg {n : ℕ} (u : SourceSpinVector n) :
    0 ≤ sourceSpinMass u :=
  Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

theorem sourceSpinMass_swap {n : ℕ} (i j : Fin n) (u : SourceSpinVector n) :
    (∑ s, Complex.normSq (u (sourceSpinSwap i j s))) = sourceSpinMass u :=
  (sourceSpinSwap i j).sum_comp (fun s => Complex.normSq (u s))

/-- The expectation of coordinate exchange, taking its real part. -/
def sourceSwapExpectation {n : ℕ} (i j : Fin n) (u : SourceSpinVector n) : ℝ :=
  ∑ s, (star (u s) * u (sourceSpinSwap i j s)).re

theorem sourceSwapExpectation_add_identity {n : ℕ}
    (i j : Fin n) (u : SourceSpinVector n) :
    (∑ s, Complex.normSq (u s + u (sourceSpinSwap i j s))) =
      2 * sourceSpinMass u + 2 * sourceSwapExpectation i j u := by
  have hpoint (s : SourceSpinBasis n) :
      Complex.normSq (u s + u (sourceSpinSwap i j s)) =
        Complex.normSq (u s) + Complex.normSq (u (sourceSpinSwap i j s)) +
          2 * (star (u s) * u (sourceSpinSwap i j s)).re := by
    simp [Complex.normSq_apply, Complex.mul_re, Complex.star_def]
    ring
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    sourceSpinMass_swap]
  unfold sourceSpinMass sourceSwapExpectation
  ring

theorem sourceSwapExpectation_sub_identity {n : ℕ}
    (i j : Fin n) (u : SourceSpinVector n) :
    (∑ s, Complex.normSq (u s - u (sourceSpinSwap i j s))) =
      2 * sourceSpinMass u - 2 * sourceSwapExpectation i j u := by
  have hpoint (s : SourceSpinBasis n) :
      Complex.normSq (u s - u (sourceSpinSwap i j s)) =
        Complex.normSq (u s) + Complex.normSq (u (sourceSpinSwap i j s)) -
          2 * (star (u s) * u (sourceSpinSwap i j s)).re := by
    simp [Complex.normSq_apply, Complex.mul_re, Complex.star_def]
    ring
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    sourceSpinMass_swap]
  unfold sourceSpinMass sourceSwapExpectation
  ring

theorem sourceSwapExpectation_bounds {n : ℕ}
    (i j : Fin n) (u : SourceSpinVector n) :
    -sourceSpinMass u ≤ sourceSwapExpectation i j u ∧
      sourceSwapExpectation i j u ≤ sourceSpinMass u := by
  have hp := sourceSwapExpectation_add_identity i j u
  have hm := sourceSwapExpectation_sub_identity i j u
  have hp0 : 0 ≤ ∑ s, Complex.normSq (u s + u (sourceSpinSwap i j s)) :=
    Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  have hm0 : 0 ≤ ∑ s, Complex.normSq (u s - u (sourceSpinSwap i j s)) :=
    Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  constructor <;> linarith

/-- The local Heisenberg action on the complete `n`-spin Hilbert space. -/
def sourceHeisenbergAction {n : ℕ} (i j : Fin n) (u : SourceSpinVector n) :
    SourceSpinVector n :=
  fun s => 2 * u (sourceSpinSwap i j s) - u s

/-- The real quadratic form of the local Heisenberg interaction. -/
def sourceHeisenbergForm {n : ℕ} (i j : Fin n) (u : SourceSpinVector n) : ℝ :=
  ∑ s, (star (u s) * sourceHeisenbergAction i j u s).re

theorem sourceHeisenbergForm_eq {n : ℕ}
    (i j : Fin n) (u : SourceSpinVector n) :
    sourceHeisenbergForm i j u =
      2 * sourceSwapExpectation i j u - sourceSpinMass u := by
  have hpoint (s : SourceSpinBasis n) :
      (star (u s) * sourceHeisenbergAction i j u s).re =
        2 * (star (u s) * u (sourceSpinSwap i j s)).re - Complex.normSq (u s) := by
    simp [sourceHeisenbergAction, Complex.mul_re, Complex.normSq_apply, Complex.star_def]
    ring
  simp only [sourceHeisenbergForm, hpoint, Finset.sum_sub_distrib,
    ← Finset.mul_sum, sourceSwapExpectation, sourceSpinMass]

theorem sourceHeisenbergForm_bounds {n : ℕ}
    (i j : Fin n) (u : SourceSpinVector n) :
    -3 * sourceSpinMass u ≤ sourceHeisenbergForm i j u ∧
      sourceHeisenbergForm i j u ≤ sourceSpinMass u := by
  obtain ⟨hl, hu⟩ := sourceSwapExpectation_bounds i j u
  rw [sourceHeisenbergForm_eq]
  constructor <;> linarith

theorem sourceHeisenbergForm_abs_le {n : ℕ}
    (i j : Fin n) (u : SourceSpinVector n) :
    |sourceHeisenbergForm i j u| ≤ 3 * sourceSpinMass u := by
  obtain ⟨hl, hu⟩ := sourceHeisenbergForm_bounds i j u
  have hn := sourceSpinMass_nonneg u
  apply abs_le.mpr
  constructor <;> linarith

/-- The signed rational field-free square-lattice source input.  Polynomial
size/weight bounds are properties of the published reduction, not extra
one-site terms or restrictions on the variational spin states. -/
structure SquareLatticeHeisenberg where
  vertices : ℕ
  vertices_pos : 0 < vertices
  coordinate : Fin vertices → ℤ × ℤ
  coordinate_injective : Function.Injective coordinate
  edges : ℕ
  left : Fin edges → Fin vertices
  right : Fin edges → Fin vertices
  adjacent : ∀ e,
    Int.natAbs ((coordinate (left e)).1 - (coordinate (right e)).1) +
      Int.natAbs ((coordinate (left e)).2 - (coordinate (right e)).2) = 1
  edge_simple : ∀ e f, e ≠ f →
    ¬(left e = left f ∧ right e = right f) ∧
      ¬(left e = right f ∧ right e = left f)
  coefficient : Fin edges → ℚ
  lower : ℚ
  upper : ℚ
  gap_pos : lower < upper

theorem SquareLatticeHeisenberg.edge_ne (d : SquareLatticeHeisenberg)
    (e : Fin d.edges) : d.left e ≠ d.right e := by
  intro heq
  have h := d.adjacent e
  rw [heq] at h
  simp at h

def sourceHamiltonianForm (d : SquareLatticeHeisenberg)
    (u : SourceSpinVector d.vertices) : ℝ :=
  ∑ e, (d.coefficient e : ℝ) * sourceHeisenbergForm (d.left e) (d.right e) u

/-- Variational source energy over all normalized spin states. -/
def sourceGroundEnergy (d : SquareLatticeHeisenberg) : EReal :=
  sInf {e | ∃ u : SourceSpinVector d.vertices,
    sourceSpinMass u = 1 ∧ e = (sourceHamiltonianForm d u : EReal)}

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourcePauli
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual one-site Pauli matrices on the complete source spin basis. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators

def sourceHeisenbergMatrix (n : ℕ) (i j : Fin n) :
    Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ := fun s t =>
  2 * (if sourceSpinSwap i j s = t then 1 else 0) - (if s = t then 1 else 0)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Source spectral bottom and rational normalization

The bottom ranges over every normalized many-spin vector. Uniform
coefficient error controls that variational bottom and the YES/NO
thresholds of the square-lattice Heisenberg problem.
-/

noncomputable section

namespace ContinuumCoulomb

open scoped BigOperators

def allUpSourceBasis (n : ℕ) : SourceSpinBasis n := fun _ => 0

def allUpSourceVector (n : ℕ) : SourceSpinVector n :=
  fun s => if s = allUpSourceBasis n then 1 else 0

theorem allUpSourceVector_mass (n : ℕ) : sourceSpinMass (allUpSourceVector n) = 1 := by
  classical
  simp [sourceSpinMass, allUpSourceVector]

/-- Uniform form bound for the complete signed source Hamiltonian. -/
theorem sourceHamiltonianForm_abs_le (d : SquareLatticeHeisenberg)
    (u : SourceSpinVector d.vertices) :
    |sourceHamiltonianForm d u| ≤
      (3 * ∑ e, |(d.coefficient e : ℝ)|) * sourceSpinMass u := by
  unfold sourceHamiltonianForm
  calc
    |∑ e, (d.coefficient e : ℝ) * sourceHeisenbergForm (d.left e) (d.right e) u| ≤
        ∑ e, |(d.coefficient e : ℝ) * sourceHeisenbergForm (d.left e) (d.right e) u| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ e, |(d.coefficient e : ℝ)| * (3 * sourceSpinMass u) := by
      apply Finset.sum_le_sum
      intro e _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        (sourceHeisenbergForm_abs_le (d.left e) (d.right e) u) (abs_nonneg _)
    _ = (3 * ∑ e, |(d.coefficient e : ℝ)|) * sourceSpinMass u := by
      rw [← Finset.sum_mul]
      ring

theorem sourceGroundEnergy_le_trial (d : SquareLatticeHeisenberg)
    (u : SourceSpinVector d.vertices) (hu : sourceSpinMass u = 1) :
    sourceGroundEnergy d ≤ (sourceHamiltonianForm d u : EReal) :=
  sInf_le ⟨u, hu, rfl⟩

theorem sourceGroundEnergy_lower_of_forall (d : SquareLatticeHeisenberg)
    (a : ℝ)
    (ha : ∀ u : SourceSpinVector d.vertices, sourceSpinMass u = 1 →
      a ≤ sourceHamiltonianForm d u) :
    (a : EReal) ≤ sourceGroundEnergy d := by
  apply le_sInf
  rintro e ⟨u, hu, rfl⟩
  exact EReal.coe_le_coe (ha u hu)

theorem sourceGroundEnergy_lower_bound (d : SquareLatticeHeisenberg) :
    (-(3 * ∑ e, |(d.coefficient e : ℝ)|) : ℝ) ≤ sourceGroundEnergy d := by
  apply sourceGroundEnergy_lower_of_forall
  intro u hu
  have h := (abs_le.mp (sourceHamiltonianForm_abs_le d u)).1
  simpa only [hu, mul_one] using h

theorem sourceGroundEnergy_ne_bot (d : SquareLatticeHeisenberg) :
    sourceGroundEnergy d ≠ ⊥ :=
  ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (sourceGroundEnergy_lower_bound d)

theorem sourceGroundEnergy_ne_top (d : SquareLatticeHeisenberg) :
    sourceGroundEnergy d ≠ ⊤ :=
  ne_top_of_le_ne_top (EReal.coe_ne_top _)
    (sourceGroundEnergy_le_trial d (allUpSourceVector d.vertices)
      (allUpSourceVector_mass d.vertices))

/-- The finite source bottom, now known to be a real number. -/
def realSourceGroundEnergy (d : SquareLatticeHeisenberg) : ℝ :=
  (sourceGroundEnergy d).toReal

theorem realSourceGroundEnergy_coe (d : SquareLatticeHeisenberg) :
    (realSourceGroundEnergy d : EReal) = sourceGroundEnergy d :=
  EReal.coe_toReal (sourceGroundEnergy_ne_top d) (sourceGroundEnergy_ne_bot d)

theorem realSourceGroundEnergy_le_trial (d : SquareLatticeHeisenberg)
    (u : SourceSpinVector d.vertices) (hu : sourceSpinMass u = 1) :
    realSourceGroundEnergy d ≤ sourceHamiltonianForm d u := by
  apply EReal.coe_le_coe_iff.mp
  rw [realSourceGroundEnergy_coe]
  exact sourceGroundEnergy_le_trial d u hu

theorem realSourceGroundEnergy_lower_of_forall (d : SquareLatticeHeisenberg)
    (a : ℝ)
    (ha : ∀ u : SourceSpinVector d.vertices, sourceSpinMass u = 1 →
      a ≤ sourceHamiltonianForm d u) :
    a ≤ realSourceGroundEnergy d := by
  apply EReal.coe_le_coe_iff.mp
  rw [realSourceGroundEnergy_coe]
  exact sourceGroundEnergy_lower_of_forall d a ha

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourcePromise
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite binary input and promise language for the published signed,
field-free square-lattice Heisenberg problem. Invalid encodings and inputs
outside the energy promise belong to neither promise set. -/

namespace ContinuumCoulomb
open BinaryEncoding

def BinaryRational.ofRat (q : ℚ) : BinaryRational := ⟨q.num, q.den⟩

@[simp] theorem BinaryRational.value_ofRat (q : ℚ) : (BinaryRational.ofRat q).value = q := by
  exact Rat.num_div_den q

structure BinaryHeisenbergEdge where
  left : ℕ
  right : ℕ
  coefficient : BinaryRational
  deriving DecidableEq, Repr

def binaryHeisenbergEdgeEquiv : BinaryHeisenbergEdge ≃ (ℕ × (ℕ × BinaryRational)) where
  toFun e := (e.left, e.right, e.coefficient)
  invFun e := ⟨e.1, e.2.1, e.2.2⟩
  left_inv e := by cases e; rfl
  right_inv e := by rcases e with ⟨i, j, q⟩; rfl

def binaryHeisenbergEdgeCodec : Codec BinaryHeisenbergEdge := BinaryEncoding.equiv
  (pair natural (pair natural binaryRationalCodec)) binaryHeisenbergEdgeEquiv

structure BinaryHeisenberg where
  coordinate : List (ℤ × ℤ)
  edges : List BinaryHeisenbergEdge
  lower : BinaryRational
  upper : BinaryRational
  deriving DecidableEq, Repr

def binaryHeisenbergEquiv : BinaryHeisenberg ≃
    (List (ℤ × ℤ) × (List BinaryHeisenbergEdge × (BinaryRational × BinaryRational))) where
  toFun d := (d.coordinate, d.edges, d.lower, d.upper)
  invFun d := ⟨d.1, d.2.1, d.2.2.1, d.2.2.2⟩
  left_inv d := by cases d; rfl
  right_inv d := by rcases d with ⟨cs, es, a, b⟩; rfl

def binaryHeisenbergCodec : Codec BinaryHeisenberg := BinaryEncoding.equiv
  (pair (BinaryEncoding.list (pair integer integer))
    (pair (BinaryEncoding.list binaryHeisenbergEdgeCodec) (pair binaryRationalCodec binaryRationalCodec)))
      binaryHeisenbergEquiv

structure BinaryHeisenberg.Valid (d : BinaryHeisenberg) : Prop where
  vertices_pos : 0 < d.coordinate.length
  coordinate_nodup : d.coordinate.Nodup
  bounds : ∀ e : Fin d.edges.length,
    (d.edges.get e).left < d.coordinate.length ∧ (d.edges.get e).right < d.coordinate.length
  denominators : ∀ e : Fin d.edges.length, 0 < (d.edges.get e).coefficient.denominator
  adjacent : ∀ e : Fin d.edges.length,
    Int.natAbs ((d.coordinate.getD (d.edges.get e).left (0, 0)).1 -
      (d.coordinate.getD (d.edges.get e).right (0, 0)).1) +
    Int.natAbs ((d.coordinate.getD (d.edges.get e).left (0, 0)).2 -
      (d.coordinate.getD (d.edges.get e).right (0, 0)).2) = 1
  simple : ∀ e f : Fin d.edges.length, e ≠ f →
    ¬((d.edges.get e).left = (d.edges.get f).left ∧ (d.edges.get e).right = (d.edges.get f).right) ∧
    ¬((d.edges.get e).left = (d.edges.get f).right ∧ (d.edges.get e).right = (d.edges.get f).left)
  lower_denominator : 0 < d.lower.denominator
  upper_denominator : 0 < d.upper.denominator
  gap : d.lower.value < d.upper.value

/-- Decode valid finite data into the existing actual spin Hamiltonian. -/
def BinaryHeisenberg.toSource (d : BinaryHeisenberg) (h : d.Valid) : SquareLatticeHeisenberg where
  vertices := d.coordinate.length
  vertices_pos := h.vertices_pos
  coordinate := d.coordinate.get
  coordinate_injective := h.coordinate_nodup.injective_get
  edges := d.edges.length
  left e := ⟨(d.edges.get e).left, (h.bounds e).1⟩
  right e := ⟨(d.edges.get e).right, (h.bounds e).2⟩
  adjacent e := by
    have ha := h.adjacent e
    rw [List.getD_eq_get d.coordinate (0, 0) ⟨(d.edges.get e).left, (h.bounds e).1⟩,
      List.getD_eq_get d.coordinate (0, 0) ⟨(d.edges.get e).right, (h.bounds e).2⟩] at ha
    exact ha
  edge_simple e f hne := by
    have hs := h.simple e f hne
    constructor
    · rintro ⟨hl, hr⟩
      exact hs.1 ⟨congrArg Fin.val hl, congrArg Fin.val hr⟩
    · rintro ⟨hl, hr⟩
      exact hs.2 ⟨congrArg Fin.val hl, congrArg Fin.val hr⟩
  coefficient e := (d.edges.get e).coefficient.value
  lower := d.lower.value
  upper := d.upper.value
  gap_pos := h.gap

/-- A single fixed exponent bounds lattice extent, source weights and inverse
gap, as in the polynomial-weight spatially sparse source branch. -/
structure BinaryHeisenberg.PolynomialPromise (k : ℕ) (d : BinaryHeisenberg) : Prop where
  coordinate_bound : ∀ p ∈ d.coordinate,
    |(p.1 : ℝ)| ≤ ((binaryHeisenbergCodec.encode d).length + 1 : ℝ) ^ k ∧
      |(p.2 : ℝ)| ≤ ((binaryHeisenbergCodec.encode d).length + 1 : ℝ) ^ k
  weight_bound : ∀ e : Fin d.edges.length, |((d.edges.get e).coefficient.value : ℝ)| ≤
    ((binaryHeisenbergCodec.encode d).length + 1 : ℝ) ^ k
  gap_bound : (((binaryHeisenbergCodec.encode d).length + 1 : ℝ) ^ k)⁻¹ ≤
    (d.upper.value : ℝ) - d.lower.value

noncomputable section

def sourceHeisenbergPromise (k : ℕ) : PromiseProblem BinaryHeisenberg where
  yes := {d | ∃ h : d.Valid, d.PolynomialPromise k ∧
    sourceGroundEnergy (d.toSource h) ≤ ((d.lower.value : ℝ) : EReal)}
  no := {d | ∃ h : d.Valid, d.PolynomialPromise k ∧
    ((d.upper.value : ℝ) : EReal) ≤ sourceGroundEnergy (d.toSource h)}
  disjoint := by
    apply Set.disjoint_left.mpr
    rintro d ⟨h, _, hyes⟩ ⟨h', _, hno⟩
    have hab : ((d.upper.value : ℝ) : EReal) ≤ ((d.lower.value : ℝ) : EReal) := hno.trans hyes
    have hgap : ((d.lower.value : ℝ) : EReal) < ((d.upper.value : ℝ) : EReal) := by
      exact_mod_cast h.gap
    exact (not_le_of_gt hgap) hab

/-- Field-free signed square-lattice Heisenberg hardness of
Cubitt–Montanaro–Piddock, arXiv:1701.05182v4, Theorem 48 and Section 10.1,
with the polynomial-weight sparse construction of Lemma 47. -/
def PublishedCMPHardness : Prop :=
  ∃ k : ℕ, 0 < k ∧ QMAHard binaryHeisenbergCodec.encode (sourceHeisenbergPromise k)

end
end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_FieldAnalysis_DeterminantWave
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

noncomputable def determinantWave {A : Type*} {n : ℕ} (v : Fin n → A → ℂ)
    (x : Fin n → A) : ℂ := Matrix.det (fun i j => v i (x j))

noncomputable def slaterWave {A : Type*} {n : ℕ} (v : Fin n → A → ℂ)
    (x : Fin n → A) : ℂ := (↑(Real.sqrt (n.factorial : ℝ))⁻¹ : ℂ) * determinantWave v x

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ApproximateBisection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Approximate rational bisection for a Lipschitz residual.  A numerically
ambiguous sign terminates with a certified residual bound; otherwise the
true endpoint signs are preserved.  No monotonicity or derivative lower
bound is required. -/

namespace ContinuumCoulomb.ApproximateBisection

structure Interval where
  lo : ℚ
  hi : ℚ
  settled : Bool
  deriving DecidableEq

def midpoint (s : Interval) : ℚ := (s.lo + s.hi) / 2

def width (s : Interval) : ℝ := (s.hi : ℝ) - s.lo

def step (δ : ℚ) (evaluate : ℚ → ℚ) (s : Interval) : Interval :=
  if s.settled then s
  else if δ < evaluate (midpoint s) then ⟨midpoint s, s.hi, false⟩
  else if evaluate (midpoint s) < -δ then ⟨s.lo, midpoint s, false⟩
  else ⟨midpoint s, midpoint s, true⟩

def initial (a b : ℚ) : Interval := ⟨a, b, false⟩

def run (δ : ℚ) (evaluate : ℚ → ℚ) (a b : ℚ) (n : ℕ) : Interval :=
  (step δ evaluate)^[n] (initial a b)

@[simp] theorem midpoint_cast (s : Interval) :
    (midpoint s : ℝ) = ((s.lo : ℝ) + s.hi) / 2 := by
  simp [midpoint]

/-- The invariant concerns actual residual values, not numerical signs. -/
structure Invariant (a b : ℚ) (f : ℝ → ℝ) (δ : ℚ) (s : Interval) : Prop where
  lower : a ≤ s.lo
  upper : s.hi ≤ b
  ordered : s.lo ≤ s.hi
  certified : s.settled = true → s.lo = s.hi ∧ |f s.lo| ≤ 2 * (δ : ℝ)
  signs : s.settled = false → 0 ≤ f s.lo ∧ f s.hi ≤ 0

end ContinuumCoulomb.ApproximateBisection

end OAI
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

abbrev Config (K Λ : Type) := Cfg (fun _ : K => Bool) Λ (Option Bool)
def jump {K Λ : Type} (l : Λ) : Stmt (fun _ : K => Bool) Λ (Option Bool) :=
  .load (fun _ => none) (.goto (fun _ => l))
def dispatch {K Λ : Type} (k : K) (nil ff tt : Λ) :
    Stmt (fun _ : K => Bool) Λ (Option Bool) :=
  .pop k (fun _ b => b) (.branch Option.isSome
    (.branch (fun b => b.getD false) (jump tt) (jump ff)) (jump nil))

lemma iterate_step {α : Type*} (f : α → Option α) (a b : α) (h : f a=some b) :
    (flip bind f)^[1] (some a) = some b := h
lemma iterate_comp {α : Type*} (f : α → Option α) (a b c : α) (k l : ℕ)
    (h : (flip bind f)^[k] (some a)=some b)
    (g : (flip bind f)^[l] (some b)=some c) :
    (flip bind f)^[l+k] (some a)=some c := by
  rw [Function.iterate_add_apply,h,g]

end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_BitStackUnary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram

lemma pred_iterate_word (i n : ℕ) : (fun k=>k-1)^[i] n=n-i := by
  induction i with
  | zero=>simp
  | succ i ih=>
    rw [Function.iterate_succ_apply',ih,Nat.sub_sub]

end ExactQuantumFactoring.BitStackProgram

end


end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_BitStackMultiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram

lemma bits_length_add (a b : ℕ) : (a+b).bits.length≤a.bits.length+b.bits.length+1 := by
  rw [Nat.size_eq_bits_len,Nat.size_le]
  have ha:=Nat.lt_size_self a
  have hb:=Nat.lt_size_self b
  have hap : 2^a.size≤2^(a.bits.length+b.bits.length):=by
    apply Nat.pow_le_pow_right (by omega)
    simp only [Nat.size_eq_bits_len];omega
  have hbp : 2^b.size≤2^(a.bits.length+b.bits.length):=by
    apply Nat.pow_le_pow_right (by omega)
    simp only [Nat.size_eq_bits_len];omega
  rw [pow_succ]
  omega

lemma bits_length_mul (a b : ℕ) : (a*b).bits.length≤a.bits.length+b.bits.length := by
  rw [Nat.size_eq_bits_len,Nat.size_le,pow_add]
  have h:=Nat.mul_lt_mul_of_lt_of_lt (Nat.lt_size_self a) (Nat.lt_size_self b)
  simpa only [Nat.size_eq_bits_len] using h

lemma bits_length_pow2 (n : ℕ) : (2^n).bits.length=n+1 := by
  rw [Nat.size_eq_bits_len,Nat.size_pow]

def mulZeroStep (x : ℕ×ℕ) : ℕ×ℕ := (x.1,2*x.2)
def mulOneStep (x : ℕ×ℕ) : ℕ×ℕ := (x.1,2*x.2+x.1)

end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_BitStackIntegers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram

def signedAdd (x : (Bool×ℕ)×(Bool×ℕ)) : Bool×ℕ :=
  if x.1.1=x.2.1 then (x.1.1,x.1.2+x.2.2)
  else if x.1.2≤x.2.2 then (x.2.1,x.2.2-x.1.2) else (x.1.1,x.1.2-x.2.2)

end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_BisectionRegisters
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

abbrev Registers := ℤ × (ℤ × (ℕ × Bool))

def left (r : Registers) : ℚ := mkRat r.1 r.2.2.1
def right (r : Registers) : ℚ := mkRat r.2.1 r.2.2.1
def middle (r : Registers) : ℚ := mkRat (r.1 + r.2.1) (2 * r.2.2.1)

def interval (r : Registers) : ApproximateBisection.Interval :=
  ⟨left r, right r, r.2.2.2⟩

def step (δ : ℚ) (evaluate : ℚ → ℚ) (r : Registers) : Registers :=
  if r.2.2.2 then r
  else if δ < evaluate (middle r) then
    (r.1 + r.2.1, (2 * r.2.1, (2 * r.2.2.1, false)))
  else if evaluate (middle r) < -δ then
    (2 * r.1, (r.1 + r.2.1, (2 * r.2.2.1, false)))
  else (r.1 + r.2.1, (r.1 + r.2.1, (2 * r.2.2.1, true)))

def initial (a b : ℚ) : Registers :=
  (a.num * b.den, (b.num * a.den, (a.den * b.den, false)))

def bits (r : Registers) : ℕ :=
  max (max r.1.natAbs.bits.length r.2.1.natAbs.bits.length) r.2.2.1.bits.length

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

abbrev Config (E : Type) := E × (ℚ × Registers)

def advance {E : Type} (evaluate : E → ℚ → ℚ) (s : Config E) : Config E :=
  (s.1, (s.2.1, step s.2.1 (evaluate s.1) s.2.2))

theorem iterate_config {E : Type} (evaluate : E → ℚ → ℚ) (s : Config E) (n : ℕ) :
    (advance evaluate)^[n] s =
      (s.1, (s.2.1, (step s.2.1 (evaluate s.1))^[n] s.2.2)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
    rfl

abbrev Input (E : Type) := ℕ × (E × (ℚ × (ℚ × ℚ)))

def approximate {E : Type} (evaluate : E → ℚ → ℚ) (x : Input E) : ℚ :=
  middle ((step x.2.2.1 (evaluate x.2.1))^[x.1] (initial x.2.2.2.1 x.2.2.2.2))

end ContinuumCoulomb.BisectionProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.Laughlin_Operators_CAR
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock

abbrev Orbital (Q : ℕ) := Fin (Q+1) → ℂ
abbrev Space (Q : ℕ) := ExteriorAlgebra ℂ (Orbital Q)

noncomputable def mode {Q : ℕ} (i : Fin (Q+1)) : Orbital Q := Pi.single i 1

noncomputable def create {Q : ℕ} (i : Fin (Q+1)) : Module.End ℂ (Space Q) where
  toFun x := ExteriorAlgebra.ι ℂ (mode i) * x
  map_add' x y := mul_add _ x y
  map_smul' c x := by simp

noncomputable def annihilate {Q : ℕ} (i : Fin (Q+1)) : Module.End ℂ (Space Q) :=
  CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ (Orbital Q))) (LinearMap.proj i : Module.Dual ℂ (Orbital Q))

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_HubbardGlobal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Global finite-fermion identities for the Hubbard reduction

These are identities of actual creation and contraction operators on
the finite exterior algebra.  They retain every spectator mode and
therefore do not assume transition signs from the two-site calculation.
-/

noncomputable section

namespace ContinuumCoulomb.HubbardGlobal

open Laughlin.Fock
open scoped BigOperators

variable {Q : ℕ}

def transfer (i j : Fin (Q + 1)) : Module.End ℂ (Space Q) :=
  create i * annihilate j

def number (i : Fin (Q + 1)) : Module.End ℂ (Space Q) := transfer i i

def totalNumber (Q : ℕ) : Module.End ℂ (Space Q) := ∑ i, number i

def bondTransfer (i j : Fin (Q + 1)) : Module.End ℂ (Space Q) :=
  transfer i j + transfer j i

def spinSwap (a b c d : Fin (Q + 1)) : Module.End ℂ (Space Q) :=
  number a * number c + number b * number d +
    transfer a b * transfer d c + transfer c d * transfer b a

def twoSiteHopping (a b c d : Fin (Q + 1)) : Module.End ℂ (Space Q) :=
  bondTransfer a c + bondTransfer b d

def siteHeisenberg (a b c d : Fin (Q + 1)) : Module.End ℂ (Space Q) :=
  (2 : ℂ) • spinSwap a b c d - 1

def densityInteraction (v : Fin (Q + 1) → Fin (Q + 1) → ℂ) : Module.End ℂ (Space Q) :=
  ∑ i, ∑ j, v i j • (number i * number j)

end ContinuumCoulomb.HubbardGlobal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_HubbardOccupation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual occupation-basis diagonal action for the global Hubbard model. -/

noncomputable section
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock
open scoped BigOperators
variable {Q : ℕ}

def fockBasis (Q : ℕ) : Module.Basis (Finset (Fin (Q + 1))) ℂ (Space Q) :=
  (Pi.basisFun ℂ (Fin (Q + 1))).ExteriorAlgebra

end ContinuumCoulomb.HubbardGlobal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_HubbardSpin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identifying the singly occupied exterior sector with the spin model. -/

noncomputable section
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock
open scoped BigOperators

variable {Q : ℕ}

def wedgeModes (n : ℕ) (v : Fin n → Fin (Q + 1)) : Space Q :=
  ExteriorAlgebra.ιMulti ℂ n (fun k => mode (v k))

def siteModes (m : ℕ) : Fin (m + 1) × Fin 2 ≃ Fin ((2 * m + 1) + 1) :=
  finProdFinEquiv.trans (Fin.castOrderIso (by omega)).toEquiv

def siteMode (m : ℕ) (i : Fin (m + 1)) (σ : Fin 2) : Fin ((2 * m + 1) + 1) :=
  siteModes m (i, σ)

def spinWedge (m : ℕ) (s : Fin (m + 1) → Fin 2) : Space (2 * m + 1) :=
  wedgeModes (m + 1) (fun i => siteMode m i (s i))

end ContinuumCoulomb.HubbardGlobal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_HubbardExcitation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual occupation-diagonal inverse and charge-selection rules. -/

noncomputable section
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock
open scoped BigOperators

variable {Q : ℕ}

def fockDiagonal (f : Finset (Fin (Q + 1)) → ℂ) : Module.End ℂ (Space Q) :=
  (fockBasis Q).constr ℂ (fun A => f A • fockBasis Q A)

def siteNumber (m : ℕ) (i : Fin (m + 1)) : Module.End ℂ (Space (2 * m + 1)) :=
  number (siteMode m i 0) + number (siteMode m i 1)

def occupationAt (m : ℕ) (A : Finset (Fin ((2 * m + 1) + 1))) (i : Fin (m + 1)) : Fin 3 :=
  ⟨(if siteMode m i 0 ∈ A then 1 else 0) + (if siteMode m i 1 ∈ A then 1 else 0),
    by split_ifs <;> omega⟩

def occupationDiagonal (m : ℕ) (f : (Fin (m + 1) → Fin 3) → ℂ) :
    Module.End ℂ (Space (2 * m + 1)) := fockDiagonal (fun A => f (occupationAt m A))

def lowProjection (m : ℕ) : Module.End ℂ (Space (2 * m + 1)) :=
  occupationDiagonal m (fun o => if ∀ i, o i = 1 then 1 else 0)

def chargeInverse (m : ℕ) (U : ℝ) (V : Fin (m + 1) → Fin (m + 1) → ℝ) :
    Module.End ℂ (Space (2 * m + 1)) :=
  occupationDiagonal m (fun o => ((chargePenalty U V o)⁻¹ : ℝ))

def chargeShift {m : ℕ} (k i j : Fin (m + 1)) : ℂ :=
  (if k = i then 1 else 0) - (if k = j then 1 else 0)

def siteHopping (m : ℕ) (i j : Fin (m + 1)) : Module.End ℂ (Space (2 * m + 1)) :=
  twoSiteHopping (siteMode m i 0) (siteMode m i 1) (siteMode m j 0) (siteMode m j 1)

end ContinuumCoulomb.HubbardGlobal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_GlobalSuperexchange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact global Hubbard second-order compression on the spin sector. -/

noncomputable section
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock
open scoped BigOperators

variable {Edge : Type*} [Fintype Edge]

def graphHopping (m : ℕ) (left right : Edge → Fin (m + 1)) (t : Edge → ℂ) :
    Module.End ℂ (Space (2 * m + 1)) := ∑ e, t e • siteHopping m (left e) (right e)

end ContinuumCoulomb.HubbardGlobal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_SpinEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The canonical, norm-preserving embedding of the spin sector in Fock space. -/

noncomputable section
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock
open scoped BigOperators

theorem siteMode_val (m : ℕ) (i : Fin (m + 1)) (σ : Fin 2) :
    (siteMode m i σ : ℕ) = (σ : ℕ) + 2 * (i : ℕ) := rfl

def spinModeOrderEmbedding (m : ℕ) (s : SourceSpinBasis (m + 1)) :
    Fin (m + 1) ↪o Fin ((2 * m + 1) + 1) :=
  OrderEmbedding.ofStrictMono (fun i => siteMode m i (s i)) (by
    intro i j hij
    apply Fin.lt_def.mpr
    rw [siteMode_val, siteMode_val]
    have hi := (s i).isLt
    have hj := (s j).isLt
    have hij' := Fin.lt_def.mp hij
    omega)

def spinOccupationSet (m : ℕ) (s : SourceSpinBasis (m + 1)) :
    Finset (Fin ((2 * m + 1) + 1)) :=
  (Set.powersetCard.ofFinEmbEquiv (spinModeOrderEmbedding m s)).val

def spinEmbedding (m : ℕ) : SourceSpinVector (m + 1) →ₗ[ℂ] Space (2 * m + 1) where
  toFun u := ∑ s, u s • spinWedge m s
  map_add' u v := by simp [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c u := by simp [Pi.smul_apply, smul_smul, Finset.smul_sum]

def fockMass {Q : ℕ} (x : Space Q) : ℝ :=
  ∑ A, Complex.normSq ((fockBasis Q).repr x A)

end ContinuumCoulomb.HubbardGlobal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_FockNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial operator bounds from the actual exterior occupation basis. -/

noncomputable section
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock
open scoped BigOperators InnerProductSpace
variable {Q : ℕ}

def creationCoefficient (i : Fin (Q + 1)) (A : Finset (Fin (Q + 1))) : ℂ :=
  (fockBasis Q).repr (create i (fockBasis Q A)) (insert i A)

def insertModeEquiv (i : Fin (Q + 1)) :
    {A : Finset (Fin (Q + 1)) // i ∉ A} ≃ {A : Finset (Fin (Q + 1)) // i ∈ A} where
  toFun A := ⟨insert i A.val, Finset.mem_insert_self _ _⟩
  invFun A := ⟨A.val.erase i, Finset.notMem_erase _ _⟩
  left_inv A := Subtype.ext (Finset.erase_insert A.property)
  right_inv A := Subtype.ext (Finset.insert_erase A.property)

@[simp] theorem insertModeEquiv_val (i : Fin (Q + 1))
    (A : {A : Finset (Fin (Q + 1)) // i ∉ A}) :
    (insertModeEquiv i A).val = insert i A.val := rfl

@[simp] theorem insertModeEquiv_erase (i : Fin (Q + 1))
    (A : {A : Finset (Fin (Q + 1)) // i ∉ A}) :
    (insertModeEquiv i A).val.erase i = A.val := Finset.erase_insert A.property

@[simp] theorem insertModeEquiv_symm_insert (i : Fin (Q + 1))
    (A : {A : Finset (Fin (Q + 1)) // i ∈ A}) :
    insert i ((insertModeEquiv i).symm A).val = A.val := Finset.insert_erase A.property

abbrev FockCoordinateSpace (Q : ℕ) := EuclideanSpace ℂ (Finset (Fin (Q + 1)))

def fockCoordinates (Q : ℕ) : Space Q ≃ₗ[ℂ] FockCoordinateSpace Q :=
  (fockBasis Q).equivFun.trans (WithLp.linearEquiv 2 ℂ _).symm

@[simp] theorem fockCoordinates_apply (x : Space Q) (A : Finset (Fin (Q + 1))) :
    fockCoordinates Q x A = (fockBasis Q).repr x A := rfl

def fockOperatorLinear (T : Module.End ℂ (Space Q)) :
    Module.End ℂ (FockCoordinateSpace Q) :=
  (fockCoordinates Q).toLinearMap.comp (T.comp (fockCoordinates Q).symm.toLinearMap)

def fockOperator (T : Module.End ℂ (Space Q)) :
    FockCoordinateSpace Q →L[ℂ] FockCoordinateSpace Q :=
  LinearMap.toContinuousLinearMap (fockOperatorLinear T)

@[simp] theorem fockOperator_coordinates (T : Module.End ℂ (Space Q)) (x : Space Q) :
    fockOperator T (fockCoordinates Q x) = fockCoordinates Q (T x) := by
  simp [fockOperator, fockOperatorLinear]

@[simp] theorem fockOperator_add (T S : Module.End ℂ (Space Q)) :
    fockOperator (T + S) = fockOperator T + fockOperator S := by
  ext v
  obtain ⟨x, rfl⟩ := (fockCoordinates Q).surjective v
  simp only [fockOperator_coordinates, add_apply,
    LinearMap.add_apply, map_add]

@[simp] theorem fockOperator_smul (c : ℂ) (T : Module.End ℂ (Space Q)) :
    fockOperator (c • T) = c • fockOperator T := by
  ext v
  obtain ⟨x, rfl⟩ := (fockCoordinates Q).surjective v
  simp only [fockOperator_coordinates, smul_apply,
    LinearMap.smul_apply, map_smul]

@[simp] theorem fockOperator_mul (T S : Module.End ℂ (Space Q)) :
    fockOperator (T * S) = (fockOperator T).comp (fockOperator S) := by
  ext v
  obtain ⟨x, rfl⟩ := (fockCoordinates Q).surjective v
  simp only [fockOperator_coordinates, ContinuousLinearMap.comp_apply,
    Module.End.mul_apply]

end ContinuumCoulomb.HubbardGlobal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_HalfFilledSector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual half-filled occupation basis splits into spins and charge defects. -/

noncomputable section
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock
open scoped BigOperators

def occupationSpin (m : ℕ) (A : Finset (Fin ((2 * m + 1) + 1))) :
    SourceSpinBasis (m + 1) :=
  fun i => if siteMode m i 0 ∈ A then 0 else 1

abbrev HalfFilledBasis (m : ℕ) :=
  {A : Finset (Fin ((2 * m + 1) + 1)) // A.card = m + 1}

abbrev HalfFilledHighBasis (m : ℕ) :=
  {A : HalfFilledBasis m // ¬ ∀ i, occupationAt m A.val i = 1}

end ContinuumCoulomb.HubbardGlobal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_HubbardReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Second-order estimate with the global charge penalty

The occupation configurations determine the penalty, its inverse, its
positivity and its spectral gap. The resulting bottom-energy comparison
retains every electron and spin configuration.
-/

noncomputable section
open scoped BigOperators InnerProductSpace
namespace ContinuumCoulomb

abbrev HubbardLowSpace (m : ℕ) := EuclideanSpace ℂ (Fin m → Fin 2)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_FockBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete hopping blocks on the actual half-filled Fock basis. -/

noncomputable section
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock
open scoped BigOperators InnerProductSpace

section Coordinates
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

def coordinateInclusionLinear (f : α → β) :
    EuclideanSpace ℂ α →ₗ[ℂ] EuclideanSpace ℂ β := by
  classical
  exact
    { toFun := fun x => ∑ a, x a • EuclideanSpace.single (f a) 1
      map_add' := fun x y => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun c x => by simp [smul_smul, Finset.smul_sum] }

def coordinateInclusion (f : α → β) :
    EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ β :=
  LinearMap.toContinuousLinearMap (coordinateInclusionLinear f)

theorem coordinateInclusion_apply_image (f : α → β) (hf : Function.Injective f)
    (x : EuclideanSpace ℂ α) (a : α) : coordinateInclusion f x (f a) = x a := by
  classical
  simp [coordinateInclusion, coordinateInclusionLinear, Pi.single_apply, hf.eq_iff]

theorem coordinateInclusion_apply_outside (f : α → β)
    (x : EuclideanSpace ℂ α) (b : β) (hb : ∀ a, f a ≠ b) :
    coordinateInclusion f x b = 0 := by
  classical
  simp [coordinateInclusion, coordinateInclusionLinear,
    fun a => Ne.symm (hb a)]

theorem coordinateInclusion_norm_map (f : α → β) (hf : Function.Injective f)
    (x : EuclideanSpace ℂ α) : ‖coordinateInclusion f x‖ = ‖x‖ := by
  classical
  have hsq : ‖coordinateInclusion f x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    let S := Finset.univ.image f
    have hsum : (∑ b ∈ S, ‖coordinateInclusion f x b‖ ^ 2) =
        ∑ b, ‖coordinateInclusion f x b‖ ^ 2 := by
      apply Finset.sum_subset (Finset.subset_univ S)
      intro b _ hb
      have hout : ∀ a, f a ≠ b := by
        intro a ha
        exact hb (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, ha⟩)
      rw [coordinateInclusion_apply_outside f x b hout]
      simp
    rw [← hsum]
    unfold S
    rw [Finset.sum_image]
    · simp only [coordinateInclusion_apply_image f hf]
    · intro a _ b _ hab
      exact hf hab
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

def coordinateRestriction (f : α → β) :
    EuclideanSpace ℂ β →L[ℂ] EuclideanSpace ℂ α := (coordinateInclusion f).adjoint

end Coordinates

abbrev ActualHubbardLowSpace (m : ℕ) := EuclideanSpace ℂ (SourceSpinBasis (m + 1))
abbrev ActualHubbardHighSpace (m : ℕ) := EuclideanSpace ℂ (HalfFilledHighBasis m)

def highOccupationIndex (m : ℕ) (A : HalfFilledHighBasis m) :
    Finset (Fin ((2 * m + 1) + 1)) := A.val.val

def lowFockInclusion (m : ℕ) : ActualHubbardLowSpace m →L[ℂ] FockCoordinateSpace (2 * m + 1) :=
  coordinateInclusion (spinOccupationSet m)

def highFockInclusion (m : ℕ) : ActualHubbardHighSpace m →L[ℂ] FockCoordinateSpace (2 * m + 1) :=
  coordinateInclusion (highOccupationIndex m)

def lowFockRestriction (m : ℕ) : FockCoordinateSpace (2 * m + 1) →L[ℂ] ActualHubbardLowSpace m :=
  coordinateRestriction (spinOccupationSet m)

def highFockRestriction (m : ℕ) : FockCoordinateSpace (2 * m + 1) →L[ℂ] ActualHubbardHighSpace m :=
  coordinateRestriction (highOccupationIndex m)

variable {Edge : Type*} [Fintype Edge]

def actualHubbardCoupling (m : ℕ) (left right : Edge → Fin (m + 1)) (t : Edge → ℝ) :
    ActualHubbardLowSpace m →L[ℝ] ActualHubbardHighSpace m :=
  ((highFockRestriction m).comp
    ((fockOperator (graphHopping m left right (fun e => (t e : ℂ)))).comp
      (lowFockInclusion m))).restrictScalars ℝ

def actualHubbardHighHopping (m : ℕ) (left right : Edge → Fin (m + 1)) (t : Edge → ℝ) :
    ActualHubbardHighSpace m →L[ℝ] ActualHubbardHighSpace m :=
  ((highFockRestriction m).comp
    ((fockOperator (graphHopping m left right (fun e => (t e : ℂ)))).comp
      (highFockInclusion m))).restrictScalars ℝ

end ContinuumCoulomb.HubbardGlobal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_FockSector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed-particle support and the true low/high Fock projections. -/

noncomputable section
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock
open scoped BigOperators InnerProductSpace

variable {Q : ℕ}

def IsHalfFilled (m : ℕ) (x : Space (2 * m + 1)) : Prop :=
  ∀ A, A.card ≠ m + 1 → (fockBasis (2 * m + 1)).repr x A = 0

def highProjection (m : ℕ) : Module.End ℂ (Space (2 * m + 1)) :=
  fockDiagonal (fun A =>
    if A.card = m + 1 ∧ ¬ ∀ i, occupationAt m A i = 1 then 1 else 0)

end ContinuumCoulomb.HubbardGlobal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_SuperexchangeSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact spectral identification of the global Hubbard inverse term. -/

noncomputable section
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock
open scoped BigOperators InnerProductSpace
variable {Edge : Type*} [Fintype Edge]

def graphHeisenbergFock (m : ℕ) (left right : Edge → Fin (m + 1)) (J : Edge → ℂ) :
    Module.End ℂ (Space (2 * m + 1)) :=
  ∑ e, J e • (siteHeisenberg (siteMode m (left e) 0) (siteMode m (left e) 1)
    (siteMode m (right e) 0) (siteMode m (right e) 1) - 1)

def graphSourceAction (m : ℕ) (left right : Edge → Fin (m + 1)) (J : Edge → ℂ)
    (u : SourceSpinVector (m + 1)) : SourceSpinVector (m + 1) :=
  fun s => ∑ e, J e * (sourceHeisenbergAction (left e) (right e) u s - u s)

def graphSourceForm (m : ℕ) (left right : Edge → Fin (m + 1)) (J : Edge → ℝ)
    (u : SourceSpinVector (m + 1)) : ℝ :=
  ∑ e, J e * (sourceHeisenbergForm (left e) (right e) u - sourceSpinMass u)

def actualChargeInverse (m : ℕ) (U : ℝ) (V : Fin (m + 1) → Fin (m + 1) → ℝ) :
    ActualHubbardHighSpace m →L[ℝ] ActualHubbardHighSpace m :=
  diagonalPenalty (fun A => (chargePenalty U V (occupationAt m A.val.val))⁻¹)

def graphSourceBottom (m : ℕ) (left right : Edge → Fin (m + 1)) (J : Edge → ℝ) : ℝ :=
  sInf {e | ∃ u : SourceSpinVector (m + 1),
    sourceSpinMass u = 1 ∧ e = graphSourceForm m left right J u}

end ContinuumCoulomb.HubbardGlobal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_HubbardFermionSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete half-filled Fock variational problem has the concrete block form. -/

noncomputable section
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock
open scoped BigOperators InnerProductSpace

def assembleFock (m : ℕ) (p : ActualHubbardLowSpace m) (q : ActualHubbardHighSpace m) :
    Laughlin.Fock.Space (2 * m + 1) :=
  (fockCoordinates (2 * m + 1)).symm (lowFockInclusion m p + highFockInclusion m q)

@[simp] theorem fockCoordinates_assemble (m : ℕ) (p : ActualHubbardLowSpace m)
    (q : ActualHubbardHighSpace m) :
    fockCoordinates (2 * m + 1) (assembleFock m p q) =
      lowFockInclusion m p + highFockInclusion m q :=
  (fockCoordinates (2 * m + 1)).apply_symm_apply _

def chargePenaltyFock (m : ℕ) (U : ℝ) (V : Fin (m + 1) → Fin (m + 1) → ℝ) :
    Module.End ℂ (Laughlin.Fock.Space (2 * m + 1)) :=
  occupationDiagonal m (fun o => (chargePenalty U V o : ℂ))

def actualChargePenalty (m : ℕ) (U : ℝ) (V : Fin (m + 1) → Fin (m + 1) → ℝ) :
    ActualHubbardHighSpace m →L[ℝ] ActualHubbardHighSpace m :=
  diagonalPenalty (fun A => chargePenalty U V (occupationAt m A.val.val))

variable {Edge : Type*} [Fintype Edge]

def hubbardFermionForm (m : ℕ) (U : ℝ) (V : Fin (m + 1) → Fin (m + 1) → ℝ)
    (left right : Edge → Fin (m + 1)) (t : Edge → ℝ)
    (x : Laughlin.Fock.Space (2 * m + 1)) : ℝ :=
  ⟪fockCoordinates (2 * m + 1) x,
    fockCoordinates (2 * m + 1)
      ((chargePenaltyFock m U V + graphHopping m left right (fun e => (t e : ℂ))) x)⟫_ℝ

/-- The actual fermionic spectral bottom on all nonzero half-filled
states, in the canonical occupation norm. -/
def hubbardFermionBottom (m : ℕ) (U : ℝ) (V : Fin (m + 1) → Fin (m + 1) → ℝ)
    (left right : Edge → Fin (m + 1)) (t : Edge → ℝ) : ℝ :=
  sInf {e | ∃ x : Laughlin.Fock.Space (2 * m + 1), IsHalfFilled m x ∧ 0 < fockMass x ∧
    e = hubbardFermionForm m U V left right t x / fockMass x}

end ContinuumCoulomb.HubbardGlobal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_MediatorEffective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact effective matrices for simultaneous singlet mediators, on the
complete original-spin Hilbert space. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker

abbrev MediatedSpinBasis (n r : ℕ) := SourceSpinBasis n × MediatorBasis r

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_SpinMatrixNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dimension-independent operator bounds for the actual spin matrices. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker InnerProductSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The ordinary Euclidean operator represented by a finite spin matrix. -/
def spinMatrixOperator (M : Matrix ι ι ℂ) : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι :=
  LinearMap.toContinuousLinearMap M.toEuclideanLin

@[simp] theorem spinMatrixOperator_apply (M : Matrix ι ι ℂ) (x : EuclideanSpace ℂ ι) (i : ι) :
    spinMatrixOperator M x i = ∑ j, M i j * x j := rfl

@[simp] theorem spinMatrixOperator_add (M N : Matrix ι ι ℂ) :
    spinMatrixOperator (M + N) = spinMatrixOperator M + spinMatrixOperator N := by
  unfold spinMatrixOperator
  rw [map_add, map_add]

@[simp] theorem spinMatrixOperator_smul (c : ℂ) (M : Matrix ι ι ℂ) :
    spinMatrixOperator (c • M) = c • spinMatrixOperator M := by
  unfold spinMatrixOperator
  rw [map_smul, map_smul]

@[simp] theorem spinMatrixOperator_mul (M N : Matrix ι ι ℂ) :
    spinMatrixOperator (M * N) = (spinMatrixOperator M).comp (spinMatrixOperator N) := by
  ext x i
  change Matrix.toLpLin 2 2 (M * N) x i =
    Matrix.toLpLin 2 2 M (Matrix.toLpLin 2 2 N x) i
  rw [Matrix.toLpLin_mul_same, LinearMap.comp_apply]

@[simp] theorem spinMatrixOperator_one : spinMatrixOperator (1 : Matrix ι ι ℂ) = 1 := by
  ext x i
  simp [Matrix.one_apply]

@[simp] theorem spinMatrixOperator_star (M : Matrix ι ι ℂ) :
    spinMatrixOperator M.conjTranspose = (spinMatrixOperator M).adjoint := by
  unfold spinMatrixOperator
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_toContinuousLinearMap]

def sourceGraphMatrix (n r : ℕ) (left right : Fin r → Fin n) (J : Fin r → ℝ) :
    Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ :=
  ∑ e, (J e : ℂ) • sourceHeisenbergMatrix n (left e) (right e)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_MediatorBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete low and high blocks for simultaneous singlet mediators.
The nonzero original-spin block is retained throughout. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker InnerProductSpace

abbrev MediatorLowSpace (n : ℕ) := EuclideanSpace ℂ (SourceSpinBasis n)
abbrev MediatorHighSpace (n r : ℕ) := EuclideanSpace ℂ (SourceSpinBasis n × MediatorHighBasis r)
abbrev MediatorFullSpace (n r : ℕ) := EuclideanSpace ℂ (MediatedSpinBasis n r)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_MediatorSector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The singlet and excited mediator coordinates form the full spin space. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker InnerProductSpace

@[simp] theorem spinMatrixOperator_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ℂ) (x : EuclideanSpace ℂ ι) (i : ι) :
    spinMatrixOperator (Matrix.diagonal d) x i = d i * x i := by
  simp [spinMatrixOperator_apply, Matrix.diagonal_apply]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_MediatorForms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full simultaneous-mediator quadratic forms and their exact effective matrix. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker InnerProductSpace

@[simp] theorem spinMatrixOperator_zero {ι : Type*} [Fintype ι] [DecidableEq ι] :
    spinMatrixOperator (0 : Matrix ι ι ℂ) = 0 := by
  unfold spinMatrixOperator
  rw [map_zero, map_zero]

@[simp] theorem spinMatrixOperator_sub {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M N : Matrix ι ι ℂ) : spinMatrixOperator (M - N) = spinMatrixOperator M - spinMatrixOperator N := by
  unfold spinMatrixOperator
  rw [map_sub, map_sub]

end ContinuumCoulomb

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

/-- Addition costs at most one more bit than the larger input. -/
theorem bits_add_max (a b : ℕ) :
    (a + b).bits.length ≤ max a.bits.length b.bits.length + 1 := by
  simp only [Nat.size_eq_bits_len]
  rw [Nat.size_le, pow_succ]
  have ha := Nat.lt_size_self a
  have hb := Nat.lt_size_self b
  have hap : 2 ^ a.size ≤ 2 ^ max a.size b.size := by
    apply Nat.pow_le_pow_right (by decide)
    exact le_max_left a.size b.size
  have hbp : 2 ^ b.size ≤ 2 ^ max a.size b.size := by
    apply Nat.pow_le_pow_right (by decide)
    exact le_max_right a.size b.size
  omega

theorem bits_succ (a : ℕ) : (a + 1).bits.length ≤ a.bits.length + 1 := by
  simp only [Nat.size_eq_bits_len]
  rw [Nat.size_le, pow_succ]
  have ha := Nat.lt_size_self a
  have hp : 0 < 2 ^ a.size := by positivity
  omega

theorem encodeUnary_replicate (D : ℕ) :
    BinaryEncoding.encodeUnary D = List.replicate D true ++ [false] := by
  induction D with
  | zero => rfl
  | succ D ih => simp only [BinaryEncoding.encodeUnary, List.replicate_succ, List.cons_append, ih]

end ContinuumCoulomb.AmplificationProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_EncodingPrograms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite-stack parsing and serialization routines for the coordinate codes. Sign bits, natural-number marker bits, and field tails
are read by the program rather than by an assumed record-decoding operation. -/

namespace ContinuumCoulomb.EncodingPrograms
open ExactQuantumFactoring.BitStackProgram

def integerPayload : ℤ → ℕ
  | .ofNat n => n
  | .negSucc n => n

def integerNegative : ℤ → Bool
  | .ofNat _ => false
  | .negSucc _ => true

def emptyUnit : BinaryEncoding.Codec Unit where
  encode _ := []
  read s := ((), s)
  read_encode x tail := by cases x; rfl

end ContinuumCoulomb.EncodingPrograms

end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_BitStackListOps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {α β : Type}

lemma fold_cons_append (xs ys : List α) : xs.foldl (fun ys a=>a::ys) ys=xs.reverse++ys := by
  induction xs generalizing ys with
  | nil=>rfl
  | cons a as ih=>simp only [List.foldl_cons,ih,List.reverse_cons,List.append_assoc,List.singleton_append]

lemma fold_map_cons_append (f : α→β) (xs : List α) (ys : List β) :
    xs.foldl (fun ys a=>f a::ys) ys=(xs.map f).reverse++ys := by
  induction xs generalizing ys with
  | nil=>rfl
  | cons a as ih=>simp only [List.foldl_cons,ih,List.map_cons,List.reverse_cons,
      List.append_assoc,List.singleton_append]

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
def tabStep (f : α→ℕ→β) (s : ℕ×(α×List β)) : ℕ×(α×List β) :=
  (s.1+1,s.2.1,f s.2.1 s.1::s.2.2)
lemma tabStep_iterate (f : α→ℕ→β) (j i : ℕ) (a : α) (ys : List β) :
    (tabStep f)^[j] (i,a,ys)=(i+j,a,((List.range' i j).map (f a)).reverse++ys) := by
  induction j with
  | zero=>simp
  | succ j ih=>
    rw [Function.iterate_succ_apply',ih]
    simp only [tabStep,List.range'_1_concat,List.map_append,List.map_cons,List.map_nil,
      List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,List.cons_append]
    simp only [Nat.add_assoc]
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
def dropStep : ℕ×List α→ℕ×List α
  | (n,xs)=>if n=0 then (n,xs) else (n-1,xs.tail)
lemma dropStep_iterate (i n : ℕ) (xs : List α) :
    dropStep^[i] (n,xs)=(n-i,xs.drop (min i n)) := by
  induction i generalizing n xs with
  | zero=>simp
  | succ i ih=>
    rw [Function.iterate_succ_apply]
    by_cases hn : n=0
    · subst n;simp [dropStep,ih]
    · obtain ⟨n,rfl⟩:=Nat.exists_eq_succ_of_ne_zero hn
      simp only [dropStep,Nat.succ_ne_zero,ite_false, if_false,Nat.succ_sub_one,ih]
      rw [←List.drop_one,List.drop_drop]
      congr 1
      · omega
      · congr 1; omega

end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_NativeAIGBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open BitStackProgram

lemma nat_bits_length_bound (n : ℕ) : n.bits.length≤n := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr Nat.lt_two_pow_self
end ExactQuantumFactoring.NativeAIG

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
lemma map_range_getD (xs : List β) (d : β) (f : β→γ) :
    (List.range xs.length).map (fun i=>f ((xs.drop i).headD d))=xs.map f := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map,List.getElem_range]
    have hi : i<xs.length:=by simpa using h1
    rw [List.headD_eq_head?_getD,List.head?_drop,List.getElem?_eq_getElem hi,Option.getD_some]
end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_BitStackPowers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
lemma bits_length_pow (a k : ℕ) : (a^k).bits.length≤k*a.bits.length+1:=by
  induction k with
  | zero=>simp
  | succ k ih=>
    have h:=bits_length_mul (a^k) a
    rw [pow_succ];nlinarith

def powerStep (s : ℕ×ℕ) : ℕ×ℕ:=(s.1,s.2*s.1)
lemma powerStep_iterate (s : ℕ×ℕ) (i : ℕ) : (powerStep^[i]) s=(s.1,s.2*s.1^i):=by
  induction i with
  | zero=>simp
  | succ i ih=>rw [Function.iterate_succ_apply',ih];simp [powerStep,pow_succ,Nat.mul_assoc]
end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_SquareRootProgram
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

abbrev State := ℕ × (ℕ × ℕ)

def step (s : State) : State :=
  let half := s.2.1 / 2
  let candidate := s.2.2 + half
  (s.1, half, if candidate * candidate ≤ s.1 then candidate else s.2.2)

def measure (s : State) : ℕ := s.1.bits.length + s.2.1.bits.length + s.2.2.bits.length

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

abbrev Input := ℕ × (ℕ × ℕ)

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

def scale (r W G : ℕ) : ℕ := 1048576 * (r + 1) ^ 3 * W ^ 3 * G
def delta (r W G : ℕ) : ℕ := scale r W G ^ 2
def precision (r G : ℕ) : ℕ := r + G + 20

noncomputable def epsilon (r W G : ℕ) : ℝ := 4 * (r + 1) * W / scale r W G

def radicand (r W G : ℕ) (J : ℚ) : ℚ := 2 * (delta r W G : ℚ) * |J|

end ContinuumCoulomb.MediatorParameters

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_MediatorGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit ordinary-spin coordinates for a simultaneous mediator stage.
The new sites are the two actual members of every fresh pair. -/

noncomputable section
namespace ContinuumCoulomb.MediatorGraph
open Matrix
open scoped BigOperators Kronecker InnerProductSpace

def vertexEquiv (n r : ℕ) : Fin n ⊕ (Fin r × Fin 2) ≃ Fin (n + r * 2) :=
  (Equiv.sumCongr (Equiv.refl _) finProdFinEquiv).trans finSumFinEquiv

def old (n r : ℕ) (i : Fin n) : Fin (n + r * 2) := vertexEquiv n r (Sum.inl i)

def fresh (n r : ℕ) (e : Fin r) (member : Fin 2) : Fin (n + r * 2) :=
  vertexEquiv n r (Sum.inr (e, member))

def pairEquiv : (Fin 2 → Fin 2) ≃ Fin 4 :=
  (finTwoArrowEquiv (Fin 2)).trans finProdFinEquiv

def basisEquiv (n r : ℕ) : MediatedSpinBasis n r ≃ SourceSpinBasis (n + r * 2) where
  toFun p k := Sum.elim p.1 (fun a => pairEquiv.symm (p.2 a.1) a.2)
    ((vertexEquiv n r).symm k)
  invFun s := (fun i => s (old n r i),
    fun e => pairEquiv (fun member => s (fresh n r e member)))
  left_inv p := by
    apply Prod.ext
    · funext i
      simp [old]
    · funext e
      simp [fresh]
  right_inv s := by
    funext k
    obtain ⟨i, rfl⟩ := (vertexEquiv n r).surjective k
    cases i with
    | inl i => simp [old]
    | inr a => simp [fresh]

@[simp] theorem basisEquiv_old (n r : ℕ) (p : MediatedSpinBasis n r) (i : Fin n) :
    basisEquiv n r p (old n r i) = p.1 i := by
  simp [basisEquiv, old]

@[simp] theorem basisEquiv_fresh (n r : ℕ) (p : MediatedSpinBasis n r)
    (e : Fin r) (member : Fin 2) :
    basisEquiv n r p (fresh n r e member) = pairEquiv.symm (p.2 e) member := by
  simp [basisEquiv, fresh]

theorem old_ne_fresh (n r : ℕ) (i : Fin n) (e : Fin r) (member : Fin 2) :
    old n r i ≠ fresh n r e member := by
  intro h
  have := (vertexEquiv n r).injective h
  cases this

theorem fresh_injective (n r : ℕ) : Function.Injective (fun a : Fin r × Fin 2 =>
    fresh n r a.1 a.2) := by
  intro a b h
  exact Sum.inr.inj ((vertexEquiv n r).injective h)

theorem old_injective (n r : ℕ) : Function.Injective (old n r) := by
  intro a b h
  exact Sum.inl.inj ((vertexEquiv n r).injective h)

def joinedMatrices (n r : ℕ) (A : Fin n → Matrix (Fin 2) (Fin 2) ℂ)
    (B : Fin r → Fin 2 → Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin (n + r * 2)) : Matrix (Fin 2) (Fin 2) ℂ :=
  Sum.elim A (fun a => B a.1 a.2) ((vertexEquiv n r).symm k)

section Reindex
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def normalizedBottom (H : Matrix ι ι ℂ) : ℝ :=
  sInf {e | ∃ x : EuclideanSpace ℂ ι, ‖x‖ = 1 ∧ e = ⟪x, spinMatrixOperator H x⟫_ℝ}

end Reindex

abbrev EdgeIndex (q r : ℕ) := Fin q ⊕ (Fin r ⊕ (Fin r × Fin 2))

def edgeEquiv (q r : ℕ) : EdgeIndex q r ≃ Fin (q + (r + r * 2)) :=
  (Equiv.sumCongr (Equiv.refl _)
    ((Equiv.sumCongr (Equiv.refl _) finProdFinEquiv).trans finSumFinEquiv)).trans finSumFinEquiv

def stageLeft (n q r : ℕ) (keepLeft : Fin q → Fin n) (left right : Fin r → Fin n)
    (a : Fin (q + (r + r * 2))) : Fin (n + r * 2) :=
  match (edgeEquiv q r).symm a with
  | .inl e => old n r (keepLeft e)
  | .inr (.inl e) => fresh n r e 0
  | .inr (.inr (e, side)) => old n r (if side = 0 then left e else right e)

def stageRight (n q r : ℕ) (keepRight : Fin q → Fin n) (member : Fin r → Fin 2)
    (a : Fin (q + (r + r * 2))) : Fin (n + r * 2) :=
  match (edgeEquiv q r).symm a with
  | .inl e => old n r (keepRight e)
  | .inr (.inl e) => fresh n r e 1
  | .inr (.inr (e, side)) => fresh n r e (if side = 0 then 0 else member e)

def stageWeight (q r : ℕ) (keepWeight : Fin q → ℚ) (Delta : ℚ) (amplitude : Fin r → ℚ)
    (a : Fin (q + (r + r * 2))) : ℚ :=
  match (edgeEquiv q r).symm a with
  | .inl e => keepWeight e
  | .inr (.inl _) => Delta
  | .inr (.inr (e, _)) => amplitude e

def stageMatrix (n q r : ℕ) (keepLeft keepRight : Fin q → Fin n) (keepWeight : Fin q → ℚ)
    (left right : Fin r → Fin n) (member : Fin r → Fin 2) (Delta : ℚ)
    (amplitude : Fin r → ℚ) :
    Matrix (SourceSpinBasis (n + r * 2)) (SourceSpinBasis (n + r * 2)) ℂ :=
  sourceGraphMatrix (n + r * 2) (q + (r + r * 2))
    (stageLeft n q r keepLeft left right) (stageRight n q r keepRight member)
    (fun a => (stageWeight q r keepWeight Delta amplitude a : ℝ))

end ContinuumCoulomb.MediatorGraph

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_MediatorScaleBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete weight and inverse-weight bounds for the three mediator
stages. Each bound is a fixed polynomial in entering unary parameters. -/

namespace ContinuumCoulomb.MediatorParameters

def secondWeight (r W G : ℕ) : ℕ :=
  2 + 3 * r * delta r W G + 2 * scale r W G * W

def thirdWeight (r W G : ℕ) : ℕ :=
  2 + 3 * r * delta r W G + delta (2 * r) (secondWeight r W G) G +
    2 * scale (2 * r) (secondWeight r W G) G * secondWeight r W G

def finalWeight (r W G : ℕ) : ℕ :=
  2 + delta r W G + delta (6 * r) (thirdWeight r W G) G +
    2 * scale (6 * r) (thirdWeight r W G) G * thirdWeight r W G

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

structure Bonds (n r : ℕ) where
  left : Fin r → Fin n
  right : Fin r → Fin n
  weight : Fin r → ℚ

def Bonds.NoLoops {n r : ℕ} (F : Bonds n r) : Prop := ∀ e, F.left e ≠ F.right e

noncomputable def Bonds.matrix {n r : ℕ} (F : Bonds n r) :
    Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ :=
  sourceGraphMatrix n r F.left F.right (fun e => (F.weight e : ℝ))

def empty (n : ℕ) : Bonds n 0 where
  left := Fin.elim0
  right := Fin.elim0
  weight := Fin.elim0

def lift {n q : ℕ} (r : ℕ) (F : Bonds n q) : Bonds (n + r * 2) q where
  left e := old n r (F.left e)
  right e := old n r (F.right e)
  weight := F.weight

def central (n r : ℕ) (Delta : ℚ) : Bonds (n + r * 2) r where
  left e := fresh n r e 0
  right e := fresh n r e 1
  weight _ := Delta

def spokes {n r : ℕ} (F : Bonds n r) (member : Fin r → Fin 2)
    (amplitude : Fin r → ℚ) : Bonds (n + r * 2) (r * 2) where
  left a := old n r (if (finProdFinEquiv.symm a).2 = 0 then
    F.left (finProdFinEquiv.symm a).1 else F.right (finProdFinEquiv.symm a).1)
  right a := fresh n r (finProdFinEquiv.symm a).1
    (if (finProdFinEquiv.symm a).2 = 0 then 0 else member (finProdFinEquiv.symm a).1)
  weight a := amplitude (finProdFinEquiv.symm a).1

def join {n q r : ℕ} (F : Bonds n q) (K : Bonds n r) : Bonds n (q + r) where
  left a := Sum.elim F.left K.left (finSumFinEquiv.symm a)
  right a := Sum.elim F.right K.right (finSumFinEquiv.symm a)
  weight a := Sum.elim F.weight K.weight (finSumFinEquiv.symm a)

def secondBound (r W G : ℕ) : ℕ := MediatorParameters.secondWeight r W G
def thirdBound (r W G : ℕ) : ℕ := MediatorParameters.thirdWeight r W G

def member (J : ℚ) : Fin 2 := if J < 0 then 0 else 1

def deltaOne (r W G : ℕ) : ℕ := MediatorParameters.delta r W G
def deltaTwo (r W G : ℕ) : ℕ := MediatorParameters.delta (r * 2) (secondBound r W G) G
def deltaThree (r W G : ℕ) : ℕ :=
  MediatorParameters.delta (r * 2 + r * 2 * 2) (thirdBound r W G) G

def firstCentral {n r : ℕ} (_F : Bonds n r) (W G : ℕ) : Bonds (n + r * 2) r :=
  central n r (deltaOne r W G)

def secondCentral {n r : ℕ} (_F : Bonds n r) (W G : ℕ) :
    Bonds (n + r * 2 + r * 2 * 2) (r * 2) := central _ _ (deltaTwo r W G)

def retainedCentral {n r : ℕ} (F : Bonds n r) (W G : ℕ) :
    Bonds (n + r * 2 + r * 2 * 2) r := lift (r * 2) (firstCentral F W G)

def thirdCentral {n r : ℕ} (_F : Bonds n r) (W G : ℕ) :
    Bonds (n + r * 2 + r * 2 * 2 + (r * 2 + r * 2 * 2) * 2) (r * 2 + r * 2 * 2) :=
  central _ _ (deltaThree r W G)

end ContinuumCoulomb.MediatorIteration

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identification of the encoded source's original swap-form variational
energy with the complete finite matrix used by all mediator stages. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators InnerProductSpace

def SquareLatticeHeisenberg.bonds (d : SquareLatticeHeisenberg) :
    MediatorIteration.Bonds d.vertices d.edges where
  left := d.left
  right := d.right
  weight := d.coefficient

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_MediatorProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual polynomial-time arithmetic for the explicitly scaled rational
mediator stage. Edge count, weight bound and inverse-error bound are unary;
the entering coefficient and emitted spoke are canonical binary rationals. -/

namespace ContinuumCoulomb.MediatorProgram
open ExactQuantumFactoring.BitStackProgram

abbrev Input := ℕ × (ℕ × (ℕ × ℚ))

end ContinuumCoulomb.MediatorProgram

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

def prefixCode {α : Type} (c : BinaryEncoding.Codec α) (x : α × List Bool) : List Bool :=
  c.encode x.1 ++ x.2

end ContinuumCoulomb.PrefixPrograms

end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_BitStackListWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
lemma fold_append_words (xs : List (List Bool)) (ys : List Bool) :
    xs.foldl (fun ys x=>ys++x) ys=ys++xs.flatten := by
  induction xs generalizing ys with
  | nil=>simp
  | cons x xs ih=>simp [ih,List.append_assoc]
end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_PrefixListPrograms
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

abbrev State (α : Type) := List α × (List Bool × List α)

def stateView {α : Type} (c : BinaryEncoding.Codec α) (s : State α) :
    ℕ × (List Bool × List α) := (s.1.length, (s.1.flatMap c.encode ++ s.2.1, s.2.2))

def step {α : Type} (s : State α) : State α :=
  match s.1 with
  | [] => s
  | a :: xs => (xs, s.2.1, a :: s.2.2)

theorem step_iterate {α : Type} (i : ℕ) (xs : List α) (tail : List Bool) (acc : List α) :
    step^[i] (xs, tail, acc) = (xs.drop i, tail, (xs.take i).reverse ++ acc) := by
  induction i generalizing xs acc with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply]
    cases xs with
    | nil => simpa [step] using ih [] acc
    | cons a xs => simpa [step, List.reverse_cons, List.append_assoc] using ih xs (a :: acc)

theorem flat_length {α : Type} (c : BinaryEncoding.Codec α) (hc : ∀ a, 0 < (c.encode a).length)
    (xs : List α) : xs.length ≤ (xs.flatMap c.encode).length := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have ha := hc a
    simp only [List.length_cons, List.flatMap_cons, List.length_append]
    omega

section Parser
variable {α : Type}
  (c : BinaryEncoding.Codec α)
  (d : α)

abbrev NonemptyState (α : Type) := {s : State α // ¬s.1 = []}

theorem input_length (hc : ∀ a, 0 < (c.encode a).length) (x : List α × List Bool) :
    x.1.length ≤ (prefixCode (BinaryEncoding.list c) x).length := by
  have h := flat_length c hc x.1
  change x.1.length ≤ ((BinaryEncoding.natural.encode x.1.length ++ x.1.flatMap c.encode) ++ x.2).length
  simp only [List.length_append]
  omega

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

theorem integer_length_pos (z : ℤ) : 0 < (BinaryEncoding.integer.encode z).length := by
  cases z <;> simp only [BinaryEncoding.integer, List.length_cons] <;> omega

theorem coordinate_length_pos (p : ℤ × ℤ) :
    0 < ((BinaryEncoding.pair BinaryEncoding.integer BinaryEncoding.integer).encode p).length := by
  have h := integer_length_pos p.1
  simp only [BinaryEncoding.pair_length]
  omega

theorem edge_length_pos (e : BinaryHeisenbergEdge) :
    0 < (binaryHeisenbergEdgeCodec.encode e).length := by
  have h := BinaryEncoding.natural_length e.left
  change 0 < ((BinaryEncoding.natural.encode e.left ++
    (BinaryEncoding.natural.encode e.right ++ binaryRationalCodec.encode e.coefficient))).length
  simp only [List.length_append]
  omega

abbrev Coordinate := ℤ × ℤ

def coordinateCodec := BinaryEncoding.pair BinaryEncoding.integer BinaryEncoding.integer

def coordinateListCodec := BinaryEncoding.list coordinateCodec

def edgeListCodec := BinaryEncoding.list binaryHeisenbergEdgeCodec

def thresholdCodec := BinaryEncoding.pair binaryRationalCodec binaryRationalCodec

def sourceTailCodec := BinaryEncoding.pair edgeListCodec thresholdCodec

end ContinuumCoulomb.SourcePrograms

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

abbrev Bond := ℕ × (ℕ × ℚ)

def zeroBond : Bond := (0, 0, 0)

abbrev Env := ℕ × (ℕ × (ℕ × ℕ))

abbrev IndexedBond := Env × (ℕ × Bond)

abbrev Input := Env × List Bond

abbrev LoopInput := ℕ × Input

def central (x : Input) : List Bond := (List.range x.2.length).map (fun i =>
  (x.1.2.2.2 + 2 * i, x.1.2.2.2 + 2 * i + 1,
    (MediatorParameters.delta x.1.1 x.1.2.1 x.1.2.2.1 : ℚ)))

end ContinuumCoulomb.MediatorListProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceCoefficientRounding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact common-denominator source coefficient rounding, implemented by
actual integer/rational machine arithmetic. Nonzero rounded weights have
an inverse-polynomial lower bound without assuming one for the source. -/

namespace ContinuumCoulomb.SourceCoefficientRounding
open ExactQuantumFactoring.BitStackProgram MediatorListProgram

def coefficient (M : ℕ) (q : ℚ) : ℚ := (round ((M : ℚ) * q) : ℚ) / M

abbrev Input := ℕ × Bond

end ContinuumCoulomb.SourceCoefficientRounding

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceZeroFilter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual deletion of zero source bonds after common-denominator rounding. -/

namespace ContinuumCoulomb.SourceZeroFilter
open ExactQuantumFactoring.BitStackProgram MediatorListProgram

def keep (e : Bond) : Bool := decide (e.2.2 ≠ 0)

def step (acc : List Bond) (e : Bond) : List Bond := if keep e then e :: acc else acc

theorem fold_step (xs acc : List Bond) :
    xs.foldl step acc = (xs.filter keep).reverse ++ acc := by
  induction xs generalizing acc with
  | nil => simp
  | cons e xs ih =>
    rw [List.foldl_cons, ih]
    by_cases h : keep e = true
    · simp only [step, h, ite_true, if_true, List.filter_cons_of_pos h, List.reverse_cons, List.append_assoc,
        List.singleton_append]
    · have hn : keep e = false := Bool.eq_false_iff.mpr h
      simp only [step, hn, Bool.false_eq_true, ite_false, if_false, List.filter_cons_of_neg h]

end ContinuumCoulomb.SourceZeroFilter

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceBondLists
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complete matrix semantics for the literal bond registers. Removing zero
terms preserves the actual Hamiltonian, while valid bounded indices give
the exact finite family used in the mediator comparison. -/

noncomputable section
namespace ContinuumCoulomb.SourceBondLists
open Matrix MediatorIteration MediatorListProgram
open scoped BigOperators

def bounded (n : ℕ) (xs : List _root_.OAI.ContinuumCoulomb.MediatorListProgram.Bond) : Prop := ∀ e ∈ xs, e.1 < n ∧ e.2.1 < n

def bonds (n : ℕ) (xs : List _root_.OAI.ContinuumCoulomb.MediatorListProgram.Bond) (h : bounded n xs) : Bonds n xs.length where
  left i := ⟨(xs.get i).1, (h _ (List.get_mem xs i)).1⟩
  right i := ⟨(xs.get i).2.1, (h _ (List.get_mem xs i)).2⟩
  weight i := (xs.get i).2.2

theorem filter_bounded (n : ℕ) (xs : List _root_.OAI.ContinuumCoulomb.MediatorListProgram.Bond) (h : bounded n xs) :
    bounded n (xs.filter SourceZeroFilter.keep) := by
  intro e he
  exact h e (List.mem_filter.mp he).1

end ContinuumCoulomb.SourceBondLists

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceNormalizedSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal source rounding and zero deletion feed the complete three-stage
spin comparison. Only the source's upper coefficient and gap bounds are
needed; a nonzero lower coefficient bound is proved by rounding. -/

noncomputable section
namespace ContinuumCoulomb.SourceNormalizedSpectrum
open Matrix MediatorIteration MediatorListProgram SourceBondLists
open scoped BigOperators

def rounded (d : SquareLatticeHeisenberg) (M : ℕ) : List _root_.OAI.ContinuumCoulomb.MediatorListProgram.Bond :=
  List.ofFn (fun e => ((d.left e).val, (d.right e).val,
    SourceCoefficientRounding.coefficient M (d.coefficient e)))

def retained (d : SquareLatticeHeisenberg) (M : ℕ) : List _root_.OAI.ContinuumCoulomb.MediatorListProgram.Bond :=
  (rounded d M).filter SourceZeroFilter.keep

theorem rounded_bounded (d : SquareLatticeHeisenberg) (M : ℕ) : bounded d.vertices (rounded d M) := by
  intro e he
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
  exact ⟨(d.left i).isLt, (d.right i).isLt⟩

theorem retained_bounded (d : SquareLatticeHeisenberg) (M : ℕ) : bounded d.vertices (retained d M) :=
  filter_bounded d.vertices (rounded d M) (rounded_bounded d M)

def family (d : SquareLatticeHeisenberg) (M : ℕ) : Bonds d.vertices (retained d M).length :=
  bonds d.vertices (retained d M) (retained_bounded d M)

end ContinuumCoulomb.SourceNormalizedSpectrum

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceNormalizedPromise
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed polynomial common denominator absorbs both coefficient rounding
and all three mediator errors into one inverse-polynomial promise budget. -/

noncomputable section
namespace ContinuumCoulomb.SourceNormalizedSpectrum

def denominator (r G : ℕ) : ℕ := 1024 * (r + 1) * G

end ContinuumCoulomb.SourceNormalizedSpectrum

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

def rounded (x : Input) : List Bond := x.2.map (fun e =>
  (e.1, e.2.1, SourceCoefficientRounding.coefficient
    (SourceNormalizedSpectrum.denominator x.2.length x.1.2.2.1) e.2.2))

def retained (x : Input) : List Bond := (rounded x).filter SourceZeroFilter.keep

def normalized (x : Input) : Input :=
  (((retained x).length,
    SourceNormalizedSpectrum.denominator x.2.length x.1.2.2.1 + x.1.2.1 + 1,
    x.1.2.2.1, x.1.2.2.2), retained x)

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

def size (d : BinaryHeisenberg) : ℕ := (binaryHeisenbergCodec.encode d).length + 1

def input (k : ℕ) (d : BinaryHeisenberg) : Input :=
  ((d.edges.length, size d ^ k, size d ^ k, d.coordinate.length),
    d.edges.map (fun e => (e.left, e.right, e.coefficient.value)))

end ContinuumCoulomb.SourceMetadataProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_SingleSpinSource
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal, constant-size decision branch covers the original one-spin
source. This prevents the many-electron construction from excluding it. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators

theorem source_one_vertex_edges (d : SquareLatticeHeisenberg) (hv : d.vertices ≤ 1) : d.edges=0 := by
  apply Nat.eq_zero_of_not_pos
  intro he
  let e : Fin d.edges := ⟨0,he⟩
  have hn := d.edge_ne e
  have hl := (d.left e).isLt
  have hr := (d.right e).isLt
  exact hn (Fin.ext (by omega))

theorem source_one_vertex_energy (d : SquareLatticeHeisenberg) (hv : d.vertices ≤ 1) :
    realSourceGroundEnergy d=0 := by
  have he := source_one_vertex_edges d hv
  let : IsEmpty (Fin d.edges) := by rw [he]; infer_instance
  have hf (w : SourceSpinVector d.vertices) : sourceHamiltonianForm d w=0 := by
    simp [sourceHamiltonianForm]
  apply le_antisymm
  · simpa only [hf] using realSourceGroundEnergy_le_trial d (allUpSourceVector d.vertices)
      (allUpSourceVector_mass d.vertices)
  · exact realSourceGroundEnergy_lower_of_forall d 0 (fun w _ => (hf w).ge)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.MinUncut_Machines_Runtime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.Runtime

def statementPushBound {K : Type} {Γ : K → Type} {Λ σ : Type} :
    Turing.TM2.Stmt Γ Λ σ → Nat
  | .push _ _ next => statementPushBound next + 1
  | .peek _ _ next => statementPushBound next
  | .pop _ _ next => statementPushBound next
  | .load _ next => statementPushBound next
  | .branch _ yes no => max (statementPushBound yes) (statementPushBound no)
  | .goto _ => 0
  | .halt => 0

def maxLabelPushes {K : Type} {Γ : K → Type} {Λ σ : Type}
    (program : Λ → Turing.TM2.Stmt Γ Λ σ) : List Λ → Nat
  | [] => 0
  | label :: rest => max (statementPushBound (program label)) (maxLabelPushes program rest)

theorem maxLabelPushes_ge {K : Type} {Γ : K → Type} {Λ σ : Type}
    (program : Λ → Turing.TM2.Stmt Γ Λ σ) (labels : List Λ) (label : Λ)
    (member : label ∈ labels) :
    statementPushBound (program label) ≤ maxLabelPushes program labels := by
  induction labels with
  | nil => simp at member
  | cons first rest ih =>
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih member) (Nat.le_max_right _ _)

noncomputable def programPushBound (tm : Turing.FinTM2) : Nat :=
  maxLabelPushes tm.m tm.ΛFin.elems.toList

theorem statement_le_programPushBound (tm : Turing.FinTM2) (label : tm.Λ) :
    statementPushBound (tm.m label) ≤ programPushBound tm := by
  apply maxLabelPushes_ge
  simpa using tm.ΛFin.complete label

theorem stepAuxStackLength {K : Type} {Γ : K → Type} {Λ σ : Type} [DecidableEq K]
    (stmt : Turing.TM2.Stmt Γ Λ σ) (state : σ) (tapes : ∀ k, List (Γ k)) (k : K) :
    ((Turing.TM2.stepAux stmt state tapes).stk k).length ≤
      (tapes k).length + statementPushBound stmt := by
  induction stmt generalizing state tapes with
  | push j f next ih =>
      have changed : ((Function.update tapes j (f state :: tapes j)) k).length ≤
          (tapes k).length + 1 := by
        by_cases same : k = j
        · subst k; simp
        · simp [Function.update, same]
      have h := ih state (Function.update tapes j (f state :: tapes j))
      simp only [Turing.TM2.stepAux, statementPushBound]
      omega
  | peek j f next ih =>
      simpa only [Turing.TM2.stepAux, statementPushBound] using
        ih (f state (tapes j).head?) tapes
  | pop j f next ih =>
      have changed : ((Function.update tapes j (tapes j).tail) k).length ≤
          (tapes k).length := by
        by_cases same : k = j
        · subst k; simp
        · simp [Function.update, same]
      have h := ih (f state (tapes j).head?) (Function.update tapes j (tapes j).tail)
      simp only [Turing.TM2.stepAux, statementPushBound]
      omega
  | load f next ih =>
      simpa only [Turing.TM2.stepAux, statementPushBound] using ih (f state) tapes
  | branch condition yes no ihYes ihNo =>
      cases decision : condition state with
      | false =>
          have h := ihNo state tapes
          have hm := Nat.le_max_right (statementPushBound yes) (statementPushBound no)
          simp only [Turing.TM2.stepAux, statementPushBound, decision, Bool.cond_false]
          omega
      | true =>
          have h := ihYes state tapes
          have hm := Nat.le_max_left (statementPushBound yes) (statementPushBound no)
          simp only [Turing.TM2.stepAux, statementPushBound, decision, Bool.cond_true]
          omega
  | goto f => simp [Turing.TM2.stepAux, statementPushBound]
  | halt => simp [Turing.TM2.stepAux, statementPushBound]

theorem iterateSizeBound {α : Type} (f : α → α) (size : α → Nat) (C : Nat)
    (oneStep : ∀ x, size (f x) ≤ size x + C) (n : Nat) (x : α) :
    size ((f^[n]) x) ≤ size x + n * C := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hs := oneStep ((f^[n]) x)
      have bound : size (f ((f^[n]) x)) ≤ size x + (n + 1) * C := by
        rw [Nat.add_mul, Nat.one_mul]
        omega
      simpa only [Function.iterate_succ_apply'] using bound

theorem executionSizeBound {σ : Type} (step : σ → Option σ) (size : σ → Nat) (C : Nat)
    (oneStep : ∀ a b, step a = some b → size b ≤ size a + C)
    {start finish : σ} {budget : Nat}
    (execution : StateTransition.EvalsToInTime step start (some finish) budget) :
    size finish ≤ size start + budget * C := by
  let liftedSize : Option σ → Nat := fun state => (state.map size).getD 0
  have liftedStep : ∀ state : Option σ,
      liftedSize (state.bind step) ≤ liftedSize state + C := by
    intro state
    cases state with
    | none => simp [liftedSize]
    | some a =>
        cases transition : step a with
        | none => simp [liftedSize, transition]
        | some b => simpa [liftedSize, transition] using oneStep a b transition
  have bound := iterateSizeBound (fun state : Option σ => state.bind step)
    liftedSize C liftedStep execution.steps (some start)
  change liftedSize ((flip bind step)^[execution.steps] (some start)) ≤ _ at bound
  rw [execution.evals_in_steps] at bound
  simp only [liftedSize, Option.map_some, Option.getD_some] at bound
  exact Nat.le_trans bound (Nat.add_le_add_left
    (Nat.mul_le_mul_right C execution.steps_le_m) _)

theorem stepStackLength (tm : Turing.FinTM2) (k : tm.K) (a b : tm.Cfg)
    (transition : tm.step a = some b) :
    (b.stk k).length ≤ (a.stk k).length + programPushBound tm := by
  cases a with
  | mk label state tapes =>
      cases label with
      | none => simp [Turing.FinTM2.step, Turing.TM2.step] at transition
      | some label =>
          have result := Option.some.inj transition
          rw [← result]
          exact Nat.le_trans (stepAuxStackLength _ _ _ _)
            (Nat.add_le_add_left (statement_le_programPushBound tm label) _)

theorem initialStackLength (tm : Turing.FinTM2) (input : List (tm.Γ tm.k₀)) (k : tm.K) :
    ((Turing.initList tm input).stk k).length ≤ input.length := by
  simp only [Turing.initList]
  split
  next same => subst k; exact Nat.le_refl _
  next _ => simp

@[simp] theorem haltedOutputLength (tm : Turing.FinTM2) (output : List (tm.Γ tm.k₁)) :
    ((Turing.haltList tm output).stk tm.k₁).length = output.length := by
  simp [Turing.haltList]

theorem outputLength_le (tm : Turing.FinTM2) (input : List (tm.Γ tm.k₀))
    (output : List (tm.Γ tm.k₁)) (budget : Nat)
    (execution : Turing.TM2OutputsInTime tm input (some output) budget) :
    output.length ≤ input.length + budget * programPushBound tm := by
  have bound := executionSizeBound tm.step (fun cfg => (cfg.stk tm.k₁).length)
    (programPushBound tm) (stepStackLength tm tm.k₁) execution
  calc
    output.length = ((Turing.haltList tm output).stk tm.k₁).length := (haltedOutputLength tm output).symm
    _ ≤ ((Turing.initList tm input).stk tm.k₁).length + budget * programPushBound tm := bound
    _ ≤ input.length + budget * programPushBound tm :=
      Nat.add_le_add_right (initialStackLength tm input tm.k₁) _

theorem encodedOutputLength {α β αΓ βΓ : Type}
    {ea : α → List αΓ} {eb : β → List βΓ} {f : α → β}
    (certificate : Turing.TM2ComputableInPolyTime ea eb f) (a : α) :
    (eb (f a)).length ≤
      (Polynomial.X + Polynomial.C (programPushBound certificate.tm) * certificate.time).eval
        (ea a).length := by
  have bound := outputLength_le certificate.tm _ _ _ (certificate.outputsFun a)
  simpa only [List.length_map, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_mul, Polynomial.eval_C, Nat.mul_comm] using bound

end MinUncutGames.Foundations.Complexity.Runtime

namespace MinUncutGames.Foundations.Complexity.MachineEmbedding

open Turing.TM2

variable {K E Λ Λextra σ τ : Type} {Γ : K → Type} {Δ : E → Type}

abbrev Alphabet (Γ : K → Type) (Δ : E → Type) : K ⊕ E → Type
  | .inl k => Γ k
  | .inr e => Δ e

def tapes (source : ∀ k, List (Γ k)) (extra : ∀ e, List (Δ e)) :
    ∀ j, List (Alphabet Γ Δ j)
  | .inl k => source k
  | .inr e => extra e

@[simp] theorem tapes_inl (source : ∀ k, List (Γ k)) (extra : ∀ e, List (Δ e))
    (k : K) : tapes source extra (.inl k) = source k := rfl

@[simp] theorem tapes_inr (source : ∀ k, List (Γ k)) (extra : ∀ e, List (Δ e))
    (e : E) : tapes source extra (.inr e) = extra e := rfl

def label (haltTarget : Option (Λ ⊕ Λextra)) : Option Λ → Option (Λ ⊕ Λextra)
  | none => haltTarget
  | some l => some (.inl l)

def configuration (haltTarget : Option (Λ ⊕ Λextra)) (extraState : τ)
    (extraTapes : ∀ e, List (Δ e)) (c : Cfg Γ Λ σ) :
    Cfg (Alphabet Γ Δ) (Λ ⊕ Λextra) (σ × τ) where
  l := label haltTarget c.l
  var := (c.var, extraState)
  stk := tapes c.stk extraTapes

def statement (haltTarget : Option (Λ ⊕ Λextra)) :
    Stmt Γ Λ σ → Stmt (Alphabet Γ Δ) (Λ ⊕ Λextra) (σ × τ)
  | .push k f next => .push (.inl k) (fun st => f st.1) (statement haltTarget next)
  | .peek k f next => .peek (.inl k) (fun st v => (f st.1 v, st.2))
      (statement haltTarget next)
  | .pop k f next => .pop (.inl k) (fun st v => (f st.1 v, st.2))
      (statement haltTarget next)
  | .load f next => .load (fun st => (f st.1, st.2)) (statement haltTarget next)
  | .branch f yes no => .branch (fun st => f st.1)
      (statement haltTarget yes) (statement haltTarget no)
  | .goto f => .goto (fun st => .inl (f st.1))
  | .halt => match haltTarget with
      | none => .halt
      | some l => .goto (fun _ => l)

variable [DecidableEq K] [DecidableEq E]

theorem tapes_update (source : ∀ k, List (Γ k)) (extra : ∀ e, List (Δ e))
    (k : K) (value : List (Γ k)) :
    tapes (Function.update source k value) extra =
      Function.update (tapes source extra) (.inl k) value := by
  funext j
  cases j with
  | inl j =>
    by_cases h : j = k
    · subst j
      simp [Function.update]
    · simp [Function.update, h]
  | inr e => simp [Function.update]

theorem stepAux_simulation (haltTarget : Option (Λ ⊕ Λextra))
    (extraState : τ) (extraTapes : ∀ e, List (Δ e))
    (q : Stmt Γ Λ σ) (state : σ) (source : ∀ k, List (Γ k)) :
    stepAux (statement haltTarget q) (state, extraState) (tapes source extraTapes) =
      configuration haltTarget extraState extraTapes (stepAux q state source) := by
  induction q generalizing state source with
  | push k f next ih =>
    simp only [statement, stepAux, tapes_inl]
    rw [← tapes_update]
    exact ih state (Function.update source k (f state :: source k))
  | peek k f next ih =>
    simpa only [statement, stepAux, tapes_inl] using
      ih (f state (source k).head?) source
  | pop k f next ih =>
    simp only [statement, stepAux, tapes_inl]
    rw [← tapes_update]
    exact ih (f state (source k).head?) (Function.update source k (source k).tail)
  | load f next ih =>
    simpa only [statement, stepAux] using ih (f state) source
  | branch f yes no ihYes ihNo =>
    cases h : f state with
    | false => simpa only [statement, stepAux, h, Bool.cond_false] using ihNo state source
    | true => simpa only [statement, stepAux, h, Bool.cond_true] using ihYes state source
  | goto f => rfl
  | halt => cases haltTarget <;> rfl

end MinUncutGames.Foundations.Complexity.MachineEmbedding

namespace MinUncutGames.Foundations.Complexity.MachineComposition

def advance {σ : Type} (step : σ → Option σ) (state : Option σ) : Option σ :=
  state.bind step

@[simp] theorem advance_none {σ : Type} (step : σ → Option σ) :
    advance step none = none := rfl

@[simp] theorem advance_some {σ : Type} (step : σ → Option σ) (state : σ) :
    advance step (some state) = step state := rfl

@[simp] theorem advance_iterate_none {σ : Type} (step : σ → Option σ) (n : Nat) :
    (advance step)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, advance_none]

theorem liftSuccessfulTrace {σ τ : Type} (source : σ → Option σ)
    (target : τ → Option τ) (embed : σ → τ)
    (simulation : ∀ a b, source a = some b → target (embed a) = some (embed b))
    (n : Nat) (start finish : σ)
    (trace : (advance source)^[n] (some start) = some finish) :
    (advance target)^[n] (some (embed start)) = some (embed finish) := by
  induction n generalizing start with
  | zero =>
      have same := Option.some.inj trace
      cases same
      rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply] at trace ⊢
      change (advance source)^[n] (source start) = some finish at trace
      change (advance target)^[n] (target (embed start)) = some (embed finish)
      cases firstStep : source start with
      | none =>
          rw [firstStep, advance_iterate_none] at trace
          contradiction
      | some intermediate =>
          rw [firstStep] at trace
          rw [simulation start intermediate firstStep]
          exact ih intermediate trace

def liftExecutionInTime {σ τ : Type} (source : σ → Option σ)
    (target : τ → Option τ) (embed : σ → τ)
    (simulation : ∀ a b, source a = some b → target (embed a) = some (embed b))
    {start finish : σ} {budget : Nat}
    (execution : StateTransition.EvalsToInTime source start (some finish) budget) :
    StateTransition.EvalsToInTime target (embed start) (some (embed finish)) budget where
  steps := execution.steps
  evals_in_steps := by
    have sourceTrace := execution.evals_in_steps
    change (advance source)^[execution.steps] (some start) = some finish at sourceTrace
    change (advance target)^[execution.steps] (some (embed start)) = some (embed finish)
    exact liftSuccessfulTrace source target embed simulation execution.steps start finish sourceTrace
  steps_le_m := execution.steps_le_m

@[simp] theorem liftExecutionInTime_steps {σ τ : Type} (source : σ → Option σ)
    (target : τ → Option τ) (embed : σ → τ)
    (simulation : ∀ a b, source a = some b → target (embed a) = some (embed b))
    {start finish : σ} {budget : Nat}
    (execution : StateTransition.EvalsToInTime source start (some finish) budget) :
    (liftExecutionInTime source target embed simulation execution).steps = execution.steps := rfl

theorem natPolynomial_eval_mono (p : Polynomial Nat) {a b : Nat} (h : a ≤ b) :
    p.eval a ≤ p.eval b := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simpa only [Polynomial.eval_add] using Nat.add_le_add hp hq
  | monomial degree coefficient =>
      simp only [Polynomial.eval_monomial]
      exact Nat.mul_le_mul_left coefficient (Nat.pow_le_pow_left h degree)

noncomputable def compositionPolynomial (first second intermediate : Polynomial Nat) : Polynomial Nat :=
  first + Polynomial.C 2 * (intermediate + 1) + second.comp intermediate

theorem compositionBudget_le (first second intermediate : Polynomial Nat)
    (inputLength intermediateLength : Nat)
    (intermediateBound : intermediateLength ≤ intermediate.eval inputLength) :
    first.eval inputLength + 2 * (intermediateLength + 1) + second.eval intermediateLength ≤
      (compositionPolynomial first second intermediate).eval inputLength := by
  have secondBound := natPolynomial_eval_mono second intermediateBound
  have transferBound := Nat.mul_le_mul_left 2 (Nat.add_le_add_right intermediateBound 1)
  simp only [compositionPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_one, Polynomial.eval_comp]
  omega

end MinUncutGames.Foundations.Complexity.MachineComposition

namespace MinUncutGames.Reduction.MachineTransfer

open Turing

abbrev alphabet (α β : Type) : Bool → Type
  | false => α
  | true => β

variable {α β : Type} [Fintype α] [Fintype β]

def loop (f : α → β) (fallback : β) :
    TM2.Stmt (alphabet α β) Unit (Option β) :=
  .pop false (fun _ head => head.map f)
    (.branch Option.isSome
      (.push true (fun state => state.getD fallback) (.goto fun _ => ()))
      .halt)

def machine (f : α → β) (fallback : β) : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ := alphabet α β
  Λ := Unit
  main := ()
  σ := Option β
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype α)
  m _ := loop f fallback

def tapeStacks (input : List α) (output : List β) :
    (side : Bool) → List (alphabet α β side)
  | false => input
  | true => output

def running (f : α → β) (fallback : β) (input : List α) (output : List β)
    (state : Option β) : (machine f fallback).Cfg :=
  ⟨some (), state, tapeStacks input output⟩

def halted (f : α → β) (fallback : β) (output : List β) : (machine f fallback).Cfg :=
  ⟨none, none, tapeStacks (α := α) [] output⟩

omit [Fintype α] [Fintype β] in
theorem update_input (input replacement : List α) (output : List β) :
    Function.update (tapeStacks input output) false replacement = tapeStacks replacement output := by
  funext side
  cases side <;> rfl

omit [Fintype α] [Fintype β] in
theorem update_output (input : List α) (output replacement : List β) :
    Function.update (tapeStacks input output) true replacement = tapeStacks input replacement := by
  funext side
  cases side <;> rfl

theorem step_empty (f : α → β) (fallback : β) (output : List β) (state : Option β) :
    (machine f fallback).step (running f fallback [] output state) =
      some (halted f fallback output) := by
  change some (TM2.stepAux (loop f fallback) state (tapeStacks (α := α) [] output)) = _
  simp [loop, TM2.stepAux, tapeStacks, halted, Function.update]
  rw [update_input]
  rfl

theorem step_cons (f : α → β) (fallback : β) (head : α) (input : List α)
    (output : List β) (state : Option β) :
    (machine f fallback).step (running f fallback (head :: input) output state) =
      some (running f fallback input (f head :: output) (some (f head))) := by
  change some (TM2.stepAux (loop f fallback) state (tapeStacks (head :: input) output)) = _
  simp [loop, TM2.stepAux, tapeStacks, running, Function.update]
  rw [update_input, update_output]
  rfl

def next (f : α → β) (fallback : β) (configuration : Option (machine f fallback).Cfg) :
    Option (machine f fallback).Cfg := configuration.bind (machine f fallback).step

theorem transfer_steps (f : α → β) (fallback : β) (input : List α) (output : List β)
    (state : Option β) :
    (next f fallback)^[input.length + 1] (some (running f fallback input output state)) =
      some (halted f fallback (input.reverse.map f ++ output)) := by
  induction input generalizing output state with
  | nil =>
    simpa only [List.length_nil, Nat.zero_add, Function.iterate_one, next,
      Option.bind_some, List.reverse_nil, List.map_nil, List.nil_append]
      using step_empty f fallback output state
  | cons head input ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    change (next f fallback)^[input.length + 1]
      ((machine f fallback).step (running f fallback (head :: input) output state)) = _
    rw [step_cons, ih]
    simp only [List.reverse_cons, List.map_append, List.map_singleton,
      List.append_assoc, List.singleton_append]

theorem initList_eq (f : α → β) (fallback : β) (input : List α) :
    initList (machine f fallback) input = running f fallback input [] none := by
  unfold initList running
  congr 1
  funext side
  cases side <;> rfl

theorem haltList_eq (f : α → β) (fallback : β) (output : List β) :
    haltList (machine f fallback) output = halted f fallback output := by
  unfold haltList halted
  congr 1
  funext side
  cases side <;> rfl

theorem transfer_init_steps (f : α → β) (fallback : β) (input : List α) :
    (next f fallback)^[input.length + 1] (some (initList (machine f fallback) input)) =
      some (haltList (machine f fallback) (input.reverse.map f)) := by
  have ht := transfer_steps f fallback input [] none
  simp only [List.append_nil] at ht
  exact (congrArg (fun c => (next f fallback)^[input.length + 1] (some c))
    (initList_eq f fallback input)).trans
    (ht.trans ((congrArg some (haltList_eq f fallback (input.reverse.map f))).symm))

def outputsInTime (f : α → β) (fallback : β) (input : List α) :
    TM2OutputsInTime (machine f fallback) input (some (input.reverse.map f))
      (input.length + 1) where
  steps := input.length + 1
  evals_in_steps := transfer_init_steps f fallback input
  steps_le_m := Nat.le_refl _

@[simp] theorem outputsInTime_steps (f : α → β) (fallback : β) (input : List α) :
    (outputsInTime f fallback input).steps = input.length + 1 := rfl

variable {K Λ σ : Type} {Γ : K → Type} [DecidableEq K]

def exitAt (dst : K) (exit : Option Λ) : TM2.Stmt Γ Λ (σ × Option (Γ dst)) :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

def loopAt (src dst : K) (f : Γ src → Γ dst) (fallback : Γ dst)
    (loopLabel : Λ) (exit : Option Λ) : TM2.Stmt Γ Λ (σ × Option (Γ dst)) :=
  .pop src (fun state head => (state.1, head.map f))
    (.branch (fun state => state.2.isSome)
      (.push dst (fun state => state.2.getD fallback) (.goto fun _ => loopLabel))
      (exitAt dst exit))

def tapesAt (src dst : K) (base : (k : K) → List (Γ k))
    (input : List (Γ src)) (output : List (Γ dst)) : (k : K) → List (Γ k) :=
  Function.update (Function.update base src input) dst output

@[simp] theorem tapesAt_src (src dst : K) (distinct : src ≠ dst)
    (base : (k : K) → List (Γ k)) (input : List (Γ src)) (output : List (Γ dst)) :
    tapesAt src dst base input output src = input := by
  simp [tapesAt, distinct]

@[simp] theorem tapesAt_dst (src dst : K)
    (base : (k : K) → List (Γ k)) (input : List (Γ src)) (output : List (Γ dst)) :
    tapesAt src dst base input output dst = output := by
  simp [tapesAt]

@[simp] theorem tapesAt_self (src dst : K) (base : (k : K) → List (Γ k)) :
    tapesAt src dst base (base src) (base dst) = base := by
  simp [tapesAt]

theorem update_tapesAt_src (src dst : K) (distinct : src ≠ dst)
    (base : (k : K) → List (Γ k)) (input replacement : List (Γ src))
    (output : List (Γ dst)) :
    Function.update (tapesAt src dst base input output) src replacement =
      tapesAt src dst base replacement output := by
  funext k
  by_cases hs : k = src
  · subst k
    simp [tapesAt, distinct]
  · by_cases hd : k = dst
    · subst k
      simp [tapesAt, Ne.symm distinct]
    · simp [tapesAt, hs, hd]

theorem update_tapesAt_dst (src dst : K)
    (base : (k : K) → List (Γ k)) (input : List (Γ src))
    (output replacement : List (Γ dst)) :
    Function.update (tapesAt src dst base input output) dst replacement =
      tapesAt src dst base input replacement := by
  funext k
  by_cases hd : k = dst
  · subst k
    simp [tapesAt]
  · simp [tapesAt, hd]

def nextAt (dst : K) (program : Λ → TM2.Stmt Γ Λ (σ × Option (Γ dst)))
    (configuration : Option (TM2.Cfg Γ Λ (σ × Option (Γ dst)))) :
    Option (TM2.Cfg Γ Λ (σ × Option (Γ dst))) :=
  configuration.bind (TM2.step program)

theorem stepAt_empty (src dst : K) (distinct : src ≠ dst)
    (f : Γ src → Γ dst) (fallback : Γ dst) (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Γ Λ (σ × Option (Γ dst)))
    (atLoop : program loopLabel = loopAt src dst f fallback loopLabel exit)
    (base : (k : K) → List (Γ k)) (output : List (Γ dst))
    (ambient : σ) (register : Option (Γ dst)) :
    TM2.step program ⟨some loopLabel, (ambient, register), tapesAt src dst base [] output⟩ =
      some ⟨exit, (ambient, none), tapesAt src dst base [] output⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, register)
    (tapesAt src dst base [] output)) = _
  rw [atLoop]
  cases exit <;>
    simp [loopAt, exitAt, TM2.stepAux, tapesAt_src, distinct, update_tapesAt_src]

theorem stepAt_cons (src dst : K) (distinct : src ≠ dst)
    (f : Γ src → Γ dst) (fallback : Γ dst) (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Γ Λ (σ × Option (Γ dst)))
    (atLoop : program loopLabel = loopAt src dst f fallback loopLabel exit)
    (base : (k : K) → List (Γ k)) (head : Γ src) (input : List (Γ src))
    (output : List (Γ dst)) (ambient : σ) (register : Option (Γ dst)) :
    TM2.step program
      ⟨some loopLabel, (ambient, register), tapesAt src dst base (head :: input) output⟩ =
      some ⟨some loopLabel, (ambient, some (f head)),
        tapesAt src dst base input (f head :: output)⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, register)
    (tapesAt src dst base (head :: input) output)) = _
  rw [atLoop]
  simp [loopAt, TM2.stepAux, tapesAt_src, tapesAt_dst, distinct,
    update_tapesAt_src, update_tapesAt_dst]

theorem transferAt_steps (src dst : K) (distinct : src ≠ dst)
    (f : Γ src → Γ dst) (fallback : Γ dst) (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Γ Λ (σ × Option (Γ dst)))
    (atLoop : program loopLabel = loopAt src dst f fallback loopLabel exit)
    (base : (k : K) → List (Γ k)) (input : List (Γ src)) (output : List (Γ dst))
    (ambient : σ) (register : Option (Γ dst)) :
    (nextAt dst program)^[input.length + 1]
      (some ⟨some loopLabel, (ambient, register), tapesAt src dst base input output⟩) =
      some ⟨exit, (ambient, none), tapesAt src dst base [] (input.reverse.map f ++ output)⟩ := by
  induction input generalizing output register with
  | nil =>
    simpa only [List.length_nil, Nat.zero_add, Function.iterate_one, nextAt,
      Option.bind_some, List.reverse_nil, List.map_nil, List.nil_append]
      using stepAt_empty src dst distinct f fallback loopLabel exit program atLoop base output
        ambient register
  | cons head input ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    change (nextAt dst program)^[input.length + 1]
      (TM2.step program
        ⟨some loopLabel, (ambient, register), tapesAt src dst base (head :: input) output⟩) = _
    rw [stepAt_cons src dst distinct f fallback loopLabel exit program atLoop, ih]
    simp only [List.reverse_cons, List.map_append, List.map_singleton,
      List.append_assoc, List.singleton_append]

theorem transferAt_fromTapes (src dst : K) (distinct : src ≠ dst)
    (f : Γ src → Γ dst) (fallback : Γ dst) (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Γ Λ (σ × Option (Γ dst)))
    (atLoop : program loopLabel = loopAt src dst f fallback loopLabel exit)
    (base : (k : K) → List (Γ k)) (ambient : σ) (register : Option (Γ dst)) :
    (nextAt dst program)^[(base src).length + 1]
      (some ⟨some loopLabel, (ambient, register), base⟩) =
      some ⟨exit, (ambient, none),
        tapesAt src dst base [] ((base src).reverse.map f ++ base dst)⟩ := by
  simpa only [tapesAt_self] using
    transferAt_steps src dst distinct f fallback loopLabel exit program atLoop base
      (base src) (base dst) ambient register

def transferAtInTime (src dst : K) (distinct : src ≠ dst)
    (f : Γ src → Γ dst) (fallback : Γ dst) (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Γ Λ (σ × Option (Γ dst)))
    (atLoop : program loopLabel = loopAt src dst f fallback loopLabel exit)
    (base : (k : K) → List (Γ k)) (ambient : σ) (register : Option (Γ dst)) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some loopLabel, (ambient, register), base⟩
      (some ⟨exit, (ambient, none),
        tapesAt src dst base [] ((base src).reverse.map f ++ base dst)⟩)
      ((base src).length + 1) where
  steps := (base src).length + 1
  evals_in_steps := transferAt_fromTapes src dst distinct f fallback loopLabel exit
    program atLoop base ambient register
  steps_le_m := Nat.le_refl _

end MinUncutGames.Reduction.MachineTransfer

end OAI
end

section
-- module Solutions.OAIQ092_CC.MinUncut_Machines_MachineCompare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.MachineCompare

open Turing
open MinUncutGames.Reduction.MachineTransfer

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (K : Type) : K → Type := fun _ => Bool
abbrev State (σ : Type) := σ × Bool × Option Bool × Option Bool

def exitAt (exit : Option Λ) : TM2.Stmt (Alphabet K) Λ (State σ) :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

def finish (exit : Option Λ) : TM2.Stmt (Alphabet K) Λ (State σ) :=
  .load (fun state => (state.1, false, none, none)) (exitAt exit)

def loop (left right : K) (loopLabel : Λ) (equalExit differentExit : Option Λ) :
    TM2.Stmt (Alphabet K) Λ (State σ) :=
  .pop left (fun state head => (state.1, state.2.1, head, state.2.2.2))
    (.pop right (fun state head => (state.1, state.2.1, state.2.2.1, head))
      (.branch (fun state => state.2.2.1.isNone && state.2.2.2.isNone)
        (.branch (fun state => state.2.1) (finish differentExit) (finish equalExit))
        (.load (fun state =>
          (state.1, state.2.1 || decide (state.2.2.1 ≠ state.2.2.2), none, none))
          (.goto fun _ => loopLabel))))

def mismatch (flag : Bool) (leftWord rightWord : List Bool) : Bool :=
  flag || decide (leftWord ≠ rightWord)

@[simp] theorem mismatch_nil_nil (flag : Bool) : mismatch flag [] [] = flag := by
  simp [mismatch]

@[simp] theorem mismatch_nil_cons (flag head : Bool) (tail : List Bool) :
    mismatch flag [] (head :: tail) = true := by simp [mismatch]

@[simp] theorem mismatch_cons_nil (flag head : Bool) (tail : List Bool) :
    mismatch flag (head :: tail) [] = true := by simp [mismatch]

@[simp] theorem mismatch_true (leftWord rightWord : List Bool) :
    mismatch true leftWord rightWord = true := by simp [mismatch]

theorem mismatch_cons (flag leftHead rightHead : Bool) (leftTail rightTail : List Bool) :
    mismatch (flag || decide (leftHead ≠ rightHead)) leftTail rightTail =
      mismatch flag (leftHead :: leftTail) (rightHead :: rightTail) := by
  cases flag <;> cases leftHead <;> cases rightHead <;> simp [mismatch]

@[simp] theorem stepAux_exitAt (exit : Option Λ) (state : State σ)
    (tapes : K → List Bool) :
    TM2.stepAux (exitAt exit) state tapes = ⟨exit, state, tapes⟩ := by
  cases exit <;> rfl

@[simp] theorem stepAux_finish (exit : Option Λ) (state : State σ)
    (tapes : K → List Bool) :
    TM2.stepAux (finish exit) state tapes =
      ⟨exit, (state.1, false, none, none), tapes⟩ := by
  simp [finish, TM2.stepAux]

theorem update_left (left right : K) (distinct : left ≠ right)
    (base : K → List Bool) (leftWord rightWord replacement : List Bool) :
    Function.update (tapesAt left right base leftWord rightWord) left replacement =
      tapesAt left right base replacement rightWord := by
  funext k
  by_cases hl : k = left
  · subst k
    simp [tapesAt, distinct]
  · by_cases hr : k = right
    · subst k
      simp [tapesAt, Ne.symm distinct]
    · simp [tapesAt, hl, hr]

theorem update_right (left right : K) (base : K → List Bool)
    (leftWord rightWord replacement : List Bool) :
    Function.update (tapesAt left right base leftWord rightWord) right replacement =
      tapesAt left right base leftWord replacement := by
  simp [tapesAt]

theorem step_empty (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (ambient : σ) (flag : Bool)
    (leftRegister rightRegister : Option Bool) :
    TM2.step program
      ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
        tapesAt left right base [] []⟩ =
      some ⟨if flag then differentExit else equalExit, (ambient, false, none, none),
        tapesAt left right base [] []⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, flag, leftRegister, rightRegister)
    (tapesAt left right base [] [])) = _
  rw [atLoop]
  cases flag <;>
    simp [loop, TM2.stepAux, distinct, update_left, update_right]

theorem step_nil_cons (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (head : Bool) (tail : List Bool) (ambient : σ) (flag : Bool)
    (leftRegister rightRegister : Option Bool) :
    TM2.step program
      ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
        tapesAt left right base [] (head :: tail)⟩ =
      some ⟨some loopLabel, (ambient, true, none, none), tapesAt left right base [] tail⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, flag, leftRegister, rightRegister)
    (tapesAt left right base [] (head :: tail))) = _
  rw [atLoop]
  simp [loop, TM2.stepAux, distinct, update_left, update_right]

theorem step_cons_nil (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (head : Bool) (tail : List Bool) (ambient : σ) (flag : Bool)
    (leftRegister rightRegister : Option Bool) :
    TM2.step program
      ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
        tapesAt left right base (head :: tail) []⟩ =
      some ⟨some loopLabel, (ambient, true, none, none), tapesAt left right base tail []⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, flag, leftRegister, rightRegister)
    (tapesAt left right base (head :: tail) [])) = _
  rw [atLoop]
  simp [loop, TM2.stepAux, distinct, update_left, update_right]

theorem step_cons_cons (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (leftHead rightHead : Bool) (leftTail rightTail : List Bool)
    (ambient : σ) (flag : Bool) (leftRegister rightRegister : Option Bool) :
    TM2.step program
      ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
        tapesAt left right base (leftHead :: leftTail) (rightHead :: rightTail)⟩ =
      some ⟨some loopLabel,
        (ambient, flag || decide (leftHead ≠ rightHead), none, none),
        tapesAt left right base leftTail rightTail⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, flag, leftRegister, rightRegister)
    (tapesAt left right base (leftHead :: leftTail) (rightHead :: rightTail))) = _
  rw [atLoop]
  simp [loop, TM2.stepAux, distinct, update_left, update_right]

theorem trace_left_empty (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (rightWord : List Bool) (ambient : σ) (flag : Bool)
    (leftRegister rightRegister : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[rightWord.length + 1]
      (some ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
        tapesAt left right base [] rightWord⟩) =
      some ⟨if mismatch flag [] rightWord then differentExit else equalExit,
        (ambient, false, none, none), tapesAt left right base [] []⟩ := by
  induction rightWord generalizing flag leftRegister rightRegister with
  | nil =>
    simpa only [List.length_nil, Nat.zero_add, Function.iterate_one,
      MachineComposition.advance_some, mismatch_nil_nil] using
      step_empty left right distinct loopLabel equalExit differentExit program atLoop base
        ambient flag leftRegister rightRegister
  | cons head tail ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    change (MachineComposition.advance (TM2.step program))^[tail.length + 1]
      (TM2.step program ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
        tapesAt left right base [] (head :: tail)⟩) = _
    rw [step_nil_cons left right distinct loopLabel equalExit differentExit program atLoop]
    simpa only [mismatch_true, mismatch_nil_cons] using ih true none none

theorem compareTrace_flag (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (leftWord rightWord : List Bool) (ambient : σ) (flag : Bool)
    (leftRegister rightRegister : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[max leftWord.length rightWord.length + 1]
      (some ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
        tapesAt left right base leftWord rightWord⟩) =
      some ⟨if mismatch flag leftWord rightWord then differentExit else equalExit,
        (ambient, false, none, none), tapesAt left right base [] []⟩ := by
  induction leftWord generalizing rightWord flag leftRegister rightRegister with
  | nil =>
    simpa only [List.length_nil, Nat.zero_max] using
      trace_left_empty left right distinct loopLabel equalExit differentExit program atLoop
        base rightWord ambient flag leftRegister rightRegister
  | cons head tail ih =>
    cases rightWord with
    | nil =>
      rw [List.length_cons, List.length_nil, Nat.max_zero, Function.iterate_succ_apply]
      change (MachineComposition.advance (TM2.step program))^[tail.length + 1]
        (TM2.step program ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
          tapesAt left right base (head :: tail) []⟩) = _
      rw [step_cons_nil left right distinct loopLabel equalExit differentExit program atLoop]
      simpa only [List.length_nil, Nat.max_zero, mismatch_true, mismatch_cons_nil] using
        ih [] true none none
    | cons rightHead rightTail =>
      rw [List.length_cons, List.length_cons, Nat.succ_max_succ, Function.iterate_succ_apply]
      change (MachineComposition.advance (TM2.step program))^[max tail.length rightTail.length + 1]
        (TM2.step program ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
          tapesAt left right base (head :: tail) (rightHead :: rightTail)⟩) = _
      rw [step_cons_cons left right distinct loopLabel equalExit differentExit program atLoop]
      simpa only [mismatch_cons] using
        ih rightTail (flag || decide (head ≠ rightHead)) none none

theorem compareTrace (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (leftWord rightWord : List Bool) (ambient : σ)
    (leftRegister rightRegister : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[max leftWord.length rightWord.length + 1]
      (some ⟨some loopLabel, (ambient, false, leftRegister, rightRegister),
        tapesAt left right base leftWord rightWord⟩) =
      some ⟨if leftWord = rightWord then equalExit else differentExit,
        (ambient, false, none, none), tapesAt left right base [] []⟩ := by
  have h := compareTrace_flag left right distinct loopLabel equalExit differentExit program
    atLoop base leftWord rightWord ambient false leftRegister rightRegister
  by_cases heq : leftWord = rightWord <;> simpa [mismatch, heq] using h

theorem compareTrace_fromTapes (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (ambient : σ) (leftRegister rightRegister : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[max (base left).length (base right).length + 1]
      (some ⟨some loopLabel, (ambient, false, leftRegister, rightRegister), base⟩) =
      some ⟨if base left = base right then equalExit else differentExit,
        (ambient, false, none, none), tapesAt left right base [] []⟩ := by
  simpa only [tapesAt_self] using
    compareTrace left right distinct loopLabel equalExit differentExit program atLoop base
      (base left) (base right) ambient leftRegister rightRegister

def compareInTime (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (ambient : σ) (leftRegister rightRegister : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some loopLabel, (ambient, false, leftRegister, rightRegister), base⟩
      (some ⟨if base left = base right then equalExit else differentExit,
        (ambient, false, none, none), tapesAt left right base [] []⟩)
      (max (base left).length (base right).length + 1) where
  steps := max (base left).length (base right).length + 1
  evals_in_steps := compareTrace_fromTapes left right distinct loopLabel equalExit differentExit
    program atLoop base ambient leftRegister rightRegister
  steps_le_m := Nat.le_refl _

@[simp] theorem compareInTime_steps (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (ambient : σ) (leftRegister rightRegister : Option Bool) :
    (compareInTime left right distinct loopLabel equalExit differentExit program atLoop base
      ambient leftRegister rightRegister).steps =
        max (base left).length (base right).length + 1 := rfl

end MinUncutGames.Foundations.Complexity.MachineCompare

namespace MinUncutGames.Foundations.Complexity.MachineControl

open Turing.TM2

variable {K Λ Λ' σ σ' : Type} {Γ : K → Type}

def configuration (labels : Λ → Λ') (states : σ ≃ σ') (c : Cfg Γ Λ σ) :
    Cfg Γ Λ' σ' where
  l := c.l.map labels
  var := states c.var
  stk := c.stk

def statement (labels : Λ → Λ') (states : σ ≃ σ') : Stmt Γ Λ σ → Stmt Γ Λ' σ'
  | .push k f next => .push k (fun st => f (states.symm st)) (statement labels states next)
  | .peek k f next => .peek k (fun st v => states (f (states.symm st) v))
      (statement labels states next)
  | .pop k f next => .pop k (fun st v => states (f (states.symm st) v))
      (statement labels states next)
  | .load f next => .load (fun st => states (f (states.symm st)))
      (statement labels states next)
  | .branch f yes no => .branch (fun st => f (states.symm st))
      (statement labels states yes) (statement labels states no)
  | .goto f => .goto (fun st => labels (f (states.symm st)))
  | .halt => .halt

variable [DecidableEq K]

theorem stepAux_simulation (labels : Λ → Λ') (states : σ ≃ σ')
    (q : Stmt Γ Λ σ) (state : σ) (tapes : ∀ k, List (Γ k)) :
    stepAux (statement labels states q) (states state) tapes =
      configuration labels states (stepAux q state tapes) := by
  induction q generalizing state tapes with
  | push k f next ih =>
    simpa only [statement, stepAux, Equiv.symm_apply_apply] using
      ih state (Function.update tapes k (f state :: tapes k))
  | peek k f next ih =>
    simpa only [statement, stepAux, Equiv.symm_apply_apply] using
      ih (f state (tapes k).head?) tapes
  | pop k f next ih =>
    simpa only [statement, stepAux, Equiv.symm_apply_apply] using
      ih (f state (tapes k).head?) (Function.update tapes k (tapes k).tail)
  | load f next ih =>
    simpa only [statement, stepAux, Equiv.symm_apply_apply] using ih (f state) tapes
  | branch f yes no ihYes ihNo =>
    cases h : f state with
    | false =>
      simpa only [statement, stepAux, Equiv.symm_apply_apply, h, Bool.cond_false] using
        ihNo state tapes
    | true =>
      simpa only [statement, stepAux, Equiv.symm_apply_apply, h, Bool.cond_true] using
        ihYes state tapes
  | goto f => simp [statement, stepAux, configuration]
  | halt => rfl

end MinUncutGames.Foundations.Complexity.MachineControl

end OAI
end

section
-- module Solutions.OAIQ092_CC.MinUncut_Machines_MachineSubstitution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Reduction.MachineSubstitution

open Turing

open MinUncutGames.Foundations.Complexity

section PushWord

variable {K Λ σ : Type} {Γ : K → Type} [DecidableEq K]

def pushWord (dst : K) : List (Γ dst) → TM2.Stmt Γ Λ σ → TM2.Stmt Γ Λ σ
  | [], continuation => continuation
  | symbol :: word, continuation =>
      .push dst (fun _ => symbol) (pushWord dst word continuation)

theorem stepAux_pushWord (dst : K) (word : List (Γ dst))
    (continuation : TM2.Stmt Γ Λ σ) (state : σ) (tapes : ∀ k, List (Γ k)) :
    TM2.stepAux (pushWord dst word continuation) state tapes =
      TM2.stepAux continuation state
        (Function.update tapes dst (word.reverse ++ tapes dst)) := by
  induction word generalizing tapes with
  | nil => simp [pushWord]
  | cons symbol word ih =>
    simp only [pushWord, TM2.stepAux]
    rw [ih]
    simp only [Function.update_self, Function.update_idem, List.reverse_cons,
      List.append_assoc, List.singleton_append]

end PushWord

def loop : TM2.Stmt (fun _ : Bool => Bool) (Option Bool) (Option Bool) :=
  .pop false (fun _ head => head)
    (.branch Option.isSome
      (.goto fun state => some (state.getD false))
      .halt)

def program (emit : Bool → List Bool) :
    Option Bool → TM2.Stmt (fun _ : Bool => Bool) (Option Bool) (Option Bool)
  | none => loop
  | some symbol => pushWord true (emit symbol) (.goto fun _ => none)

def machine (emit : Bool → List Bool) : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ _ := Bool
  Λ := Option Bool
  main := none
  σ := Option Bool
  initialState := none
  m := program emit

def tapeStacks (input output : List Bool) : Bool → List Bool :=
  fun side => if side then output else input

def running (emit : Bool → List Bool) (input output : List Bool) (state : Option Bool) :
    (machine emit).Cfg :=
  ⟨some none, state, tapeStacks input output⟩

def emitting (emit : Bool → List Bool) (symbol : Bool)
    (input output : List Bool) (state : Option Bool) : (machine emit).Cfg :=
  ⟨some (some symbol), state, tapeStacks input output⟩

def halted (emit : Bool → List Bool) (output : List Bool) : (machine emit).Cfg :=
  ⟨none, none, tapeStacks [] output⟩

theorem update_input (input output replacement : List Bool) :
    Function.update (tapeStacks input output) false replacement = tapeStacks replacement output := by
  funext side
  cases side <;> simp [tapeStacks]

theorem update_output (input output replacement : List Bool) :
    Function.update (tapeStacks input output) true replacement = tapeStacks input replacement := by
  funext side
  cases side <;> simp [tapeStacks]

theorem step_empty (emit : Bool → List Bool) (output : List Bool) (state : Option Bool) :
    (machine emit).step (running emit [] output state) = some (halted emit output) := by
  change some (TM2.stepAux loop state (tapeStacks [] output)) = some (halted emit output)
  simp [loop, TM2.stepAux, tapeStacks, halted]
  rw [update_input]
  rfl

theorem step_cons (emit : Bool → List Bool) (symbol : Bool)
    (input output : List Bool) (state : Option Bool) :
    (machine emit).step (running emit (symbol :: input) output state) =
      some (emitting emit symbol input output (some symbol)) := by
  change some (TM2.stepAux loop state (tapeStacks (symbol :: input) output)) = _
  simp [loop, TM2.stepAux, tapeStacks, emitting]
  rw [update_input]
  rfl

theorem step_emit (emit : Bool → List Bool) (symbol : Bool)
    (input output : List Bool) (state : Option Bool) :
    (machine emit).step (emitting emit symbol input output state) =
      some (running emit input ((emit symbol).reverse ++ output) state) := by
  change some (TM2.stepAux (pushWord true (emit symbol) (.goto fun _ => none))
    state (tapeStacks input output)) = _
  rw [stepAux_pushWord]
  simp only [TM2.stepAux]
  change some (⟨some none, state,
    Function.update (tapeStacks input output) true ((emit symbol).reverse ++ output)⟩ :
    (machine emit).Cfg) = _
  exact congrArg (fun st => (some ⟨some none, state, st⟩ :
    Option (TM2.Cfg (fun _ : Bool => Bool) (Option Bool) (Option Bool))))
    (update_output input output ((emit symbol).reverse ++ output))

def next (emit : Bool → List Bool) (configuration : Option (machine emit).Cfg) :
    Option (machine emit).Cfg :=
  configuration.bind (machine emit).step

theorem two_steps_cons (emit : Bool → List Bool) (symbol : Bool)
    (input output : List Bool) (state : Option Bool) :
    (next emit)^[2] (some (running emit (symbol :: input) output state)) =
      some (running emit input ((emit symbol).reverse ++ output) (some symbol)) := by
  change (machine emit).step (running emit (symbol :: input) output state) >>=
    (machine emit).step = _
  rw [step_cons]
  exact step_emit emit symbol input output (some symbol)

theorem substitution_steps (emit : Bool → List Bool)
    (input output : List Bool) (state : Option Bool) :
    (next emit)^[2 * input.length + 1] (some (running emit input output state)) =
      some (halted emit ((input.flatMap emit).reverse ++ output)) := by
  induction input generalizing output state with
  | nil =>
    simpa only [List.length_nil, Nat.mul_zero, Nat.zero_add, Function.iterate_one, next,
      Option.bind_some, List.flatMap_nil, List.reverse_nil, List.nil_append]
      using step_empty emit output state
  | cons symbol input ih =>
    rw [List.length_cons]
    rw [show 2 * (input.length + 1) + 1 = (2 * input.length + 1) + 2 by omega]
    rw [Function.iterate_add_apply, two_steps_cons, ih]
    simp only [List.flatMap_cons, List.reverse_append, List.append_assoc]

theorem initList_eq (emit : Bool → List Bool) (input : List Bool) :
    initList (machine emit) input = running emit input [] none := by
  unfold initList running
  congr 1
  funext side
  cases side <;> rfl

theorem haltList_eq (emit : Bool → List Bool) (output : List Bool) :
    haltList (machine emit) output = halted emit output := by
  unfold haltList halted
  congr 1

theorem substitution_init_steps (emit : Bool → List Bool) (input : List Bool) :
    (next emit)^[2 * input.length + 1] (some (initList (machine emit) input)) =
      some (haltList (machine emit) (input.flatMap emit).reverse) := by
  rw [initList_eq, haltList_eq]
  simpa only [List.append_nil] using substitution_steps emit input [] none

def outputsInTime (emit : Bool → List Bool) (input : List Bool) :
    TM2OutputsInTime (machine emit) input (some (input.flatMap emit).reverse)
      (2 * input.length + 1) where
  steps := 2 * input.length + 1
  evals_in_steps := substitution_init_steps emit input
  steps_le_m := Nat.le_refl _

@[simp] theorem outputsInTime_steps (emit : Bool → List Bool) (input : List Bool) :
    (outputsInTime emit input).steps = 2 * input.length + 1 := rfl

end MinUncutGames.Reduction.MachineSubstitution

end
section
namespace MinUncutGames.Reduction.MachineReverse

open Turing

def loop : TM2.Stmt (fun _ : Bool => Bool) Unit (Option Bool) :=
  .pop false (fun _ head => head)
    (.branch Option.isSome
      (.push true (fun state => state.getD false) (.goto fun _ => ()))
      .halt)

def machine : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := Option Bool
  initialState := none
  m _ := loop

def tapeStacks (input output : List Bool) : Bool → List Bool :=
  fun side => if side then output else input

def running (input output : List Bool) (state : Option Bool) : machine.Cfg :=
  ⟨some (), state, tapeStacks input output⟩

def halted (output : List Bool) : machine.Cfg :=
  ⟨none, none, tapeStacks [] output⟩

theorem update_input (input output replacement : List Bool) :
    Function.update (tapeStacks input output) false replacement = tapeStacks replacement output := by
  funext side
  cases side <;> simp [tapeStacks]

theorem update_output (input output replacement : List Bool) :
    Function.update (tapeStacks input output) true replacement = tapeStacks input replacement := by
  funext side
  cases side <;> simp [tapeStacks]

theorem step_empty (output : List Bool) (state : Option Bool) :
    machine.step (running [] output state) = some (halted output) := by
  change some (TM2.stepAux loop state (tapeStacks [] output)) = some (halted output)
  simp [loop, TM2.stepAux, tapeStacks, halted, Function.update]
  rw [update_input]
  rfl

theorem step_cons (head : Bool) (input output : List Bool) (state : Option Bool) :
    machine.step (running (head :: input) output state) =
      some (running input (head :: output) (some head)) := by
  change some (TM2.stepAux loop state (tapeStacks (head :: input) output)) = _
  simp [loop, TM2.stepAux, tapeStacks, running, Function.update]
  rw [update_input, update_output]
  rfl

def next (configuration : Option machine.Cfg) : Option machine.Cfg :=
  configuration.bind machine.step

theorem reverse_steps (input output : List Bool) (state : Option Bool) :
    next^[input.length + 1] (some (running input output state)) =
      some (halted (input.reverse ++ output)) := by
  induction input generalizing output state with
  | nil =>
    simpa only [List.length_nil, Nat.zero_add, Function.iterate_one, next,
      Option.bind_some, List.reverse_nil, List.nil_append] using step_empty output state
  | cons head input ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    change next^[input.length + 1]
      (machine.step (running (head :: input) output state)) = _
    rw [step_cons, ih]
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

theorem initList_eq (input : List Bool) :
    initList machine input = running input [] none := by
  unfold initList running
  congr 1
  funext side
  cases side <;> rfl

theorem haltList_eq (output : List Bool) : haltList machine output = halted output := by
  unfold haltList halted
  congr 1

theorem reverse_init_steps (input : List Bool) :
    next^[input.length + 1] (some (initList machine input)) =
      some (haltList machine input.reverse) := by
  rw [initList_eq, haltList_eq]
  simpa only [List.append_nil] using reverse_steps input [] none

def outputsInTime (input : List Bool) :
    TM2OutputsInTime machine input (some input.reverse) (input.length + 1) where
  steps := input.length + 1
  evals_in_steps := reverse_init_steps input
  steps_le_m := Nat.le_refl _

@[simp] theorem outputsInTime_steps (input : List Bool) :
    (outputsInTime input).steps = input.length + 1 := rfl

end MinUncutGames.Reduction.MachineReverse

end
section
namespace MinUncutGames.Foundations.Complexity.MachineStackSwap

open Turing.TM2

variable {A B C Λ σ : Type}
  {ΓA : A → Type} {ΓB : B → Type} {ΓC : C → Type}

abbrev Alphabet (ΓA : A → Type) (ΓB : B → Type) (ΓC : C → Type) :=
  MachineEmbedding.Alphabet ΓA (MachineEmbedding.Alphabet ΓB ΓC)

def tapes (source : ∀ k, List (Alphabet ΓA ΓB ΓC k)) :
    ∀ j, List (Alphabet ΓB ΓA ΓC j)
  | .inl b => source (.inr (.inl b))
  | .inr (.inl a) => source (.inl a)
  | .inr (.inr c) => source (.inr (.inr c))

@[simp] theorem tapes_first (source : ∀ k, List (Alphabet ΓA ΓB ΓC k)) (a : A) :
    tapes source (.inr (.inl a)) = source (.inl a) := rfl
@[simp] theorem tapes_second (source : ∀ k, List (Alphabet ΓA ΓB ΓC k)) (b : B) :
    tapes source (.inl b) = source (.inr (.inl b)) := rfl
@[simp] theorem tapes_third (source : ∀ k, List (Alphabet ΓA ΓB ΓC k)) (c : C) :
    tapes source (.inr (.inr c)) = source (.inr (.inr c)) := rfl

def configuration (c : Cfg (Alphabet ΓA ΓB ΓC) Λ σ) :
    Cfg (Alphabet ΓB ΓA ΓC) Λ σ where
  l := c.l
  var := c.var
  stk := tapes c.stk

def statement : Stmt (Alphabet ΓA ΓB ΓC) Λ σ → Stmt (Alphabet ΓB ΓA ΓC) Λ σ
  | .push (.inl a) f next => .push (.inr (.inl a)) f (statement next)
  | .push (.inr (.inl b)) f next => .push (.inl b) f (statement next)
  | .push (.inr (.inr c)) f next => .push (.inr (.inr c)) f (statement next)
  | .peek (.inl a) f next => .peek (.inr (.inl a)) f (statement next)
  | .peek (.inr (.inl b)) f next => .peek (.inl b) f (statement next)
  | .peek (.inr (.inr c)) f next => .peek (.inr (.inr c)) f (statement next)
  | .pop (.inl a) f next => .pop (.inr (.inl a)) f (statement next)
  | .pop (.inr (.inl b)) f next => .pop (.inl b) f (statement next)
  | .pop (.inr (.inr c)) f next => .pop (.inr (.inr c)) f (statement next)
  | .load f next => .load f (statement next)
  | .branch f yes no => .branch f (statement yes) (statement no)
  | .goto f => .goto f
  | .halt => .halt

variable [DecidableEq A] [DecidableEq B] [DecidableEq C]

theorem tapes_update_first (source : ∀ k, List (Alphabet ΓA ΓB ΓC k))
    (a : A) (value : List (ΓA a)) :
    tapes (Function.update source (.inl a) value) =
      Function.update (tapes source) (.inr (.inl a)) value := by
  funext j
  rcases j with b | a' | c
  · simp [Function.update]
  · by_cases h : a' = a
    · subst a'; simp [Function.update]
    · simp [Function.update, h]
  · simp [Function.update]

theorem tapes_update_second (source : ∀ k, List (Alphabet ΓA ΓB ΓC k))
    (b : B) (value : List (ΓB b)) :
    tapes (Function.update source (.inr (.inl b)) value) =
      Function.update (tapes source) (.inl b) value := by
  funext j
  rcases j with b' | a | c
  · by_cases h : b' = b
    · subst b'; simp [Function.update]
    · simp [Function.update, h]
  · simp [Function.update]
  · simp [Function.update]

theorem tapes_update_third (source : ∀ k, List (Alphabet ΓA ΓB ΓC k))
    (c : C) (value : List (ΓC c)) :
    tapes (Function.update source (.inr (.inr c)) value) =
      Function.update (tapes source) (.inr (.inr c)) value := by
  funext j
  rcases j with b | a | c'
  · simp [Function.update]
  · simp [Function.update]
  · by_cases h : c' = c
    · subst c'; simp [Function.update]
    · simp [Function.update, h]

theorem stepAux_simulation (q : Stmt (Alphabet ΓA ΓB ΓC) Λ σ)
    (state : σ) (source : ∀ k, List (Alphabet ΓA ΓB ΓC k)) :
    stepAux (statement q) state (tapes source) =
      configuration (stepAux q state source) := by
  induction q generalizing state source with
  | push k f next ih =>
    rcases k with a | b | c
    · simp only [statement, stepAux, tapes_first]
      rw [← tapes_update_first]
      exact ih state (Function.update source (.inl a) (f state :: source (.inl a)))
    · simp only [statement, stepAux, tapes_second]
      rw [← tapes_update_second]
      exact ih state (Function.update source (.inr (.inl b))
        (f state :: source (.inr (.inl b))))
    · simp only [statement, stepAux, tapes_third]
      rw [← tapes_update_third]
      exact ih state (Function.update source (.inr (.inr c))
        (f state :: source (.inr (.inr c))))
  | peek k f next ih =>
    rcases k with a | b | c
    · simpa only [statement, stepAux, tapes_first] using
        ih (f state (source (.inl a)).head?) source
    · simpa only [statement, stepAux, tapes_second] using
        ih (f state (source (.inr (.inl b))).head?) source
    · simpa only [statement, stepAux, tapes_third] using
        ih (f state (source (.inr (.inr c))).head?) source
  | pop k f next ih =>
    rcases k with a | b | c
    · simp only [statement, stepAux, tapes_first]
      rw [← tapes_update_first]
      exact ih (f state (source (.inl a)).head?)
        (Function.update source (.inl a) (source (.inl a)).tail)
    · simp only [statement, stepAux, tapes_second]
      rw [← tapes_update_second]
      exact ih (f state (source (.inr (.inl b))).head?)
        (Function.update source (.inr (.inl b)) (source (.inr (.inl b))).tail)
    · simp only [statement, stepAux, tapes_third]
      rw [← tapes_update_third]
      exact ih (f state (source (.inr (.inr c))).head?)
        (Function.update source (.inr (.inr c)) (source (.inr (.inr c))).tail)
  | load f next ih => simpa only [statement, stepAux] using ih (f state) source
  | branch f yes no ihYes ihNo =>
    cases h : f state with
    | false => simpa only [statement, stepAux, h, Bool.cond_false] using ihNo state source
    | true => simpa only [statement, stepAux, h, Bool.cond_true] using ihYes state source
  | goto f => rfl
  | halt => rfl

end MinUncutGames.Foundations.Complexity.MachineStackSwap

end
section
namespace MinUncutGames.Foundations.Complexity.MachineSequential

open Turing

abbrev Tape (first second : FinTM2) := first.K ⊕ (second.K ⊕ Unit)
abbrev Symbols (first second : FinTM2) : Tape first second → Type :=
  MachineEmbedding.Alphabet first.Γ
    (MachineEmbedding.Alphabet second.Γ (fun _ : Unit => second.Γ second.k₀))
abbrev Label (first second : FinTM2) := first.Λ ⊕ (Bool ⊕ second.Λ)
abbrev Register (second : FinTM2) := Option (second.Γ second.k₀)
abbrev State (first second : FinTM2) := (first.σ × second.σ) × Register second

def firstStates (first second : FinTM2) :
    first.σ × (second.σ × Register second) ≃ State first second where
  toFun st := ((st.1, st.2.1), st.2.2)
  invFun st := (st.1.1, (st.1.2, st.2))
  left_inv _ := rfl
  right_inv _ := rfl

def secondStates (first second : FinTM2) :
    second.σ × (first.σ × Register second) ≃ State first second where
  toFun st := ((st.2.1, st.1), st.2.2)
  invFun st := (st.1.2, (st.1.1, st.2))
  left_inv _ := rfl
  right_inv _ := rfl

def secondLabels (first second : FinTM2) :
    second.Λ ⊕ (Bool ⊕ first.Λ) → Label first second
  | .inl label => .inr (.inr label)
  | .inr (.inl bit) => .inr (.inl bit)
  | .inr (.inr label) => .inl label

def bridgeLabel (first second : FinTM2) (bit : Bool) : Label first second :=
  .inr (.inl bit)

def firstStatement (first second : FinTM2) (q : first.Stmt) :
    TM2.Stmt (Symbols first second) (Label first second) (State first second) :=
  MachineControl.statement id (firstStates first second)
    (MachineEmbedding.statement (some (bridgeLabel first second false)) q)

def secondStatement (first second : FinTM2) (q : second.Stmt) :
    TM2.Stmt (Symbols first second) (Label first second) (State first second) :=
  MachineControl.statement (secondLabels first second) (secondStates first second)
    (MachineStackSwap.statement
      (MachineEmbedding.statement
        (Δ := MachineEmbedding.Alphabet first.Γ (fun _ : Unit => second.Γ second.k₀))
        (Λextra := Bool ⊕ first.Λ) none q))

def program (first second : FinTM2)
    (relabel : first.Γ first.k₁ → second.Γ second.k₀)
    (fallback : second.Γ second.k₀) :
    Label first second → TM2.Stmt (Symbols first second) (Label first second)
      (State first second)
  | .inl label => firstStatement first second (first.m label)
  | .inr (.inr label) => secondStatement first second (second.m label)
  | .inr (.inl false) =>
      Reduction.MachineTransfer.loopAt (Γ := Symbols first second)
        (.inl first.k₁) (.inr (.inr ())) relabel fallback
        (bridgeLabel first second false) (some (bridgeLabel first second true))
  | .inr (.inl true) =>
      Reduction.MachineTransfer.loopAt (Γ := Symbols first second)
        (.inr (.inr ())) (.inr (.inl second.k₀)) id fallback
        (bridgeLabel first second true) (some (.inr (.inr second.main)))

def machine (first second : FinTM2)
    (relabel : first.Γ first.k₁ → second.Γ second.k₀)
    (fallback : second.Γ second.k₀) : FinTM2 where
  K := Tape first second
  kFin := by
    letI := first.kFin
    letI := second.kFin
    exact inferInstanceAs (Fintype (first.K ⊕ (second.K ⊕ Unit)))
  k₀ := .inl first.k₀
  k₁ := .inr (.inl second.k₁)
  Γ := Symbols first second
  Λ := Label first second
  ΛFin := by
    letI := first.ΛFin
    letI := second.ΛFin
    exact inferInstanceAs (Fintype (first.Λ ⊕ (Bool ⊕ second.Λ)))
  main := .inl first.main
  σ := State first second
  σFin := by
    letI := first.σFin
    letI := second.σFin
    letI := second.Γk₀Fin
    exact inferInstanceAs (Fintype ((first.σ × second.σ) × Option (second.Γ second.k₀)))
  initialState := ((first.initialState, second.initialState), none)
  Γk₀Fin := first.Γk₀Fin
  m := program first second relabel fallback

def firstConfiguration (first second : FinTM2) (c : first.Cfg) :
    TM2.Cfg (Symbols first second) (Label first second) (State first second) :=
  MachineControl.configuration id (firstStates first second)
    (MachineEmbedding.configuration (some (bridgeLabel first second false))
      (second.initialState, (none : Register second)) (fun _ => []) c)

def secondConfiguration (first second : FinTM2) (c : second.Cfg) :
    TM2.Cfg (Symbols first second) (Label first second) (State first second) :=
  MachineControl.configuration (secondLabels first second) (secondStates first second)
    (MachineStackSwap.configuration
      (MachineEmbedding.configuration
        (Δ := MachineEmbedding.Alphabet first.Γ (fun _ : Unit => second.Γ second.k₀))
        (Λextra := Bool ⊕ first.Λ) none
        (first.initialState, (none : Register second)) (fun _ => []) c))

theorem firstStep (first second : FinTM2)
    (relabel : first.Γ first.k₁ → second.Γ second.k₀)
    (fallback : second.Γ second.k₀) (a b : first.Cfg)
    (transition : first.step a = some b) :
    (machine first second relabel fallback).step (firstConfiguration first second a) =
      some (firstConfiguration first second b) := by
  cases a with
  | mk label state tapes =>
    cases label with
    | none => cases transition
    | some label =>
      have hb := Option.some.inj transition
      subst b
      change some (TM2.stepAux
        (MachineControl.statement id (firstStates first second)
          (MachineEmbedding.statement (some (bridgeLabel first second false)) (first.m label)))
        ((firstStates first second) (state, (second.initialState, none)))
        (MachineEmbedding.tapes tapes (fun _ => []))) = _
      have controlled := MachineControl.stepAux_simulation id (firstStates first second)
        (MachineEmbedding.statement
          (Δ := MachineEmbedding.Alphabet second.Γ (fun _ : Unit => second.Γ second.k₀))
          (some (bridgeLabel first second false)) (first.m label))
        (state, (second.initialState, none)) (MachineEmbedding.tapes tapes (fun _ => []))
      have embedded := MachineEmbedding.stepAux_simulation
        (Δ := MachineEmbedding.Alphabet second.Γ (fun _ : Unit => second.Γ second.k₀))
        (some (bridgeLabel first second false)) (second.initialState, (none : Register second))
        (fun _ => []) (first.m label) state tapes
      exact congrArg some (controlled.trans
        (congrArg (MachineControl.configuration id (firstStates first second)) embedded))

theorem secondStep (first second : FinTM2)
    (relabel : first.Γ first.k₁ → second.Γ second.k₀)
    (fallback : second.Γ second.k₀) (a b : second.Cfg)
    (transition : second.step a = some b) :
    (machine first second relabel fallback).step (secondConfiguration first second a) =
      some (secondConfiguration first second b) := by
  cases a with
  | mk label state tapes =>
    cases label with
    | none => cases transition
    | some label =>
      have hb := Option.some.inj transition
      subst b
      change some (TM2.stepAux
        (MachineControl.statement (secondLabels first second) (secondStates first second)
          (MachineStackSwap.statement
            (MachineEmbedding.statement
              (Δ := MachineEmbedding.Alphabet first.Γ (fun _ : Unit => second.Γ second.k₀))
              (Λextra := Bool ⊕ first.Λ) none (second.m label))))
        ((secondStates first second) (state, (first.initialState, none)))
        (MachineStackSwap.tapes (MachineEmbedding.tapes tapes (fun _ => [])))) = _
      rw [MachineControl.stepAux_simulation, MachineStackSwap.stepAux_simulation,
        MachineEmbedding.stepAux_simulation]
      rfl

theorem firstConfiguration_init (first second : FinTM2)
    (relabel : first.Γ first.k₁ → second.Γ second.k₀)
    (fallback : second.Γ second.k₀) (input : List (first.Γ first.k₀)) :
    firstConfiguration first second (initList first input) =
      initList (machine first second relabel fallback) input := by
  unfold firstConfiguration MachineControl.configuration MachineEmbedding.configuration initList
  congr 1
  funext k
  rcases k with k | k | k
  · by_cases h : k = first.k₀
    · subst k
      simp [machine, MachineEmbedding.tapes]
      rfl
    · simp [machine, MachineEmbedding.tapes, h]
  · simp [machine, MachineEmbedding.tapes]
  · simp [machine, MachineEmbedding.tapes]

theorem secondConfiguration_halt (first second : FinTM2)
    (relabel : first.Γ first.k₁ → second.Γ second.k₀)
    (fallback : second.Γ second.k₀) (output : List (second.Γ second.k₁)) :
    secondConfiguration first second (haltList second output) =
      haltList (machine first second relabel fallback) output := by
  unfold secondConfiguration MachineControl.configuration MachineStackSwap.configuration
    MachineEmbedding.configuration haltList
  congr 1
  funext k
  rcases k with k | k | k
  · simp [machine, MachineStackSwap.tapes, MachineEmbedding.tapes]
  · by_cases h : k = second.k₁
    · subst k
      simp [machine, MachineStackSwap.tapes, MachineEmbedding.tapes]
      rfl
    · simp [machine, MachineStackSwap.tapes, MachineEmbedding.tapes, h]
  · simp [machine, MachineStackSwap.tapes, MachineEmbedding.tapes]

def temporaryTapes (first second : FinTM2) (word : List (second.Γ second.k₀)) :
    ∀ k, List (Symbols first second k)
  | .inl _ => []
  | .inr (.inl _) => []
  | .inr (.inr _) => word

def temporaryConfiguration (first second : FinTM2) (word : List (second.Γ second.k₀)) :
    TM2.Cfg (Symbols first second) (Label first second) (State first second) :=
  ⟨some (bridgeLabel first second true),
    ((first.initialState, second.initialState), none), temporaryTapes first second word⟩

theorem firstTransfer_tapes (first second : FinTM2)
    (relabel : first.Γ first.k₁ → second.Γ second.k₀)
    (word : List (first.Γ first.k₁)) :
    Reduction.MachineTransfer.tapesAt (.inl first.k₁) (.inr (.inr ()))
      (firstConfiguration first second (haltList first word)).stk [] (word.reverse.map relabel) =
        temporaryTapes first second (word.reverse.map relabel) := by
  funext k
  rcases k with k | k | k
  · by_cases h : k = first.k₁
    · subst k
      simp [Reduction.MachineTransfer.tapesAt, temporaryTapes]
    · simp [Reduction.MachineTransfer.tapesAt, temporaryTapes, firstConfiguration,
        MachineControl.configuration, MachineEmbedding.configuration, MachineEmbedding.tapes,
        haltList, h]
  · simp [Reduction.MachineTransfer.tapesAt, temporaryTapes, firstConfiguration,
      MachineControl.configuration, MachineEmbedding.configuration, MachineEmbedding.tapes]
  · cases k
    simp [Reduction.MachineTransfer.tapesAt, temporaryTapes]

theorem secondTransfer_tapes (first second : FinTM2) (word : List (second.Γ second.k₀)) :
    Reduction.MachineTransfer.tapesAt (Γ := Symbols first second)
      (.inr (.inr ())) (.inr (.inl second.k₀))
      (temporaryTapes first second word) [] word.reverse =
        (secondConfiguration first second (initList second word.reverse)).stk := by
  funext k
  rcases k with k | k | k
  · simp [Reduction.MachineTransfer.tapesAt, temporaryTapes, secondConfiguration,
      MachineControl.configuration, MachineStackSwap.configuration, MachineStackSwap.tapes,
      MachineEmbedding.configuration, MachineEmbedding.tapes]
  · by_cases h : k = second.k₀
    · subst k
      simp [Reduction.MachineTransfer.tapesAt, secondConfiguration,
        MachineControl.configuration, MachineStackSwap.configuration, MachineStackSwap.tapes,
        MachineEmbedding.configuration, MachineEmbedding.tapes, initList]
    · simp [Reduction.MachineTransfer.tapesAt, temporaryTapes, secondConfiguration,
        MachineControl.configuration, MachineStackSwap.configuration, MachineStackSwap.tapes,
        MachineEmbedding.configuration, MachineEmbedding.tapes, initList, h]
  · cases k
    simp [Reduction.MachineTransfer.tapesAt, secondConfiguration,
      MachineControl.configuration, MachineStackSwap.configuration, MachineStackSwap.tapes,
      MachineEmbedding.configuration, MachineEmbedding.tapes]

def firstTransfer (first second : FinTM2)
    (relabel : first.Γ first.k₁ → second.Γ second.k₀)
    (fallback : second.Γ second.k₀) (word : List (first.Γ first.k₁)) :
    StateTransition.EvalsToInTime (machine first second relabel fallback).step
      (firstConfiguration first second (haltList first word))
      (some (temporaryConfiguration first second (word.reverse.map relabel)))
      (word.length + 1) := by
  let run := Reduction.MachineTransfer.transferAtInTime
    (.inl first.k₁ : Tape first second) (.inr (.inr ())) (by intro h; cases h)
    relabel fallback (bridgeLabel first second false)
    (some (bridgeLabel first second true)) (program first second relabel fallback) rfl
    (firstConfiguration first second (haltList first word)).stk
    (first.initialState, second.initialState) none
  have inputTape : (firstConfiguration first second (haltList first word)).stk (.inl first.k₁) =
      word := by simp [firstConfiguration, MachineControl.configuration,
        MachineEmbedding.configuration, MachineEmbedding.tapes, haltList]
  have outputTape :
      (firstConfiguration first second (haltList first word)).stk (.inr (.inr ())) = [] := rfl
  rw [inputTape, outputTape, List.append_nil, firstTransfer_tapes] at run
  exact run

def secondTransfer (first second : FinTM2)
    (relabel : first.Γ first.k₁ → second.Γ second.k₀)
    (fallback : second.Γ second.k₀) (word : List (second.Γ second.k₀)) :
    StateTransition.EvalsToInTime (machine first second relabel fallback).step
      (temporaryConfiguration first second word)
      (some (secondConfiguration first second (initList second word.reverse)))
      (word.length + 1) := by
  let run := Reduction.MachineTransfer.transferAtInTime
    (.inr (.inr ()) : Tape first second) (.inr (.inl second.k₀)) (by intro h; cases h)
    id fallback (bridgeLabel first second true) (some (.inr (.inr second.main)))
    (program first second relabel fallback) rfl (temporaryTapes first second word)
    (first.initialState, second.initialState) none
  simp only [temporaryTapes, List.map_id, List.append_nil] at run
  rw [secondTransfer_tapes] at run
  exact run

def execute (first second : FinTM2)
    (relabel : first.Γ first.k₁ → second.Γ second.k₀)
    (fallback : second.Γ second.k₀)
    (input : List (first.Γ first.k₀)) (middle : List (first.Γ first.k₁))
    (output : List (second.Γ second.k₁)) (firstBudget secondBudget : Nat)
    (runFirst : TM2OutputsInTime first input (some middle) firstBudget)
    (runSecond : TM2OutputsInTime second (middle.map relabel) (some output) secondBudget) :
    TM2OutputsInTime (machine first second relabel fallback) input (some output)
      (firstBudget + 2 * (middle.length + 1) + secondBudget) := by
  let start := MachineComposition.liftExecutionInTime first.step
    (machine first second relabel fallback).step (firstConfiguration first second)
    (firstStep first second relabel fallback) runFirst
  let bridge₁ := firstTransfer first second relabel fallback middle
  have bridge₂ := secondTransfer first second relabel fallback (middle.reverse.map relabel)
  have reversal : (middle.reverse.map relabel).reverse = middle.map relabel := by
    simp only [List.map_reverse, List.reverse_reverse]
  rw [reversal] at bridge₂
  simp only [List.length_map, List.length_reverse] at bridge₂
  let finish := MachineComposition.liftExecutionInTime second.step
    (machine first second relabel fallback).step (secondConfiguration first second)
    (secondStep first second relabel fallback) runSecond
  let phase₁₂ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ start bridge₁
  let phase₁₂₃ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ phase₁₂ bridge₂
  have full := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ phase₁₂₃ finish
  rw [firstConfiguration_init, secondConfiguration_halt] at full
  exact {
    toEvalsTo := full.toEvalsTo
    steps_le_m := by have h := full.steps_le_m; omega
  }

noncomputable def compose {α β γ αΓ βΓ γΓ : Type}
    {ea : α → List αΓ} {eb : β → List βΓ} {ec : γ → List γΓ}
    {f : α → β} {g : β → γ}
    (first : TM2ComputableInPolyTime ea eb f)
    (second : TM2ComputableInPolyTime eb ec g) (fallback : βΓ) :
    TM2ComputableInPolyTime ea ec (fun a => g (f a)) := by
  let relabel : first.tm.Γ first.tm.k₁ → second.tm.Γ second.tm.k₀ :=
    fun symbol => second.inputAlphabet.symm (first.outputAlphabet symbol)
  let defaultSymbol := second.inputAlphabet.symm fallback
  let intermediate : Polynomial Nat := Polynomial.X +
    Polynomial.C (Runtime.programPushBound first.tm) * first.time
  refine {
    tm := machine first.tm second.tm relabel defaultSymbol
    inputAlphabet := first.inputAlphabet
    outputAlphabet := second.outputAlphabet
    time := MachineComposition.compositionPolynomial first.time second.time intermediate
    outputsFun := ?_
  }
  intro a
  let input := (ea a).map first.inputAlphabet.invFun
  let middle := (eb (f a)).map first.outputAlphabet.invFun
  let output := (ec (g (f a))).map second.outputAlphabet.invFun
  have handoff : middle.map relabel = (eb (f a)).map second.inputAlphabet.invFun := by
    dsimp only [middle, relabel]
    simp only [List.map_map]
    apply List.map_congr_left
    intro symbol _
    exact congrArg second.inputAlphabet.symm (first.outputAlphabet.apply_symm_apply symbol)
  have runSecond : TM2OutputsInTime second.tm (middle.map relabel) (some output)
      (second.time.eval (eb (f a)).length) := by
    rw [handoff]
    exact second.outputsFun (f a)
  have full := execute first.tm second.tm relabel defaultSymbol input middle output
    (first.time.eval (ea a).length) (second.time.eval (eb (f a)).length)
    (first.outputsFun a) runSecond
  have intermediateBound : (eb (f a)).length ≤ intermediate.eval (ea a).length :=
    Runtime.encodedOutputLength first a
  have totalBound := MachineComposition.compositionBudget_le first.time second.time
    intermediate (ea a).length (eb (f a)).length intermediateBound
  have middleLength : middle.length = (eb (f a)).length := by simp only [middle, List.length_map]
  exact {
    toEvalsTo := full.toEvalsTo
    steps_le_m := by
      apply Nat.le_trans full.steps_le_m
      simpa only [middleLength] using totalBound
  }

noncomputable def composeBits {α β γ : Type}
    {ea : α → List Bool} {eb : β → List Bool} {ec : γ → List Bool}
    {f : α → β} {g : β → γ}
    (first : TM2ComputableInPolyTime ea eb f)
    (second : TM2ComputableInPolyTime eb ec g) :
    TM2ComputableInPolyTime ea ec (fun a => g (f a)) :=
  compose first second false

end MinUncutGames.Foundations.Complexity.MachineSequential

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_TM2Composition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial-time composition uses concrete finite TM2
compiler. It lifts the heterogeneous machine programs and performs a two-pass
stack transfer with a proved linear intermediate-word cost. -/

namespace ContinuumCoulomb.TM2Composition
open Turing

/-- Actual polynomial-time composition, with the intermediate length bound
proved from the first machine's execution rather than postulated. -/
noncomputable def computable {α β γ : Type}
    {ea : α → List Bool} {eb : β → List Bool} {ec : γ → List Bool}
    {f : α → β} {g : β → γ}
    (hf : TM2ComputableInPolyTime ea eb f) (hg : TM2ComputableInPolyTime eb ec g) :
    TM2ComputableInPolyTime ea ec (g ∘ f) :=
  MinUncutGames.Foundations.Complexity.MachineSequential.composeBits (f := f) (g := g) hf hg

end ContinuumCoulomb.TM2Composition

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_HardnessComposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Promise-hardness transport through actual polynomial-time machine
composition, with both yes and no promise maps retained. -/

noncomputable section
namespace ContinuumCoulomb
open BinaryEncoding

def PolynomialManyOne.comp {α β γ : Type}
    {ea : α → BitString} {eb : β → BitString} {ec : γ → BitString}
    {P : PromiseProblem α} {Q : PromiseProblem β} {R : PromiseProblem γ}
    (F : PolynomialManyOne ea eb P Q) (G : PolynomialManyOne eb ec Q R) :
    PolynomialManyOne ea ec P R where
  map := G.map ∘ F.map
  polynomialTime := TM2Composition.computable (f := F.map) (g := G.map) F.polynomialTime G.polynomialTime
  maps_yes x hx := G.maps_yes (F.map x) (F.maps_yes x hx)
  maps_no x hx := G.maps_no (F.map x) (F.maps_no x hx)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_UnitBinaryProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal polynomial-time inclusion of unit-charge Coulomb instances
into the binary-charge promise. The machine parses the position list,
attaches charge one to each position and preserves the entire encoded
electron/threshold tail. -/

namespace ContinuumCoulomb.UnitBinaryProgram
open ExactQuantumFactoring.BitStackProgram

abbrev tailCodec := BinaryEncoding.pair BinaryEncoding.unary SourcePrograms.thresholdCodec

def zeroPosition : BinaryPosition := ⟨⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩⟩

end ContinuumCoulomb.UnitBinaryProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_MediatorListCorrectness
attribute [-simp] _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete TM2 bond lists are exactly the enumerations of the finite
spin matrices whose three-stage bottom-energy estimates were proved. -/

namespace ContinuumCoulomb.MediatorIteration
open MediatorGraph

abbrev Bond := MediatorListProgram.Bond

def Bonds.toList {n r : ℕ} (F : Bonds n r) : List Bond :=
  List.ofFn (fun e => ((F.left e).val, (F.right e).val, F.weight e))

@[simp] theorem Bonds.toList_length {n r : ℕ} (F : Bonds n r) : F.toList.length = r := by
  simp only [Bonds.toList, List.length_ofFn]

theorem old_val (n r : ℕ) (i : Fin n) : (old n r i).val = i.val := rfl

theorem fresh_val (n r : ℕ) (e : Fin r) (s : Fin 2) :
    (fresh n r e s).val = n + 2 * e.val + s.val := by
  change n + (s.val + 2 * e.val) = _
  omega

end ContinuumCoulomb.MediatorIteration

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_MediatorUnaryPrimitives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual unary arithmetic, projections, and a small repeated-doubling
program for the fixed mediator scale constant. -/

namespace ContinuumCoulomb.MediatorUnaryProgram
open ExactQuantumFactoring.BitStackProgram MediatorListProgram

theorem delta_as_mul (r W G : ℕ) :
    MediatorParameters.scale r W G * MediatorParameters.scale r W G = MediatorParameters.delta r W G := by
  unfold MediatorParameters.delta
  rw [pow_two]

end ContinuumCoulomb.MediatorUnaryProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_MediatorUnarySecond
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual second-stage unary coefficient and vertex metadata. -/

namespace ContinuumCoulomb.MediatorUnaryProgram
open ExactQuantumFactoring.BitStackProgram MediatorListProgram

def secondEnv (x : Env) : Env :=
  (2 * x.1, MediatorParameters.secondWeight x.1 x.2.1 x.2.2.1, x.2.2.1, x.2.2.2 + 2 * x.1)

end ContinuumCoulomb.MediatorUnaryProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_MediatorUnaryThird
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual third-stage unary coefficient and vertex metadata. Separate
opaque arithmetic nodes prevent expansion of the finite program text. -/

namespace ContinuumCoulomb.MediatorUnaryProgram
open ExactQuantumFactoring.BitStackProgram MediatorListProgram

theorem deltaFn_apply (r W G N : ℕ) :
    (fun x : Env => MediatorParameters.delta x.1 x.2.1 x.2.2.1) (r, W, G, N) =
      MediatorParameters.delta r W G := rfl
theorem spokeFn_apply (r W G N : ℕ) :
    (fun x : Env => 2 * MediatorParameters.scale x.1 x.2.1 x.2.2.1 * x.2.1) (r, W, G, N) =
      2 * MediatorParameters.scale r W G * W := rfl

def thirdEnv (x : Env) : Env :=
  (6 * x.1, MediatorParameters.thirdWeight x.1 x.2.1 x.2.2.1, x.2.2.1, x.2.2.2 + 6 * x.1)

end ContinuumCoulomb.MediatorUnaryProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_RationalSumProgram
attribute [-simp] _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
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

abbrev State := ℤ × ℕ

def step (s : State) (q : ℚ) : State :=
  (s.1 * q.den + q.num * s.2, s.2 * q.den)

def value (s : State) : ℚ := (s.1 : ℚ) / s.2

theorem step_den_pos (s : State) (q : ℚ) (hs : 0 < s.2) : 0 < (step s q).2 :=
  Nat.mul_pos hs q.pos

theorem step_value (s : State) (q : ℚ) (hs : 0 < s.2) : value (step s q) = value s + q := by
  have hd : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
  have hs' : (s.2 : ℚ) ≠ 0 := by exact_mod_cast hs.ne'
  unfold step value
  push_cast
  conv_rhs => rw [← Rat.num_div_den q]
  field_simp

theorem fold_value (xs : List ℚ) (s : State) (hs : 0 < s.2) :
    value (xs.foldl step s) = value s + xs.sum := by
  induction xs generalizing s with
  | nil => simp
  | cons q xs ih =>
    rw [List.foldl_cons, ih _ (step_den_pos s q hs), step_value s q hs, List.sum_cons]
    ring

end ContinuumCoulomb.RationalSumProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_MediatorOffsetProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact rational threshold offsets for the fully computed mediator
construction, using actual gcd-based rational-list summation. -/

namespace ContinuumCoulomb.MediatorOffsetProgram
open ExactQuantumFactoring.BitStackProgram MediatorListProgram

def stageOffset (x : Input) : ℚ :=
  3 * x.1.1 * MediatorParameters.delta x.1.1 x.1.2.1 x.1.2.2.1 +
    3 * (x.2.map (fun e => |e.2.2|)).sum

end ContinuumCoulomb.MediatorOffsetProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_MediatorFullListCorrectness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact list semantics for all three computed mediator stages and their
rational scalar offset. The emitted list is the full finite spin graph. -/

namespace ContinuumCoulomb.MediatorIteration
open MediatorListProgram MediatorUnaryProgram
open scoped BigOperators

def literalInput {n r : ℕ} (F : Bonds n r) (W G : ℕ) : Input := ((r, W, G, n), F.toList)

end ContinuumCoulomb.MediatorIteration

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceNormalizationCorrectness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The machine-normalized source registers are the literal bond family
whose complete positive-spin spectral and promise estimates were proved. -/

namespace ContinuumCoulomb.SourceMetadataProgram
open MediatorListProgram

def roundingDenominator (k : ℕ) (d : BinaryHeisenberg) : ℕ :=
  SourceNormalizedSpectrum.denominator d.edges.length (size d ^ k)

end ContinuumCoulomb.SourceMetadataProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_SourcePositiveProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete literal source-to-positive-spin program. It parses the
original source, computes the fixed polynomial metadata, rounds and deletes
zero coefficients, emits all three graph stages, and shifts both thresholds. -/

namespace ContinuumCoulomb.SourcePositiveProgram
open ExactQuantumFactoring.BitStackProgram MediatorListProgram

structure Registers where
  coordinate : List SourcePrograms.Coordinate
  vertices : ℕ
  bound : ℕ
  gapScale : ℕ
  bonds : List Bond
  offset : ℚ
  lower : ℚ
  upper : ℚ

def normalized (k : ℕ) (d : BinaryHeisenberg) : Input :=
  SourceNormalizationProgram.normalized (SourceMetadataProgram.input k d)

def error (k : ℕ) (d : BinaryHeisenberg) : ℚ :=
  1 / (128 * ((SourceMetadataProgram.size d ^ k : ℕ) : ℚ))

end ContinuumCoulomb.SourcePositiveProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourcePositiveCorrectness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact semantics of the computed positive-spin source reduction: the
literal output has the full three-stage matrix and the proved rational
thresholds, including the common coefficient-rounding error. -/

noncomputable section
namespace ContinuumCoulomb.SourcePositiveProgram
open MediatorIteration SourceMetadataProgram

abbrev sourceBound (k : ℕ) (d : BinaryHeisenberg) :=
  roundingDenominator k d + size d ^ k + 1

end ContinuumCoulomb.SourcePositiveProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_FiniteSourceBranch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The decidable one-spin branch completed using arbitrary fixed YES and NO
instances, so that no atomic spectral formula is required. -/

noncomputable section
namespace ContinuumCoulomb.FiniteSourceBranch
open ExactQuantumFactoring.BitStackProgram

def value (y z : UnitCoulomb) (f : BinaryHeisenberg → UnitCoulomb)
    (d : BinaryHeisenberg) : UnitCoulomb :=
  if d.coordinate.length ≤ 1 then (if d.lower.value < 0 then z else y) else f d

end ContinuumCoulomb.FiniteSourceBranch

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_FockCoefficientNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coefficient perturbations of the actual one- and two-body CAR
operators. The bounds depend polynomially on the number of modes and
not on the exponentially large dimension of the exterior algebra. -/

noncomputable section
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock
open scoped BigOperators

variable {Q : ℕ}

def oneBodyOperator (K : Fin (Q + 1) → Fin (Q + 1) → ℂ) : Module.End ℂ (Space Q) :=
  ∑ i, ∑ j, K i j • transfer i j

def twoBodyOperator (W : Fin (Q + 1) → Fin (Q + 1) → Fin (Q + 1) → Fin (Q + 1) → ℂ) :
    Module.End ℂ (Space Q) :=
  (2 : ℂ)⁻¹ • ∑ i, ∑ j, ∑ k, ∑ l,
    W i j k l • (create i * create j * annihilate l * annihilate k)

end ContinuumCoulomb.HubbardGlobal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_FockChargePolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The density interaction and its counterterm on the full half-filled
Fock sector, including the scalar off-site Coulomb shift. -/

noncomputable section
open scoped BigOperators Classical
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock

def directChargeValue {m : ℕ} (U : ℝ) (V : Fin m → Fin m → ℝ)
    (o : Fin m → Fin 3) : ℝ :=
  U / 2 * (∑ i, ((o i : ℕ) : ℝ) * (((o i : ℕ) : ℝ) - 1)) +
    (1 / 2 : ℝ) * (∑ i, ∑ j, V i j * ((o i : ℕ) : ℝ) * ((o j : ℕ) : ℝ)) -
    (∑ i, (∑ j, V i j) * ((o i : ℕ) : ℝ))

def siteChargeOperator (m : ℕ) (U : ℝ) (V : Fin (m+1) → Fin (m+1) → ℝ) :
    Module.End ℂ (Space (2*m+1)) :=
  ((U / 2 : ℝ) : ℂ) • (∑ i, (siteNumber m i * siteNumber m i - siteNumber m i)) +
    (1 / 2 : ℂ) • (∑ i, ∑ j, (V i j : ℂ) • (siteNumber m i * siteNumber m j)) -
    ∑ i, ((∑ j, V i j : ℝ) : ℂ) • siteNumber m i

def modeSite (m : ℕ) (a : Fin ((2*m+1)+1)) : Fin (m+1) :=
  ((siteModes m).symm a).1

def siteCoulombCoefficient {m : ℕ} (U : ℝ) (V : Fin m → Fin m → ℝ)
    (i j : Fin m) : ℂ := if i=j then (U:ℂ) else (V i j:ℂ)

end ContinuumCoulomb.HubbardGlobal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_FockSiteOneBody
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The spatial one-body matrix acts on both conserved spin modes and
agrees with the actual graph hopping operator. -/

noncomputable section
open scoped BigOperators Classical
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock

def spinLift (m : ℕ) (K : Fin (m+1) → Fin (m+1) → ℂ)
    (a b : Fin ((2*m+1)+1)) : ℂ :=
  if ((siteModes m).symm a).2 = ((siteModes m).symm b).2 then
    K (modeSite m a) (modeSite m b) else 0

def siteBilinear (m : ℕ) (i j : Fin (m+1)) : Module.End ℂ (Space (2*m+1)) :=
  transfer (siteMode m i 0) (siteMode m j 0) +
    transfer (siteMode m i 1) (siteMode m j 1)

def siteOneBody (m : ℕ) (K : Fin (m+1) → Fin (m+1) → ℂ) :
    Module.End ℂ (Space (2*m+1)) := ∑ i, ∑ j, K i j • siteBilinear m i j

def graphHoppingMatrix {Edge : Type*} [Fintype Edge] (m : ℕ)
    (left right : Edge → Fin (m+1)) (t : Edge → ℂ) (i j : Fin (m+1)) : ℂ :=
  ∑ e, ((if i=left e ∧ j=right e then t e else 0) +
    (if i=right e ∧ j=left e then t e else 0))

end ContinuumCoulomb.HubbardGlobal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ClassicalH1
attribute [-simp] _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! C1 functions with square-integrable classical partials belong to the
actual weak H1 domain. Only the test function needs compact support; this
allows the decaying manufactured orbitals and their finite Slater sums. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem complex_C1_test_ibp {n : ℕ} (f : Configuration n → ℂ) (hf : ContDiff ℝ 1 f)
    (φ : Configuration n → ℝ) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (v : Configuration n) :
    (∫ x, f x * (fderiv ℝ φ x v : ℂ)) = -(∫ x, fderiv ℝ f x v * (φ x : ℂ)) := by
  let g : Configuration n → ℂ := fun x => (φ x : ℂ)
  have hg : ContDiff ℝ 1 g := Complex.ofRealCLM.contDiff.comp hφ
  have hgc : HasCompactSupport g := hc.comp_left Complex.ofReal_zero
  have hd (x : Configuration n) : fderiv ℝ g x v = (fderiv ℝ φ x v : ℂ) :=
    congrArg (fun L : Configuration n →L[ℝ] ℂ => L v)
      ((Complex.ofRealCLM.hasFDerivAt.comp x (hφ.differentiable (by norm_num) x).hasFDerivAt).fderiv)
  have hf' : Continuous (fun x => fderiv ℝ f x v) :=
    (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hg' : Continuous (fun x => fderiv ℝ g x v) :=
    (hg.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hi1 : Integrable (fun x => fderiv ℝ f x v * g x) :=
    (hf'.mul hg.continuous).integrable_of_hasCompactSupport hgc.mul_left
  have hi2 : Integrable (fun x => f x * fderiv ℝ g x v) :=
    (hf.continuous.mul hg').integrable_of_hasCompactSupport (hgc.fderiv_apply ℝ v).mul_left
  have hi3 : Integrable (fun x => f x * g x) :=
    (hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport hgc.mul_left
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hi1 hi2 hi3
    (fun x _ => hf.differentiable (by norm_num) x) (fun x _ => hg.differentiable (by norm_num) x)
  simpa only [hd] using h

def classicalH1State {n : ℕ} (f : SpinConfiguration n → Configuration n → ℂ)
    (hf : ∀ s, ContDiff ℝ 1 (f s)) (hL2 : ∀ s, MemLp (f s) 2)
    (hpartial : ∀ s a, MemLp (fun x => fderiv ℝ (f s) x (EuclideanSpace.single a 1)) 2) :
    Coulomb.H1Vector n where
  value := f
  gradient s a x := fderiv ℝ (f s) x (EuclideanSpace.single a 1)
  value_L2 := hL2
  partial_L2 := hpartial
  weak_partial s a φ hφ hc := complex_C1_test_ibp (f s) (hf s) φ (hφ.of_le (by first | simp | exact_mod_cast le_top)) hc _

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.Laughlin_Model
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin
open scoped BigOperators

abbrev Configuration (N Q : ℕ) := Fin N → Fin (Q+1)
abbrev State (N Q : ℕ) := Configuration N Q → ℂ

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ092_CC.Laughlin_Exterior_OccupationDiagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

noncomputable def occupationBasis (Q : ℕ) :
    Module.Basis (Finset (Fin (Q+1))) ℂ (Space Q) :=
  (Pi.basisFun ℂ (Fin (Q+1))).ExteriorAlgebra

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_FockHubbardForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact identification of the compressed Coulomb CAR Hamiltonian
with the full half-filled Hubbard variational problem. -/

noncomputable section
open scoped BigOperators Classical InnerProductSpace
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock

variable {Edge : Type*} [Fintype Edge]

def hubbardOneBodyMatrix (m : ℕ) (V : Fin (m+1) → Fin (m+1) → ℝ)
    (left right : Edge → Fin (m+1)) (t : Edge → ℝ) :
    Fin ((2*m+1)+1) → Fin ((2*m+1)+1) → ℂ :=
  spinLift m (fun i j => graphHoppingMatrix m left right (fun e => (t e:ℂ)) i j -
    if i=j then ((∑ k, V i k : ℝ):ℂ) else 0)

def hubbardCoulombTensor (m : ℕ) (U : ℝ) (V : Fin (m+1) → Fin (m+1) → ℝ)
    (a b c d : Fin ((2*m+1)+1)) : ℂ :=
  if a=c ∧ b=d then siteCoulombCoefficient U V (modeSite m a) (modeSite m b) else 0

end ContinuumCoulomb.HubbardGlobal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_SlaterOccupation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual normalized Slater waves for the sorted occupied subsets of
finitely many orthonormal spin orbitals form an orthonormal family. Their
finite linear combination map is a genuine L2 isometry. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb.SlaterOccupation
open Coulomb

abbrev Occupied (Q n : ℕ) := Set.powersetCard (Fin (Q + 1)) n

def selection {Q n : ℕ} (S : Occupied Q n) : Fin n ↪o Fin (Q + 1) :=
  Set.powersetCard.ofFinEmbEquiv.symm S

end ContinuumCoulomb.SlaterOccupation

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_FockSlaterTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalized determinant of finite Kronecker orbitals is the actual
antisymmetric coefficient tensor of an occupation basis vector. Substitution
of physical orbitals gives exactly the continuum Slater wave, also for every
complex superposition of occupations. -/

noncomputable section
namespace ContinuumCoulomb.FockSlaterTensor
open Laughlin Laughlin.Fock SlaterOccupation Coulomb
open scoped BigOperators

def basisTensor {Q n : ℕ} (S : Occupied Q n) : State n Q :=
  slaterWave (fun i j => if selection S i = j then 1 else 0)

def tensorValue {A : Type*} {Q n : ℕ} (v : Fin (Q + 1) → A → ℂ)
    (ψ : State n Q) (x : Fin n → A) : ℂ :=
  ∑ a : Laughlin.Configuration n Q, ψ a * ∏ i, v (a i) (x i)

def occupationTensor {Q n : ℕ} (c : EuclideanSpace ℂ (Occupied Q n)) : State n Q :=
  fun a => ∑ S, c S * basisTensor S a

end ContinuumCoulomb.FockSlaterTensor

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_FockTwoBodyContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two occupied-coordinate contraction, with the signs obtained from
the actual antisymmetric coefficient tensor. -/

noncomputable section
open scoped BigOperators Classical
namespace ContinuumCoulomb.FockTwoBodyContraction
open Laughlin

def pairInsert {n Q : ℕ} (i : Fin (n+2)) (j : Fin (n+1)) (a b : Fin (Q+1))
    (c : Laughlin.Configuration n Q) : Laughlin.Configuration (n+2) Q :=
  i.insertNth a (j.insertNth b c)

end ContinuumCoulomb.FockTwoBodyContraction

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_Packets_ComplexWindow
attribute [-simp] _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
namespace Coulomb
noncomputable def complexWindow (g : 𝓢(Space,ℝ)) : 𝓢(Space,ℂ) :=
  g.postcompCLM Complex.ofRealCLM
@[simp] lemma complexWindow_apply (g : 𝓢(Space,ℝ)) (x : Space) :
    complexWindow g x = (g x : ℂ) := rfl

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_VerticalEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalized Gaussian actually attains transverse oscillator energy
`freq/2`, by the differential equation and integrable integration by parts. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def verticalForm (freq : ℝ) (u : ℝ → ℝ) : ℝ :=
  (1 / 2 : ℝ) * (∫ z, deriv u z ^ 2) +
    (freq ^ 2 / 2) * (∫ z, z ^ 2 * u z ^ 2)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CoulombPackets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The global Coulomb pairing for the bounded integrable packets used in
the mode construction. Existing Gaussian-kernel positivity applies directly
once the elementary bounded-density estimate supplies joint integrability. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

structure CoulombPacket where
  value : Position → ℝ
  continuous : Continuous value
  integrable : Integrable value
  bound : ℝ
  bound_nonnegative : 0 ≤ bound
  bound_spec : ∀ x, ‖value x‖ ≤ bound

namespace CoulombPacket

instance instCoeFunForallPositionReal : CoeFun CoulombPacket (fun _ => Position → ℝ) := ⟨CoulombPacket.value⟩

def add (f g : CoulombPacket) : CoulombPacket where
  value x := f x + g x
  continuous := f.continuous.add g.continuous
  integrable := f.integrable.add g.integrable
  bound := f.bound + g.bound
  bound_nonnegative := add_nonneg f.bound_nonnegative g.bound_nonnegative
  bound_spec x := (norm_add_le _ _).trans (add_le_add (f.bound_spec x) (g.bound_spec x))

def smul (t : ℝ) (f : CoulombPacket) : CoulombPacket where
  value x := t * f x
  continuous := continuous_const.mul f.continuous
  integrable := f.integrable.const_mul t
  bound := ‖t‖ * f.bound
  bound_nonnegative := mul_nonneg (norm_nonneg t) f.bound_nonnegative
  bound_spec x := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (f.bound_spec x) (norm_nonneg t)

def pair (f g : CoulombPacket) : ℝ :=
  ∫ p : Position × Position, f p.1 * g p.2 * Coulomb.coulombKernel (p.1 - p.2)

end CoulombPacket
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_GramCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative symmetric orthonormalization of a finite real Gram matrix.
The correction is the actual spectral inverse square root, with Euclidean
operator norm estimates independent of the ambient function space. -/

noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace ContinuumCoulomb.GramCorrection

variable {m : ℕ} {G : Matrix (Fin m) (Fin m) ℝ}

def correction (hG : G.IsHermitian) : Matrix (Fin m) (Fin m) ℝ :=
  hG.cfc (fun x => (Real.sqrt x)⁻¹)

end ContinuumCoulomb.GramCorrection

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_MediatorSimple
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fresh mediator pairs give a simple unordered edge enumeration. This
supplies the cross-edge cancellation hypothesis in the global Hubbard model. -/

namespace ContinuumCoulomb.MediatorIteration
open MediatorGraph

def edgeMatches {α : Type*} (a b c d : α) : Prop :=
  (a = c ∧ b = d) ∨ (a = d ∧ b = c)

def Bonds.Simple {n r : ℕ} (F : Bonds n r) : Prop :=
  ∀ e f, edgeMatches (F.left e) (F.right e) (F.left f) (F.right f) → e = f

end ContinuumCoulomb.MediatorIteration

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_OccupationFock
attribute [-simp] _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual n-particle exterior sector is exactly the Euclidean space
of amplitudes on n-element occupied subsets, with no omitted states. -/

noncomputable section
namespace ContinuumCoulomb.OccupationFock
open Laughlin.Fock SlaterOccupation HubbardGlobal
open scoped BigOperators

variable {Q n : ℕ}

def vector (c : EuclideanSpace ℂ (Occupied Q n)) : Space Q :=
  ∑ S, c S • occupationBasis Q S.val

lemma coordinates_basis (A : Finset (Fin (Q + 1))) :
    fockCoordinates Q (occupationBasis Q A) = EuclideanSpace.single A 1 := by
  classical
  have hb : occupationBasis Q = fockBasis Q := rfl
  rw [hb]
  ext B
  simp only [fockCoordinates_apply, Module.Basis.repr_self, Finsupp.single_apply,
    PiLp.single_apply]
  split_ifs <;> simp_all

lemma vector_coordinates (c : EuclideanSpace ℂ (Occupied Q n)) :
    fockCoordinates Q (vector c) = coordinateInclusion (fun S : Occupied Q n => S.val) c := by
  unfold vector
  rw [map_sum]
  simp_rw [map_smul, coordinates_basis]
  simp only [coordinateInclusion, coordinateInclusionLinear, LinearMap.coe_toContinuousLinearMap',
    LinearMap.coe_mk, AddHom.coe_mk]
  ext A
  simp [Pi.single_apply]

lemma vector_support (c : EuclideanSpace ℂ (Occupied Q n))
    (A : Finset (Fin (Q + 1))) (hA : A.card ≠ n) : (fockBasis Q).repr (vector c) A = 0 := by
  rw [← fockCoordinates_apply, vector_coordinates]
  apply coordinateInclusion_apply_outside _ c A
  intro S he
  apply hA
  rw [← he]
  exact S.property

lemma exists_vector_of_support (x : Space Q)
    (hx : ∀ A : Finset (Fin (Q + 1)), A.card ≠ n → (fockBasis Q).repr x A = 0) :
    ∃ c : EuclideanSpace ℂ (Occupied Q n), vector c = x := by
  let c : EuclideanSpace ℂ (Occupied Q n) :=
    WithLp.toLp 2 (fun S : Occupied Q n => (fockBasis Q).repr x S.val)
  refine ⟨c, ?_⟩
  apply (fockCoordinates Q).injective
  rw [vector_coordinates]
  ext A
  by_cases hA : A.card = n
  · exact coordinateInclusion_apply_image _ Subtype.val_injective c ⟨A, hA⟩
  · rw [coordinateInclusion_apply_outside _ c A (by
      intro S he
      apply hA
      rw [← he]
      exact S.property)]
    exact (hx A hA).symm

end ContinuumCoulomb.OccupationFock

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_OccupationSector
attribute [-simp] _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The occupation-amplitude map is a linear equivalence onto the entire
fixed-particle exterior sector, preserving its actual occupation inner
product. No state in that sector is excluded. -/

noncomputable section
namespace ContinuumCoulomb.OccupationFock
open Laughlin.Fock SlaterOccupation HubbardGlobal
open scoped BigOperators InnerProductSpace

variable {Q n : ℕ}

def coordinateIsometry (Q n : ℕ) :
    EuclideanSpace ℂ (Occupied Q n) →ₗᵢ[ℂ] FockCoordinateSpace Q where
  toLinearMap := (coordinateInclusion (fun S : Occupied Q n => S.val)).toLinearMap
  norm_map' := coordinateInclusion_norm_map _ Subtype.val_injective

lemma vector_injective : Function.Injective (vector (Q := Q) (n := n)) := by
  intro c d h
  have hc := congrArg (fockCoordinates Q) h
  rw [vector_coordinates, vector_coordinates] at hc
  exact (coordinateIsometry Q n).injective hc

def particleSector (Q n : ℕ) : Submodule ℂ (Space Q) where
  carrier := {x | ∀ A : Finset (Fin (Q + 1)), A.card ≠ n → (fockBasis Q).repr x A = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy A hA
    simp only [map_add, Finsupp.add_apply, hx A hA, hy A hA, add_zero]
  smul_mem' := by
    intro c x hx A hA
    simp only [map_smul, Finsupp.smul_apply, hx A hA, smul_zero]

def synthesisLinear (Q n : ℕ) : EuclideanSpace ℂ (Occupied Q n) →ₗ[ℂ] Space Q where
  toFun := vector
  map_add' c d := by simp [vector, add_smul, Finset.sum_add_distrib]
  map_smul' c d := by simp [vector, smul_smul, Finset.smul_sum]

def sectorSynthesis (Q n : ℕ) :
    EuclideanSpace ℂ (Occupied Q n) →ₗ[ℂ] particleSector Q n :=
  (synthesisLinear Q n).codRestrict (particleSector Q n) (fun c => vector_support c)

def sectorEquiv (Q n : ℕ) :
    EuclideanSpace ℂ (Occupied Q n) ≃ₗ[ℂ] particleSector Q n :=
  LinearEquiv.ofBijective (sectorSynthesis Q n) (by
    constructor
    · intro c d h
      exact vector_injective (congrArg Subtype.val h)
    · intro x
      obtain ⟨c, hc⟩ := exists_vector_of_support x.val x.property
      exact ⟨c, Subtype.ext hc⟩)

@[simp] lemma sectorEquiv_apply (c : EuclideanSpace ℂ (Occupied Q n)) :
    (sectorEquiv Q n c).val = vector c := rfl

end ContinuumCoulomb.OccupationFock

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ThirdOrderPerturbation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A third-order block estimate. Keeping the high-block correction in the
effective form makes simultaneous three-body gadgets have a decreasing error. -/

noncomputable section
namespace ContinuumCoulomb.Perturbation
open scoped InnerProductSpace

variable {L H : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def thirdOrderForm (C : L →L[ℝ] L) (T D : H →L[ℝ] H) (B : L →L[ℝ] H)
    (p : L) : ℝ := effectiveForm C T B p + ⟪T (B p),D (T (B p))⟫_ℝ

end ContinuumCoulomb.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ThirdOrderBottom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Third-order comparison of actual finite-dimensional ground energies. -/

noncomputable section
namespace ContinuumCoulomb.Perturbation
open scoped InnerProductSpace
variable {L H : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def thirdOrderBottom (C : L →L[ℝ] L) (T D : H →L[ℝ] H) (B : L →L[ℝ] H) : ℝ :=
  sInf {e | ∃ p : L, ‖p‖ = 1 ∧ e = thirdOrderForm C T D B p}

end ContinuumCoulomb.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_OrthogonalBlockDecomposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Block coordinates on an orthogonal subspace and its actual complement.
The high space may retain an unused copy of the low coordinates, since the
physical vectors and trial vectors lie in the kernel of the restriction. -/

noncomputable section
namespace ContinuumCoulomb.Perturbation
open scoped InnerProductSpace
variable {L H : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def orthogonalHighPart (E : L →L[ℝ] H) (R : H →L[ℝ] L) (x : H) : H := x-E (R x)

end ContinuumCoulomb.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_Cubature
attribute [-simp] _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Equal-mass two-point Gauss rule

The tensor product of this degree-three rule uses eight equal masses in each
three-dimensional cell. Exact moment identities and fourth-derivative estimates
control its error.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace ContinuumCoulomb

def gaussAbscissa : ℝ := (Real.sqrt 3)⁻¹

theorem gaussAbscissa_pos : 0 < gaussAbscissa := by
  unfold gaussAbscissa
  positivity

theorem gaussAbscissa_sq : gaussAbscissa ^ 2 = (1 / 3 : ℝ) := by
  rw [gaussAbscissa, inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

/-- The two normalized abscissae, indexed for the tensor-product rule. -/
def gaussNode (b : Fin 2) : ℝ := if b = 0 then -gaussAbscissa else gaussAbscissa

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_DensitySynthesis
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Nonnegative continuous-density synthesis for the unit-charge construction

The density is the uniform slab plus `ΔV/(4π)`. Compact support of `V`
inside the slab makes its attractive Coulomb field exactly the slab field
plus `V`. A pointwise Laplacian bound makes the density nonnegative.
Only C² regularity is required, as the manuscript's manufactured well is
finitely smooth.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def slabDomain (H S : ℝ) : Set Position :=
  {x | |x 0| ≤ H ∧ |x 1| ≤ H ∧ |x 2| ≤ S}

def slabDensity (rho H S : ℝ) : Position → ℝ :=
  (slabDomain H S).indicator fun _ => rho

def slabPotential (rho H S : ℝ) (y : Position) : ℝ :=
  -(∫ x, Coulomb.coulombKernel (y - x) * slabDensity rho H S x)

end ContinuumCoulomb

end

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

def clip (B : ℕ) (z : ℤ) : ℤ := max (-(B:ℤ)) (min (B:ℤ) z)

theorem clip_bounds (B : ℕ) (z : ℤ) : -(B:ℤ) ≤ clip B z ∧ clip B z ≤ B := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by omega) (min_le_left _ _)

theorem clip_natAbs (B : ℕ) (z : ℤ) : (clip B z).natAbs ≤ B := by
  have h := clip_bounds B z
  have ha : ((clip B z).natAbs:ℤ) ≤ (B:ℤ) := by
    simpa only [Int.natCast_natAbs] using (abs_le.mpr h : |clip B z| ≤ (B:ℤ))
  exact_mod_cast ha

def numerator (D B : ℕ) (q : ℚ) : ℤ := clip B ⌊(D:ℚ)*q⌋

abbrev Input := (ℕ×ℕ)×ℚ

end ContinuumCoulomb.RationalBoxRound

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_EulerRegisters
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

abbrev Registers := ℤ×(ℤ×ℤ)
abbrev Parameters (E : Type) := E×(ℕ×(ℕ×ℚ))
abbrev Config (E : Type) := Parameters E×(ℕ×Registers)

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

variable {E : Type}

def initial (e : E) (N D B : ℕ) (r : Registers) : Config E :=
  ((e,(D,(B,(N:ℚ)⁻¹))),(0,r))

end ContinuumCoulomb.EulerRegisters

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_EulerSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial step count, sample precision, and register denominator for
unit-time integration with fixed speed/Lipschitz guards. The same step
count is used as the velocity sample precision. -/

namespace ContinuumCoulomb.EulerRegisters

def steps (C P : ℕ) : ℕ := 16*C^2*(P+1)
def denominator (C P : ℕ) : ℕ := (steps C P)^2

end ContinuumCoulomb.EulerRegisters

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_PublishedFlowInput
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-dimensional ODE input used by the transport step.

Gerald Teschl, Ordinary Differential Equations and Dynamical Systems,
AMS GSM 140 (2012), Theorem 2.10, equations (2.49)--(2.51), Lemma 2.7,
and Lemma 3.11. We retain only dimension three, four spatial derivatives,
and the closed time interval [0,1]. Uniform derivative bounds follow by
applying Gronwall to the four variational equations.
-/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

def flowJacobian (G : Position → ℝ → Position) (t : ℝ) (x : Position) : ℝ :=
  (fderiv ℝ (fun y => G y t) x).det

def IsUnitTimeFlow (v : ℝ → Position → Position) (G : Position → ℝ → Position) : Prop :=
  (∀ x, G x 0 = x) ∧
    ∀ x t, t ∈ Set.Icc (0 : ℝ) 1 →
      HasDerivWithinAt (G x) (v t (G x t)) (Set.Icc (0 : ℝ) 1) t

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_FlowImplicit
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite C⁴ implicit-function step for the actual four-dimensional
autonomous lift of the three-dimensional time-dependent flow. -/

noncomputable section
open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
namespace ContinuumCoulomb

abbrev FlowPhase := ℝ × Position
abbrev FlowPath := C(WeakMTWTransport.UnitTime,FlowPhase)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_TransportedNodes
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual tensor Gauss nodes on a cubic lattice are separated before
transport, after transport, and after rational rounding. The enclosing finite
set of cells will determine the nucleus count in the final construction. -/

noncomputable section
open scoped NNReal
namespace ContinuumCoulomb

abbrev GaussLatticeIndex := (Fin 3 → ℤ) × (Fin 3 → Fin 2)

def gaussLatticePoint (h : ℝ) (i : GaussLatticeIndex) : Position :=
  WithLp.toLp 2 (fun a => h * ((i.1 a : ℝ) + gaussNode (i.2 a) / 2))

theorem gaussAbscissa_bounds : (1 / 2 : ℝ) < gaussAbscissa ∧ gaussAbscissa < 2 / 3 := by
  have hp := gaussAbscissa_pos
  have hs := gaussAbscissa_sq
  constructor <;> nlinarith

theorem gaussNode_bounds (b : Fin 2) :
    -gaussAbscissa ≤ gaussNode b ∧ gaussNode b ≤ gaussAbscissa := by
  fin_cases b <;> norm_num [gaussNode, gaussAbscissa_pos.le]

theorem gauss_lattice_coordinate_separation {h : ℝ} (hh : 0 < h)
    (k l : ℤ) (b c : Fin 2) (hne : k ≠ l ∨ b ≠ c) :
    h / 3 ≤ |h * ((k : ℝ) + gaussNode b / 2) -
      h * ((l : ℝ) + gaussNode c / 2)| := by
  have hb := gaussNode_bounds b
  have hc := gaussNode_bounds c
  have ha := gaussAbscissa_bounds
  rcases lt_trichotomy k l with hkl | hkl | hkl
  · have hi : (k : ℝ) + 1 ≤ l := by exact_mod_cast (show k + 1 ≤ l by omega)
    have hprod := mul_nonneg hh.le (show 0 ≤ gaussNode c - gaussNode b + 2 * gaussAbscissa by linarith)
    have hscale := mul_pos hh (show 0 < (2 / 3 : ℝ) - gaussAbscissa by linarith)
    have hInt := mul_nonneg hh.le (show 0 ≤ (l : ℝ) - k - 1 by linarith)
    nlinarith [neg_le_abs (h * ((k : ℝ) + gaussNode b / 2) -
      h * ((l : ℝ) + gaussNode c / 2))]
  · subst l
    have hbc : b ≠ c := hne.resolve_left (not_not.mpr rfl)
    have hplus := le_abs_self (h * ((k : ℝ) + gaussNode b / 2) -
      h * ((k : ℝ) + gaussNode c / 2))
    have hminus := neg_le_abs (h * ((k : ℝ) + gaussNode b / 2) -
      h * ((k : ℝ) + gaussNode c / 2))
    have hscale := mul_pos hh (show 0 < gaussAbscissa - (1 / 3 : ℝ) by linarith)
    fin_cases b <;> fin_cases c <;> norm_num [gaussNode] at * <;> nlinarith
  · have hi : (l : ℝ) + 1 ≤ k := by exact_mod_cast (show l + 1 ≤ k by omega)
    have hprod := mul_nonneg hh.le (show 0 ≤ gaussNode b - gaussNode c + 2 * gaussAbscissa by linarith)
    have hscale := mul_pos hh (show 0 < (2 / 3 : ℝ) - gaussAbscissa by linarith)
    have hInt := mul_nonneg hh.le (show 0 ≤ (k : ℝ) - l - 1 by linarith)
    nlinarith [le_abs_self (h * ((k : ℝ) + gaussNode b / 2) -
      h * ((l : ℝ) + gaussNode c / 2))]

theorem gaussLatticePoint_separation {h : ℝ} (hh : 0 < h)
    (i j : GaussLatticeIndex) (hne : i ≠ j) :
    h / 3 ≤ ‖gaussLatticePoint h i - gaussLatticePoint h j‖ := by
  have hex : ∃ a, i.1 a ≠ j.1 a ∨ i.2 a ≠ j.2 a := by
    by_contra hn
    push Not at hn
    exact hne (Prod.ext (funext (fun a => (hn a).1)) (funext (fun a => (hn a).2)))
  obtain ⟨a, ha⟩ := hex
  have hcoord := gauss_lattice_coordinate_separation hh (i.1 a) (j.1 a) (i.2 a) (j.2 a) ha
  have hb := PiLp.norm_apply_le (gaussLatticePoint h i - gaussLatticePoint h j) a
  change |h * ((i.1 a : ℝ) + gaussNode (i.2 a) / 2) -
    h * ((j.1 a : ℝ) + gaussNode (j.2 a) / 2)| ≤ _ at hb
  exact hcoord.trans hb

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_HeatKernelModulus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative bounds for the scalar heat-resolvent kernel away from
time zero. Every constant is elementary in the cutoff and radius. -/

noncomputable section
namespace ContinuumCoulomb.HeatKernelModulus

def exponent (t A : ℝ) : ℝ := -t - A / (4 * t)
def kernel (t A : ℝ) : ℝ := Real.exp (exponent t A) / (4 * Real.pi * t)

end ContinuumCoulomb.HeatKernelModulus

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_RationalTaylorRegisters
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

abbrev State := ℤ × (ℕ × (ℕ × (ℤ × (ℕ × ℤ))))

def step (s : State) : State :=
  let factor := (s.2.2.1 + 1) * s.2.1
  (s.1, s.2.1, s.2.2.1 + 1, (factor : ℤ) * (s.2.2.2.1 + s.2.2.2.2.2),
    factor * s.2.2.2.2.1, s.1 * s.2.2.2.2.2)

def initial (q : ℚ) : State := (q.num, q.den, 0, 0, 1, 1)

def result (s : State) : ℚ := mkRat s.2.2.2.1 s.2.2.2.2.1

def measure (s : State) : ℕ := s.1.natAbs.bits.length + s.2.1.bits.length +
  s.2.2.1.bits.length + max s.2.2.2.1.natAbs.bits.length s.2.2.2.2.2.natAbs.bits.length +
    s.2.2.2.2.1.bits.length

theorem iterate_parameters (s : State) (n : ℕ) :
    ((step^[n]) s).1 = s.1 ∧ ((step^[n]) s).2.1 = s.2.1 ∧
      ((step^[n]) s).2.2.1.bits.length ≤ s.2.2.1.bits.length + n := by
  induction n with
  | zero => exact ⟨rfl, rfl, le_rfl⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    refine ⟨ih.1, ih.2.1, ?_⟩
    exact (AmplificationProgram.bits_succ _).trans (by omega)

end ContinuumCoulomb.RationalTaylorRegisters

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
open EulerRegisters (Registers)

abbrev Signs := Bool×(Bool×Bool)

def index (k : Registers) (b : Signs) : GaussLatticeIndex :=
  (![k.1,k.2.1,k.2.2],![if b.1 then 1 else 0,if b.2.1 then 1 else 0,if b.2.2 then 1 else 0])

end ContinuumCoulomb.RationalGaussNodes

end

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
abbrev Input := ℕ×(ℕ×(EulerRegisters.Registers×Signs))

abbrev CoordinateInput := (ℕ×ℕ)×(ℤ×Bool)

end ContinuumCoulomb.RationalGaussNodes

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CoulombPacketTests
attribute [-simp] _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
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

def zero : CoulombPacket where
  value _ := 0
  continuous := continuous_const
  integrable := integrable_zero Position ℝ volume
  bound := 0
  bound_nonnegative := le_rfl
  bound_spec _ := by simp

def sumList : List CoulombPacket → CoulombPacket
  | [] => zero
  | f :: fs => add f (sumList fs)

def combination {m : ℕ} (f : Fin m → CoulombPacket) (d : Fin m → ℝ) : CoulombPacket :=
  sumList (List.ofFn (fun i => smul (d i) (f i)))

def ofCompact (f : Position → ℝ) (hf : Continuous f) (hc : HasCompactSupport f) : CoulombPacket where
  value := f
  continuous := hf
  integrable := hf.integrable_of_hasCompactSupport hc
  bound := max (Classical.choose (hc.exists_bound_of_continuous hf)) 0
  bound_nonnegative := le_max_right _ _
  bound_spec x := (Classical.choose_spec (hc.exists_bound_of_continuous hf) x).trans (le_max_left _ _)

end ContinuumCoulomb.CoulombPacket

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedDualMatrix
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
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

def localDualBump : ContDiffBump (0 : Position) := ⟨1, 2, by norm_num, by norm_num⟩

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarModeH1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Membership of the manufactured mode in the closed planar Sobolev
graph, obtained by expanding compact cutoffs. -/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace ContinuumCoulomb
namespace PlanarSobolev
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean

def cutoffScale (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹

theorem cutoffScale_positive (n : ℕ) : 0 < cutoffScale n := inv_pos.mpr (by positivity)

theorem cutoffScale_le_one (n : ℕ) : cutoffScale n ≤ 1 := by
  unfold cutoffScale
  apply inv_le_one_of_one_le₀
  linarith [Nat.cast_nonneg (α := ℝ) n]

theorem cutoffScale_tendsto : Tendsto cutoffScale atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp
    (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)

end PlanarSobolev
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ExplicitVerticalCutoff
attribute [-simp] _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit smooth transverse cutoff. Its formula uses only the fixed
smooth transition function, so rational approximation can use the actual
exponential formula instead of a classically selected bump function. -/

noncomputable section
namespace ContinuumCoulomb

def verticalCutoffBump (z : ℝ) : ℝ :=
  Real.smoothTransition ((4-z^2)/3)

namespace verticalCutoffBump

theorem contDiff {n : ℕ∞} : ContDiff ℝ n verticalCutoffBump :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.sub (contDiff_id.pow 2)).div_const 3)

theorem zero_of_le_dist {z : ℝ} (hz : 2 ≤ dist z 0) :
    verticalCutoffBump z = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have hab : 2 ≤ |z| := by simpa [Real.dist_eq] using hz
  have hsq := (sq_le_sq₀ (by norm_num : (0:ℝ) ≤ 2) (abs_nonneg z)).mpr hab
  rw [sq_abs] at hsq
  linarith

theorem hasCompactSupport : HasCompactSupport verticalCutoffBump := by
  apply (isCompact_closedBall (0 : ℝ) 2).of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ Metric.isClosed_closedBall
  intro z hz
  by_contra hn
  have hd : 2 ≤ dist z 0 := (lt_of_not_ge (by simpa [Metric.mem_closedBall] using hn)).le
  exact hz (zero_of_le_dist hd)

end verticalCutoffBump
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

abbrev Settings := (ℕ × ℕ) × ℚ

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

abbrev Input := (ℕ × ℕ) × ℚ

def mesh (P : ℕ) : ℕ := 4096 * (P + 1)
def accuracy (P : ℕ) : ℕ := 16 * (P + 1)

end ContinuumCoulomb.HoppingSchedule

end

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

abbrev Input := HoppingSchedule.Input

end ContinuumCoulomb.ComputableHopping

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarWellNumerics
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

def outside (q : ℚ×ℚ) : Prop := 1 ≤ q.1^2+q.2^2
instance instDecidableOutside (q : ℚ×ℚ) : Decidable (outside q) := inferInstanceAs (Decidable (1 ≤ q.1^2+q.2^2))

end ContinuumCoulomb.PlanarWellNumerics

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_SmoothTransitionProgram
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

abbrev Input := ℕ × ℚ

def cutoffArgument (q : ℚ) : ℚ := (4-q^2)/3

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

abbrev Input := ℕ × (ℚ × ℚ)
def argument (x : Input) : ℚ := 2/x.2.1*x.2.2

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

def translate (r a : ℚ×ℚ) : ℚ×ℚ := (r.1-a.1,r.2-a.2)

end ContinuumCoulomb.ManufacturedFieldEvaluation

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
open EulerRegisters

abbrev Environment := ℕ×((ℚ×ℚ)×List (ℚ×ℚ))

end ContinuumCoulomb.ManufacturedEuler

end

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

abbrev RowInput := ℕ×((ℚ×ℚ)×List (ℚ×ℚ))

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

abbrev Input := ℕ × (ℚ × ℚ)

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

abbrev PlanarInput := ℕ×(ℚ×(List (ℚ×ℚ)×(ℚ×ℚ)))
abbrev TermInput := PlanarInput×(ℚ×ℚ)

end ContinuumCoulomb.ManufacturedFieldEvaluation

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

abbrev Environment := ℕ×((ℚ×ℚ)×List (ℚ×ℚ))

end ContinuumCoulomb.ManufacturedVelocityEvaluation

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
open EulerRegisters (Registers)
open RationalGaussNodes (Signs)

def precision (K P : ℕ) : ℕ := 2*(K+1)*(P+1)

end ContinuumCoulomb.TransformedGauss

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_TransformedGaussSeparation
attribute [-simp] _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Distinctness of the numerical transported nodes. The input labels use
the same integer cells and eight sign choices as the exact Gauss grid. -/

noncomputable section
open scoped NNReal
namespace ContinuumCoulomb.TransformedGauss
open EulerRegisters (Registers)
open RationalGaussNodes (Signs)

theorem sign_injective {a b : Bool}
    (h : (if a then (1:Fin 2) else 0) = (if b then (1:Fin 2) else 0)) : a = b := by
  cases a <;> cases b <;> simp_all

theorem index_injective : Function.Injective (fun x : Registers×Signs =>
    RationalGaussNodes.index x.1 x.2) := by
  rintro ⟨k,b⟩ ⟨l,c⟩ h
  have h0 : k.1 = l.1 := by
    simpa [RationalGaussNodes.index] using congrArg (fun x : GaussLatticeIndex => x.1 0) h
  have h1 : k.2.1 = l.2.1 := by
    simpa [RationalGaussNodes.index] using congrArg (fun x : GaussLatticeIndex => x.1 1) h
  have h2 : k.2.2 = l.2.2 := by
    simpa [RationalGaussNodes.index] using congrArg (fun x : GaussLatticeIndex => x.1 2) h
  have hb0 : b.1 = c.1 := sign_injective (by
    simpa [RationalGaussNodes.index] using congrArg (fun x : GaussLatticeIndex => x.2 0) h)
  have hb1 : b.2.1 = c.2.1 := sign_injective (by
    simpa [RationalGaussNodes.index] using congrArg (fun x : GaussLatticeIndex => x.2 1) h)
  have hb2 : b.2.2 = c.2.2 := sign_injective (by
    simpa [RationalGaussNodes.index] using congrArg (fun x : GaussLatticeIndex => x.2 2) h)
  exact Prod.ext (Prod.ext h0 (Prod.ext h1 h2)) (Prod.ext hb0 (Prod.ext hb1 hb2))

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
open EulerRegisters (Registers )
open RationalGaussNodes (Signs )

abbrev Input := (ℕ×ℕ)×((ℚ×ℚ)×(List (ℚ×ℚ)×(Registers×Signs)))

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
open EulerRegisters (Registers )
open RationalGaussNodes (Signs )

abbrev Label := Registers×Signs

end ContinuumCoulomb.TransformedGauss

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

def rational (q : ℚ) : BinaryRational := ⟨q.num,q.den⟩

end ContinuumCoulomb.NuclearCoordinateOutput

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_SobolevDensityInput
attribute [-simp] _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The Sobolev density input for conditional estimates

N. G. Meyers and J. Serrin, *H = W*, Proc. Natl. Acad. Sci. USA 51 (1964),
1055–1056, DOI 10.1073/pnas.51.6.1055, Theorem and the Lemma on p.1056.
We use only m=1, p=2 on the full Euclidean configuration space. The finite
spin index is handled componentwise. This is smooth approximation in the
value-and-weak-gradient norm; no compact support or Coulomb-form comparison
is included in the assumption.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

/-- Squared error in the actual value-and-gradient graph. -/
def h1GraphError {n : ℕ} (u v : Coulomb.H1Vector n) : ℝ :=
  (∑ s, ∫ x, ‖u.value s x - v.value s x‖ ^ 2) +
    ∑ s, ∑ a, ∫ x, ‖u.gradient s a x - v.gradient s a x‖ ^ 2

/-- The precise specialization of the published H=W theorem. -/
def PublishedSobolevSmoothDensity : Prop :=
  ∀ (n : ℕ) (u : Coulomb.H1Vector n) (ε : ℝ), 0 < ε →
    ∃ (f : SpinConfiguration n → Configuration n → ℂ)
      (hf : ∀ s, ContDiff ℝ (⊤ : ℕ∞) (f s))
      (hL2 : ∀ s, MemLp (f s) 2)
      (hpartial : ∀ s a, MemLp
        (fun x => fderiv ℝ (f s) x (EuclideanSpace.single a 1)) 2),
      h1GraphError u (classicalH1State f (fun s => (hf s).of_le (by first | simp | exact_mod_cast le_top)) hL2 hpartial) < ε

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_H1GraphCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full weak-H1 graph as finitely many actual L2 coordinates. Compact
C1 states approximate every coordinate simultaneously, so continuous form
inequalities on this graph extend to the full weak-H1 domain. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace ContinuumCoulomb

abbrev H1Index (n : ℕ) := SpinConfiguration n ⊕ (SpinConfiguration n × (Fin n × Fin 3))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_H1BoundedForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuous kinetic-plus-bounded-operator forms on the full H1 graph. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

abbrev H1Coordinates (n : ℕ) := H1Index n → Lp ℂ 2 (volume : Measure (Configuration n))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_BoundedPotentialOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual bounded real multiplication potentials on the weak-H1 graph. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb
namespace BoundedPotential

variable {n : ℕ} (V : Configuration n → ℝ) (hV : Continuous V)
  (B : ℝ) (hB : ∀ x, |V x| ≤ B)

include hV hB in
theorem product_memLp (u : Lp ℂ 2 (volume : Measure (Configuration n))) :
    MemLp (fun x => (V x : ℂ) * u x) 2 := by
  apply (Lp.memLp u).of_le_mul (c := B)
    ((Complex.continuous_ofReal.comp hV).aestronglyMeasurable.mul (Lp.aestronglyMeasurable u))
  filter_upwards [] with x
  change ‖(V x : ℂ) * u x‖ ≤ B * ‖u x‖
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hB x) (norm_nonneg _)

def value (u : Lp ℂ 2 (volume : Measure (Configuration n))) :
    Lp ℂ 2 (volume : Measure (Configuration n)) :=
  (product_memLp V hV B hB u).toLp (fun x => (V x : ℂ)*u x)

theorem value_ae (u : Lp ℂ 2 (volume : Measure (Configuration n))) :
    value V hV B hB u =ᵐ[volume] fun x => (V x : ℂ)*u x :=
  (product_memLp V hV B hB u).coeFn_toLp

def linear : Lp ℂ 2 (volume : Measure (Configuration n)) →ₗ[ℂ]
    Lp ℂ 2 (volume : Measure (Configuration n)) where
  toFun := value V hV B hB
  map_add' u v := by
    apply Lp.ext
    filter_upwards [value_ae V hV B hB (u+v), value_ae V hV B hB u,
      value_ae V hV B hB v, Lp.coeFn_add u v,
      Lp.coeFn_add (value V hV B hB u) (value V hV B hB v)] with x he hu hv hs ht
    simp only [he, hs, ht, hu, hv, Pi.add_apply]
    ring
  map_smul' c u := by
    change value V hV B hB (c • u) = c • value V hV B hB u
    apply Lp.ext
    filter_upwards [value_ae V hV B hB (c • u), value_ae V hV B hB u,
      Lp.coeFn_smul c u, Lp.coeFn_smul c (value V hV B hB u)] with x he hu hs ht
    simp only [he, hs, ht, hu, Pi.smul_apply, smul_eq_mul]
    ring

def operator : Lp ℂ 2 (volume : Measure (Configuration n)) →L[ℝ]
    Lp ℂ 2 (volume : Measure (Configuration n)) :=
  ((linear V hV B hB).mkContinuous B (fun u =>
    Lp.norm_le_mul_norm_of_ae_le_mul (by
      filter_upwards [value_ae V hV B hB u] with x hx
      change ‖value V hV B hB u x‖ ≤ B * ‖u x‖
      rw [hx, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hB x) (norm_nonneg _)))).restrictScalars ℝ

end BoundedPotential

end ContinuumCoulomb

end

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

abbrev Environment := (ℕ × ℕ) × (ℕ × (ℚ × ℚ))

noncomputable def coulombPrecision (N P : ℕ) : ℕ := 64 * (N + 1) * (P + 1) ^ 2
noncomputable def hoppingPrecision (scale P : ℕ) : ℕ := 4 * (scale + 1) * (P + 1)
noncomputable def rootPrecision (P : ℕ) : ℕ := 8 * (P + 1)

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

abbrev BisectionInput := ℕ × (Environment × (ℚ × ℚ))

def tolerance (e : Environment) : ℚ := 1 / ((e.1.2 : ℚ) + 1)

def bisectionArgument (x : BisectionInput) : BisectionProgram.Input Environment :=
  (x.1, (x.2.1, (tolerance x.2.1, x.2.2)))

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

def refinedEnvironment (e : Environment) : Environment :=
  ((e.1.1, 8 * (e.1.2 + 1)), e.2)

end ContinuumCoulomb.CalibratedEvaluation

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactTemplates
attribute [-simp] _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two fixed nine-link contact templates used after spin subdivision.
Coordinates use the Euclidean plane. The link lengths and separation
bounds are stable under small movements of the sites. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators

abbrev ContactPoint := EuclideanSpace ℝ (Fin 2)

def contactPoint (x y : ℝ) : ContactPoint := WithLp.toLp 2 ![x, y]

@[simp] theorem contactPoint_zero (x y : ℝ) : contactPoint x y 0 = x := rfl
@[simp] theorem contactPoint_one (x y : ℝ) : contactPoint x y 1 = y := rfl

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactAdjustment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit one-variable continuation for independent contact lengths.
Four sloping links share a transverse height; the other five remain axial.
Thus each nine-link path is adjusted by one scalar intermediate-value solve,
with fixed endpoints and no solve whose dimension grows with the lattice. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators

def adjustedContactForward (length h : ℝ) : ℝ := Real.sqrt (length ^ 2 - h ^ 2)

def adjustedContactStepX (lengths : ℕ → ℝ) (h : ℝ) (k : ℕ) : ℝ :=
  if k = 2 ∨ k = 3 ∨ k = 5 ∨ k = 6 then adjustedContactForward (lengths k) h
  else lengths k

def adjustedContactSpan (lengths : ℕ → ℝ) (h : ℝ) : ℝ :=
  ∑ j ∈ Finset.range 9, adjustedContactStepX lengths h j

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactGadgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two signed-edge contact gadgets. Each has twenty sites, nineteen
links, fixed original endpoints, and independently prescribed link lengths.
A negative input sign places the central partner off the backbone. -/

noncomputable section
namespace ContinuumCoulomb

abbrev ContactGadgetSite := Fin 10 ⊕ (Fin 9 ⊕ Unit)

def contactGadgetSide : ContactGadgetSite := Sum.inr (Sum.inr ())

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactStrips
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform separation of contacts from different lattice edges. The estimates
use only fixed strip bounds, so the lattice size never enters their constants. -/

noncomputable section
namespace ContinuumCoulomb

/-- Coordinates of an internal site in an oriented length-17 lattice edge.
Off-axis sites stay farther from both original endpoints. -/
structure ContactStripSite where
  axial : ℝ
  transverse : ℝ
  axial_lower : 1 ≤ axial
  axial_upper : axial ≤ 16
  transverse_lower : 0 ≤ transverse
  transverse_upper : transverse ≤ 4 / 3
  off_axis_lower : transverse ≠ 0 → 11 / 4 ≤ axial
  off_axis_upper : transverse ≠ 0 → axial ≤ 57 / 4

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactMediator
attribute [-simp] _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit labels for the eighteen fresh sites of each three-stage
mediator gadget. These identify the actual iterated graph with the
nineteen-link contact geometry, rather than only matching their counts. -/

namespace ContinuumCoulomb.ContactMediator
open MediatorGraph MediatorIteration

abbrev LocalPath := Fin 2 ⊕ (Fin 2 × Fin 2)
abbrev LocalInternal := Fin 2 ⊕ ((Fin 2 × Fin 2) ⊕ (LocalPath × Fin 2))
abbrev LocalSite := Fin 2 ⊕ LocalInternal

def spokeIndex (r : ℕ) (e : Fin r) (s : Fin 2) : Fin (r * 2) :=
  finProdFinEquiv (e, s)

def pathIndex (r : ℕ) (e : Fin r) : LocalPath → Fin (r * 2 + r * 2 * 2)
  | Sum.inl s => finSumFinEquiv (Sum.inl (spokeIndex r e s))
  | Sum.inr (s, t) => finSumFinEquiv (Sum.inr (spokeIndex (r * 2) (spokeIndex r e s) t))

def decodePath (r : ℕ) (a : Fin (r * 2 + r * 2 * 2)) : Fin r × LocalPath :=
  match finSumFinEquiv.symm a with
  | Sum.inl a =>
      let es := finProdFinEquiv.symm a
      (es.1, Sum.inl es.2)
  | Sum.inr a =>
      let st := finProdFinEquiv.symm a
      let es := finProdFinEquiv.symm st.1
      (es.1, Sum.inr (es.2, st.2))

def pathEquiv (r : ℕ) : Fin r × LocalPath ≃ Fin (r * 2 + r * 2 * 2) where
  toFun x := pathIndex r x.1 x.2
  invFun := decodePath r
  left_inv := by
    rintro ⟨e, s | ⟨s, t⟩⟩ <;> simp [pathIndex, decodePath, spokeIndex]
  right_inv := by
    intro a
    obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective a
    cases a with
    | inl a =>
      obtain ⟨⟨e, s⟩, rfl⟩ := finProdFinEquiv.surjective a
      simp [pathIndex, decodePath, spokeIndex]
    | inr a =>
      obtain ⟨⟨a, t⟩, rfl⟩ := finProdFinEquiv.surjective a
      obtain ⟨⟨e, s⟩, rfl⟩ := finProdFinEquiv.surjective a
      simp [pathIndex, decodePath, spokeIndex]

@[simp] theorem decodePath_pathIndex (r : ℕ) (e : Fin r) (p : LocalPath) :
    decodePath r (pathIndex r e p) = (e, p) :=
  (pathEquiv r).symm_apply_apply (e, p)

@[simp] theorem finProd_divNat {m n : ℕ} (a : Fin m) (b : Fin n) :
    (finProdFinEquiv (a, b)).divNat = a :=
  congrArg Prod.fst ((finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n)).symm_apply_apply (a, b))

@[simp] theorem finProd_modNat {m n : ℕ} (a : Fin m) (b : Fin n) :
    (finProdFinEquiv (a, b)).modNat = b :=
  congrArg Prod.snd ((finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n)).symm_apply_apply (a, b))

def encodeSite (n r : ℕ) : Fin n ⊕ (Fin r × LocalInternal) →
    Fin (n + r * 2 + r * 2 * 2 + (r * 2 + r * 2 * 2) * 2)
  | Sum.inl i => old _ _ (old _ _ (old n r i))
  | Sum.inr (e, Sum.inl s) => old _ _ (old _ _ (fresh n r e s))
  | Sum.inr (e, Sum.inr (Sum.inl (s, t))) =>
      old _ _ (fresh (n + r * 2) (r * 2) (spokeIndex r e s) t)
  | Sum.inr (e, Sum.inr (Sum.inr (p, t))) =>
      fresh (n + r * 2 + r * 2 * 2) (r * 2 + r * 2 * 2) (pathIndex r e p) t

def decodeSite (n r : ℕ)
    (k : Fin (n + r * 2 + r * 2 * 2 + (r * 2 + r * 2 * 2) * 2)) :
    Fin n ⊕ (Fin r × LocalInternal) :=
  match (vertexEquiv (n + r * 2 + r * 2 * 2) (r * 2 + r * 2 * 2)).symm k with
  | Sum.inl k =>
      match (vertexEquiv (n + r * 2) (r * 2)).symm k with
      | Sum.inl k =>
          match (vertexEquiv n r).symm k with
          | Sum.inl i => Sum.inl i
          | Sum.inr (e, s) => Sum.inr (e, Sum.inl s)
      | Sum.inr (a, t) =>
          let es := finProdFinEquiv.symm a
          Sum.inr (es.1, Sum.inr (Sum.inl (es.2, t)))
  | Sum.inr (a, t) =>
      match finSumFinEquiv.symm a with
      | Sum.inl a =>
          let es := finProdFinEquiv.symm a
          Sum.inr (es.1, Sum.inr (Sum.inr (Sum.inl es.2, t)))
      | Sum.inr a =>
          let st := finProdFinEquiv.symm a
          let es := finProdFinEquiv.symm st.1
          Sum.inr (es.1, Sum.inr (Sum.inr (Sum.inr (es.2, st.2), t)))

theorem decode_encode (n r : ℕ) (x : Fin n ⊕ (Fin r × LocalInternal)) :
    decodeSite n r (encodeSite n r x) = x := by
  rcases x with i | ⟨e, s | (st | ⟨p, t⟩)⟩
  · simp [encodeSite, decodeSite, old]
  · simp [encodeSite, decodeSite, old, fresh]
  · rcases st with ⟨s, t⟩
    simp [encodeSite, decodeSite, old, fresh, spokeIndex]
  · cases p with
    | inl s => simp [encodeSite, decodeSite, fresh, pathIndex, spokeIndex]
    | inr st =>
      rcases st with ⟨s, u⟩
      simp [encodeSite, decodeSite, fresh, pathIndex, spokeIndex]

theorem encode_decode (n r : ℕ)
    (k : Fin (n + r * 2 + r * 2 * 2 + (r * 2 + r * 2 * 2) * 2)) :
    encodeSite n r (decodeSite n r k) = k := by
  obtain ⟨k, rfl⟩ := (vertexEquiv (n + r * 2 + r * 2 * 2)
    (r * 2 + r * 2 * 2)).surjective k
  rcases k with k | ⟨a, t⟩
  · obtain ⟨k, rfl⟩ := (vertexEquiv (n + r * 2) (r * 2)).surjective k
    rcases k with k | ⟨a, t⟩
    · obtain ⟨k, rfl⟩ := (vertexEquiv n r).surjective k
      rcases k with i | ⟨e, s⟩
      · simp [encodeSite, decodeSite, old]
      · simp [encodeSite, decodeSite, old, fresh]
    · obtain ⟨⟨e, s⟩, rfl⟩ := finProdFinEquiv.surjective a
      simp [encodeSite, decodeSite, old, fresh, spokeIndex]
  · obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective a
    cases a with
    | inl a =>
      obtain ⟨⟨e, s⟩, rfl⟩ := finProdFinEquiv.surjective a
      simp [encodeSite, decodeSite, fresh, pathIndex, spokeIndex]
    | inr a =>
      obtain ⟨⟨a, u⟩, rfl⟩ := finProdFinEquiv.surjective a
      obtain ⟨⟨e, s⟩, rfl⟩ := finProdFinEquiv.surjective a
      simp [encodeSite, decodeSite, fresh, pathIndex, spokeIndex]

def siteEquiv (n r : ℕ) : Fin n ⊕ (Fin r × LocalInternal) ≃
    Fin (n + r * 2 + r * 2 * 2 + (r * 2 + r * 2 * 2) * 2) where
  toFun := encodeSite n r
  invFun := decodeSite n r
  left_inv := decode_encode n r
  right_inv := encode_decode n r

def localToContact : LocalSite → ContactGadgetSite
  | Sum.inl s => if s = 0 then Sum.inl 0 else Sum.inr (Sum.inl 8)
  | Sum.inr (Sum.inl s) => if s = 0 then Sum.inl 9 else contactGadgetSide
  | Sum.inr (Sum.inr (Sum.inl (s, t))) =>
      if s = 0 then Sum.inl (if t = 0 then 3 else 6)
      else Sum.inr (Sum.inl (if t = 0 then 5 else 2))
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl s, t))) =>
      if s = 0 then Sum.inl (if t = 0 then 4 else 5)
      else Sum.inr (Sum.inl (if t = 0 then 4 else 3))
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (s, u), t))) =>
      if s = 0 then Sum.inl (if u = 0 then (if t = 0 then 1 else 2)
        else (if t = 0 then 8 else 7))
      else Sum.inr (Sum.inl (if u = 0 then (if t = 0 then 7 else 6)
        else (if t = 0 then 0 else 1)))

def localOld (s : Fin 2) : LocalSite := Sum.inl s
def localFirst (s : Fin 2) : LocalSite := Sum.inr (Sum.inl s)
def localSecond (s t : Fin 2) : LocalSite := Sum.inr (Sum.inr (Sum.inl (s, t)))
def localThird (p : LocalPath) (t : Fin 2) : LocalSite :=
  Sum.inr (Sum.inr (Sum.inr (p, t)))

def contactToLocal : ContactGadgetSite → LocalSite
  | Sum.inl i => ![localOld 0,
      localThird (Sum.inr (0, 0)) 0, localThird (Sum.inr (0, 0)) 1,
      localSecond 0 0, localThird (Sum.inl 0) 0, localThird (Sum.inl 0) 1,
      localSecond 0 1, localThird (Sum.inr (0, 1)) 1,
      localThird (Sum.inr (0, 1)) 0, localFirst 0] i
  | Sum.inr (Sum.inl i) => ![localThird (Sum.inr (1, 1)) 0,
      localThird (Sum.inr (1, 1)) 1, localSecond 1 1,
      localThird (Sum.inl 1) 1, localThird (Sum.inl 1) 0,
      localSecond 1 0, localThird (Sum.inr (1, 0)) 1,
      localThird (Sum.inr (1, 0)) 0, localOld 1] i
  | Sum.inr (Sum.inr _) => localFirst 1

theorem contact_local_inverse (x : LocalSite) : contactToLocal (localToContact x) = x := by
  rcases x with s | (s | (⟨s, t⟩ | ⟨p, t⟩))
  · fin_cases s <;> rfl
  · fin_cases s <;> rfl
  · fin_cases s <;> fin_cases t <;> rfl
  · cases p with
    | inl s => fin_cases s <;> fin_cases t <;> rfl
    | inr su =>
      rcases su with ⟨s, u⟩
      fin_cases s <;> fin_cases u <;> fin_cases t <;> rfl

theorem local_contact_inverse (x : ContactGadgetSite) : localToContact (contactToLocal x) = x := by
  rcases x with i | (i | ⟨⟩)
  · fin_cases i <;> rfl
  · fin_cases i <;> rfl
  · rfl

def localContactEquiv : LocalSite ≃ ContactGadgetSite where
  toFun := localToContact
  invFun := contactToLocal
  left_inv := contact_local_inverse
  right_inv := local_contact_inverse

def localVertex {n r : ℕ} (a b : Fin n) (e : Fin r) : LocalSite →
    Fin (n + r * 2 + r * 2 * 2 + (r * 2 + r * 2 * 2) * 2) :=
  fun x => siteEquiv n r (Sum.elim
    (fun s => Sum.inl (if s = 0 then a else b)) (fun u => Sum.inr (e, u)) x)

abbrev LocalEdge := Unit ⊕ (LocalPath ⊕ (LocalPath × Fin 2))

def encodeEdge (r : ℕ) (e : Fin r) : LocalEdge →
    Fin (r + ((r * 2 + r * 2 * 2) + (r * 2 + r * 2 * 2) * 2))
  | Sum.inl _ => finSumFinEquiv (Sum.inl e)
  | Sum.inr (Sum.inl p) =>
      finSumFinEquiv (Sum.inr (finSumFinEquiv (Sum.inl (pathIndex r e p))))
  | Sum.inr (Sum.inr (p, t)) =>
      finSumFinEquiv (Sum.inr (finSumFinEquiv
        (Sum.inr (spokeIndex (r * 2 + r * 2 * 2) (pathIndex r e p) t))))

def decodeEdge (r : ℕ)
    (a : Fin (r + ((r * 2 + r * 2 * 2) + (r * 2 + r * 2 * 2) * 2))) :
    Fin r × LocalEdge :=
  match finSumFinEquiv.symm a with
  | Sum.inl e => (e, Sum.inl ())
  | Sum.inr a =>
      match finSumFinEquiv.symm a with
      | Sum.inl a =>
          let ep := (pathEquiv r).symm a
          (ep.1, Sum.inr (Sum.inl ep.2))
      | Sum.inr a =>
          let pt := finProdFinEquiv.symm a
          let ep := (pathEquiv r).symm pt.1
          (ep.1, Sum.inr (Sum.inr (ep.2, pt.2)))

def edgeEquiv (r : ℕ) : Fin r × LocalEdge ≃
    Fin (r + ((r * 2 + r * 2 * 2) + (r * 2 + r * 2 * 2) * 2)) where
  toFun x := encodeEdge r x.1 x.2
  invFun := decodeEdge r
  left_inv := by
    rintro ⟨e, ⟨⟩ | (p | ⟨p, t⟩)⟩
    · simp [encodeEdge, decodeEdge]
    · change decodeEdge r (finSumFinEquiv (Sum.inr
        (finSumFinEquiv (Sum.inl (pathEquiv r (e, p)))))) = _
      simp [decodeEdge]
    · change decodeEdge r (finSumFinEquiv (Sum.inr (finSumFinEquiv
        (Sum.inr (spokeIndex (r * 2 + r * 2 * 2) (pathEquiv r (e, p)) t))))) = _
      simp [decodeEdge, spokeIndex]
  right_inv := by
    intro a
    obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective a
    cases a with
    | inl e => simp [encodeEdge, decodeEdge]
    | inr a =>
      obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective a
      cases a with
      | inl a =>
        obtain ⟨⟨e, p⟩, rfl⟩ := (pathEquiv r).surjective a
        simp [encodeEdge, decodeEdge]; rfl
      | inr a =>
        obtain ⟨⟨a, t⟩, rfl⟩ := finProdFinEquiv.surjective a
        obtain ⟨⟨e, p⟩, rfl⟩ := (pathEquiv r).surjective a
        simp [encodeEdge, decodeEdge, spokeIndex]; rfl

def firstAttachment (member : Fin 2) (s : Fin 2) : Fin 2 :=
  if s = 0 then 0 else member

def secondEndpoint (member : Fin 2) (p : LocalPath) (t : Fin 2) : LocalSite :=
  match p with
  | Sum.inl s => localSecond s t
  | Sum.inr (s, u) => if t = 0 then
      (if u = 0 then localOld s else localFirst (firstAttachment member s))
    else localSecond s u

def localLeft (member : Fin 2) : LocalEdge → LocalSite
  | Sum.inl _ => localFirst 0
  | Sum.inr (Sum.inl p) => localThird p 0
  | Sum.inr (Sum.inr (p, t)) => secondEndpoint member p t

def localRight : LocalEdge → LocalSite
  | Sum.inl _ => localFirst 1
  | Sum.inr (Sum.inl p) => localThird p 1
  | Sum.inr (Sum.inr (p, t)) => localThird p t

def edgeNegative {n r : ℕ} (F : Bonds n r) (e : Fin r) : Bool := decide (F.weight e < 0)

end ContinuumCoulomb.ContactMediator

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactMediatorGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Independent prescribed lengths for the exact nineteen local edges
identified with the actual iterated mediator graph. -/

noncomputable section
namespace ContinuumCoulomb.ContactMediator

abbrev ContactEdge := Fin 9 ⊕ (Unit ⊕ Fin 9)

def leftEdge (k : Fin 9) : LocalEdge :=
  ![Sum.inr (Sum.inr (Sum.inr (0, 0), 0)),
    Sum.inr (Sum.inl (Sum.inr (0, 0))),
    Sum.inr (Sum.inr (Sum.inr (0, 0), 1)),
    Sum.inr (Sum.inr (Sum.inl 0, 0)),
    Sum.inr (Sum.inl (Sum.inl 0)),
    Sum.inr (Sum.inr (Sum.inl 0, 1)),
    Sum.inr (Sum.inr (Sum.inr (0, 1), 1)),
    Sum.inr (Sum.inl (Sum.inr (0, 1))),
    Sum.inr (Sum.inr (Sum.inr (0, 1), 0))] k

def rightEdge (k : Fin 9) : LocalEdge :=
  ![Sum.inr (Sum.inr (Sum.inr (1, 1), 0)),
    Sum.inr (Sum.inl (Sum.inr (1, 1))),
    Sum.inr (Sum.inr (Sum.inr (1, 1), 1)),
    Sum.inr (Sum.inr (Sum.inl 1, 1)),
    Sum.inr (Sum.inl (Sum.inl 1)),
    Sum.inr (Sum.inr (Sum.inl 1, 0)),
    Sum.inr (Sum.inr (Sum.inr (1, 0), 1)),
    Sum.inr (Sum.inl (Sum.inr (1, 0))),
    Sum.inr (Sum.inr (Sum.inr (1, 0), 0))] k

def edgeAt : ContactEdge → LocalEdge :=
  Sum.elim leftEdge (Sum.elim (fun _ => Sum.inl ()) rightEdge)

def edgeIndex : LocalEdge → ContactEdge
  | Sum.inl _ => Sum.inr (Sum.inl ())
  | Sum.inr (Sum.inl (Sum.inl s)) =>
      if s = 0 then Sum.inl 4 else Sum.inr (Sum.inr 4)
  | Sum.inr (Sum.inl (Sum.inr (s, u))) =>
      if s = 0 then Sum.inl (if u = 0 then 1 else 7)
      else Sum.inr (Sum.inr (if u = 0 then 7 else 1))
  | Sum.inr (Sum.inr (Sum.inl s, t)) =>
      if s = 0 then Sum.inl (if t = 0 then 3 else 5)
      else Sum.inr (Sum.inr (if t = 0 then 5 else 3))
  | Sum.inr (Sum.inr (Sum.inr (s, u), t)) =>
      if s = 0 then Sum.inl (if u = 0 then (if t = 0 then 0 else 2)
        else (if t = 0 then 8 else 6))
      else Sum.inr (Sum.inr (if u = 0 then (if t = 0 then 8 else 6)
        else (if t = 0 then 0 else 2)))

def contactEdgeEquiv : ContactEdge ≃ LocalEdge where
  toFun := edgeAt
  invFun := edgeIndex
  left_inv := by
    rintro (k | (⟨⟩ | k))
    · fin_cases k <;> rfl
    · rfl
    · fin_cases k <;> rfl
  right_inv := by
    rintro (⟨⟩ | (p | ⟨p, t⟩))
    · rfl
    · cases p with
      | inl s => fin_cases s <;> rfl
      | inr su =>
        rcases su with ⟨s, u⟩
        fin_cases s <;> fin_cases u <;> rfl
    · cases p with
      | inl s => fin_cases s <;> fin_cases t <;> rfl
      | inr su =>
        rcases su with ⟨s, u⟩
        fin_cases s <;> fin_cases u <;> fin_cases t <;> rfl

end ContinuumCoulomb.ContactMediator

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

abbrev Environment := ℕ × (List ℚ × ℚ)

def lengthAt (e : Environment) (k : ℕ) : ℚ := (e.2.1.drop k).headD 1

def residual (e : Environment) (h : ℝ) : ℝ :=
  adjustedContactSpan (fun k => (lengthAt e k : ℝ)) h - (e.2.2 : ℝ)

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

def tolerance (e : Environment) : ℚ := 1 / ((e.1 : ℚ) + 1)

def argument (e : Environment) (n : ℕ) : BisectionProgram.Input Environment :=
  (n, (e, (tolerance e, ((2 / 5 : ℚ), (3 / 4 : ℚ)))))

def refinedEnvironment (e : Environment) : Environment := (16 * (e.1 + 1), e.2)

def iterations (e : Environment) : ℕ := 64 * (e.1 + 1)

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

def stepY (h : ℚ) (k : ℕ) : ℚ :=
  if k = 2 ∨ k = 3 then h else if k = 5 ∨ k = 6 then -h else 0

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

abbrev Input := ℕ × (Bool × (ℚ × (List ℚ × List ℚ)))

def span (negative : Bool) (central : ℚ) : ℚ :=
  if negative then 17 / 2 else (17 - central) / 2

def origin (negative : Bool) (central : ℚ) : ℚ :=
  if negative then 17 / 2 else (17 + central) / 2

def leftEnvironment (x : Input) : Environment :=
  (x.1, (x.2.2.2.1, span x.2.1 x.2.2.1))

def rightEnvironment (x : Input) : Environment :=
  (x.1, (x.2.2.2.2, span x.2.1 x.2.2.1))

def leftLengths (x : Input) (k : ℕ) : ℝ := lengthAt (leftEnvironment x) k
def rightLengths (x : Input) (k : ℕ) : ℝ := lengthAt (rightEnvironment x) k

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

def input (P : ℕ) (negative : Bool) (ℓ : LocalEdge → ℚ) : ContactRationalGadget.Input :=
  (P, (negative, (ℓ (Sum.inl ()),
    (List.ofFn (fun k : Fin 9 => ℓ (leftEdge k)),
      List.ofFn (fun k : Fin 9 => ℓ (rightEdge k))))))

end ContinuumCoulomb.ContactRationalLocal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactMediatorLinks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The contact adjacency is exactly the edge relation of the actual
nineteen-link gadget, including the signed central attachment. -/

namespace ContinuumCoulomb.ContactMediator
open MediatorIteration

def samePair {α : Type*} (a b c d : α) : Prop :=
  (a = c ∧ b = d) ∨ (a = d ∧ b = c)

def contactPair (negative : Bool) (a : LocalEdge) (x y : ContactGadgetSite) : Prop :=
  samePair (localToContact (localLeft (if negative then 0 else 1) a))
    (localToContact (localRight a)) x y

end ContinuumCoulomb.ContactMediator

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactGrid
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rigid placements of the fixed contact strip on the square lattice.
Reversing an original edge reflects its axial coordinate; this keeps its
internal points in the same canonical strip. -/

noncomputable section
namespace ContinuumCoulomb

/-- The original square-lattice vertices are spaced seventeen units apart. -/
def contactGridPoint (a : ℤ × ℤ) : ContactPoint :=
  contactPoint (17 * a.1) (17 * a.2)

def contactReflect (p : ContactPoint) : ContactPoint := contactPoint (17 - p 0) (p 1)

def contactHorizontal (a : ℤ × ℤ) (p : ContactPoint) : ContactPoint :=
  contactPoint (17 * a.1 + p 0) (17 * a.2 + p 1)

def contactVertical (a : ℤ × ℤ) (p : ContactPoint) : ContactPoint :=
  contactPoint (17 * a.1 - p 1) (17 * a.2 + p 0)

def ContactStripSite.reflect (p : ContactStripSite) : ContactStripSite where
  axial := 17 - p.axial
  transverse := p.transverse
  axial_lower := by linarith [p.axial_upper]
  axial_upper := by linarith [p.axial_lower]
  transverse_lower := p.transverse_lower
  transverse_upper := p.transverse_upper
  off_axis_lower := by intro h; linarith [p.off_axis_upper h]
  off_axis_upper := by intro h; linarith [p.off_axis_lower h]

@[simp] theorem contactReflect_strip (p : ContactStripSite) :
    contactReflect (contactPoint p.axial p.transverse) =
      contactPoint p.reflect.axial p.reflect.transverse := rfl

/-- The canonical key of a lattice edge consists of its direction and its
lower/left endpoint. The final Boolean records the input orientation. -/
structure ContactGridEdge where
  vertical : Bool
  anchor : ℤ × ℤ
  reversed : Bool
  deriving DecidableEq

def ContactGridEdge.key (e : ContactGridEdge) : Bool × (ℤ × ℤ) := (e.vertical, e.anchor)

def ContactGridEdge.upper (e : ContactGridEdge) : ℤ × ℤ :=
  if e.vertical then (e.anchor.1, e.anchor.2 + 1) else (e.anchor.1 + 1, e.anchor.2)

def ContactGridEdge.left (e : ContactGridEdge) : ℤ × ℤ :=
  if e.reversed then e.upper else e.anchor

def ContactGridEdge.right (e : ContactGridEdge) : ℤ × ℤ :=
  if e.reversed then e.anchor else e.upper

def ContactGridEdge.place (e : ContactGridEdge) (p : ContactPoint) : ContactPoint :=
  let p' := if e.reversed then contactReflect p else p
  if e.vertical then contactVertical e.anchor p' else contactHorizontal e.anchor p'

@[simp] theorem ContactGridEdge.place_zero (e : ContactGridEdge) :
    e.place (contactPoint 0 0) = contactGridPoint e.left := by
  rcases e with ⟨vertical, ⟨a, b⟩, reversed⟩
  cases vertical <;> cases reversed <;> ext i <;> fin_cases i <;>
    simp [ContactGridEdge.place, ContactGridEdge.left, ContactGridEdge.upper,
      contactReflect, contactHorizontal, contactVertical, contactGridPoint, contactPoint] <;> ring

@[simp] theorem ContactGridEdge.place_end (e : ContactGridEdge) :
    e.place (contactPoint 17 0) = contactGridPoint e.right := by
  rcases e with ⟨vertical, ⟨a, b⟩, reversed⟩
  cases vertical <;> cases reversed <;> ext i <;> fin_cases i <;>
    simp [ContactGridEdge.place, ContactGridEdge.right, ContactGridEdge.upper,
      contactReflect, contactHorizontal, contactVertical, contactGridPoint, contactPoint] <;> ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactSourceGrid
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every edge of the actual signed square-lattice source has a canonical
geometric strip, and the source's simple-edge promise makes these strips
pairwise distinct. -/

noncomputable section
namespace ContinuumCoulomb

theorem natAbs_one_cases {a : ℤ} (h : a.natAbs = 1) : a = 1 ∨ a = -1 := by
  exact Int.natAbs_eq_natAbs_iff.mp (by simpa using h)

theorem exists_contactGridEdge (p q : ℤ × ℤ)
    (h : (p.1 - q.1).natAbs + (p.2 - q.2).natAbs = 1) :
    ∃ e : ContactGridEdge, e.left = p ∧ e.right = q := by
  have hx : (p.1 - q.1).natAbs = 0 ∨ (p.1 - q.1).natAbs = 1 := by omega
  rcases hx with hx | hx
  · have hxeq : p.1 = q.1 := sub_eq_zero.mp (Int.natAbs_eq_zero.mp hx)
    have hy : (p.2 - q.2).natAbs = 1 := by omega
    rcases natAbs_one_cases hy with hy | hy
    · refine ⟨⟨true, q, true⟩, ?_, ?_⟩
      · apply Prod.ext <;> simp [ContactGridEdge.left, ContactGridEdge.upper] <;> omega
      · simp [ContactGridEdge.right]
    · refine ⟨⟨true, p, false⟩, ?_, ?_⟩
      · simp [ContactGridEdge.left]
      · apply Prod.ext <;> simp [ContactGridEdge.right, ContactGridEdge.upper] <;> omega
  · have hy : (p.2 - q.2).natAbs = 0 := by omega
    have hyeq : p.2 = q.2 := sub_eq_zero.mp (Int.natAbs_eq_zero.mp hy)
    rcases natAbs_one_cases hx with hx | hx
    · refine ⟨⟨false, q, true⟩, ?_, ?_⟩
      · apply Prod.ext <;> simp [ContactGridEdge.left, ContactGridEdge.upper] <;> omega
      · simp [ContactGridEdge.right]
    · refine ⟨⟨false, p, false⟩, ?_, ?_⟩
      · simp [ContactGridEdge.left]
      · apply Prod.ext <;> simp [ContactGridEdge.right, ContactGridEdge.upper] <;> omega

def SquareLatticeHeisenberg.contactEdge (F : SquareLatticeHeisenberg) (e : Fin F.edges) :
    ContactGridEdge :=
  (exists_contactGridEdge (F.coordinate (F.left e)) (F.coordinate (F.right e)) (F.adjacent e)).choose

@[simp] theorem SquareLatticeHeisenberg.contactEdge_left (F : SquareLatticeHeisenberg)
    (e : Fin F.edges) : (F.contactEdge e).left = F.coordinate (F.left e) :=
  (exists_contactGridEdge _ _ (F.adjacent e)).choose_spec.1

@[simp] theorem SquareLatticeHeisenberg.contactEdge_right (F : SquareLatticeHeisenberg)
    (e : Fin F.edges) : (F.contactEdge e).right = F.coordinate (F.right e) :=
  (exists_contactGridEdge _ _ (F.adjacent e)).choose_spec.2

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactGlobal
attribute [-simp] _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gluing the independently adjusted nineteen-link gadgets along the
actual original lattice vertices. All fresh sites retain their source-edge
label under the explicit final-graph permutation. -/

noncomputable section
namespace ContinuumCoulomb.ContactMediator
open MediatorIteration

abbrev GlobalSite (d : SquareLatticeHeisenberg) :=
  Fin (d.vertices + d.edges * 2 + d.edges * 2 * 2 + (d.edges * 2 + d.edges * 2 * 2) * 2)

abbrev GlobalEdge (d : SquareLatticeHeisenberg) :=
  Fin (d.edges + ((d.edges * 2 + d.edges * 2 * 2) + (d.edges * 2 + d.edges * 2 * 2) * 2))

def joinedPosition (d : SquareLatticeHeisenberg)
    (P : Fin d.edges → LocalSite → ContactPoint) :
    Fin d.vertices ⊕ (Fin d.edges × LocalInternal) → ContactPoint
  | Sum.inl i => contactGridPoint (d.coordinate i)
  | Sum.inr (e, u) => (d.contactEdge e).place (P e (Sum.inr u))

def globalPosition (d : SquareLatticeHeisenberg)
    (P : Fin d.edges → LocalSite → ContactPoint) (i : GlobalSite d) : ContactPoint :=
  joinedPosition d P ((siteEquiv d.vertices d.edges).symm i)

@[simp] theorem globalPosition_old (d : SquareLatticeHeisenberg)
    (P : Fin d.edges → LocalSite → ContactPoint) (i : Fin d.vertices) :
    globalPosition d P (siteEquiv d.vertices d.edges (Sum.inl i)) =
      contactGridPoint (d.coordinate i) := by
  simp [globalPosition, joinedPosition]

@[simp] theorem globalPosition_internal (d : SquareLatticeHeisenberg)
    (P : Fin d.edges → LocalSite → ContactPoint) (e : Fin d.edges) (u : LocalInternal) :
    globalPosition d P (siteEquiv d.vertices d.edges (Sum.inr (e, u))) =
      (d.contactEdge e).place (P e (Sum.inr u)) := by
  simp [globalPosition, joinedPosition]

end ContinuumCoulomb.ContactMediator

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactGlobalSeparation
attribute [-simp] _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform all-site and nonedge separation for the actual final graph. -/

noncomputable section
namespace ContinuumCoulomb.ContactMediator
open MediatorIteration

@[simp] theorem localVertex_old_zero {n r : ℕ} (a b : Fin n) (e : Fin r) :
    localVertex a b e (localOld 0) = siteEquiv n r (Sum.inl a) := by
  simp [localVertex, localOld]

@[simp] theorem localVertex_old_one {n r : ℕ} (a b : Fin n) (e : Fin r) :
    localVertex a b e (localOld 1) = siteEquiv n r (Sum.inl b) := by
  simp [localVertex, localOld]

@[simp] theorem localVertex_internal {n r : ℕ} (a b : Fin n) (e : Fin r) (u : LocalInternal) :
    localVertex a b e (Sum.inr u) = siteEquiv n r (Sum.inr (e, u)) := rfl

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

def rationalPlace (e : ContactGridEdge) (p : ℚ × ℚ) : ℚ × ℚ :=
  let q := if e.reversed then (17 - p.1, p.2) else p
  if e.vertical then (17 * e.anchor.1 - q.2, 17 * e.anchor.2 + q.1)
  else (17 * e.anchor.1 + q.1, 17 * e.anchor.2 + q.2)

end ContinuumCoulomb.ContactRationalGlobal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactCanonicalEdge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The canonical strip record has an explicit finite computation from its
two lattice endpoints. This identifies the selected record with the record used by rational
coordinate programs. -/

namespace ContinuumCoulomb

def canonicalContactEdge (p q : ℤ × ℤ) : ContactGridEdge :=
  let vertical := decide (p.1 = q.1)
  let forward := if vertical then decide (p.2 < q.2) else decide (p.1 < q.1)
  { vertical := vertical, anchor := if forward then p else q, reversed := !forward }

end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_ContactRationalPlaceProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact strip placement uses only rational arithmetic and the two
computed orientation bits. It preserves the original lattice endpoints. -/

namespace ContinuumCoulomb.ContactRationalPlaceProgram
open ExactQuantumFactoring.BitStackProgram

abbrev Input := ContactGridEdge × (ℚ × ℚ)

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

abbrev Input := ((ℤ × ℤ) × (ℤ × ℤ)) × ContactRationalGadget.Input

def placement (x : Input) : ContactGridEdge := canonicalContactEdge x.1.1 x.1.2

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

abbrev EdgeInput := ContactPlacedGadgetProgram.Input

def defaultEdge : EdgeInput := (((0, 0), (1, 0)), (0, (false, (1, ([], [])))))

abbrev LoopInput := ℕ × List EdgeInput

def firstSites : List ContactGadgetSite :=
  List.ofFn (fun s : Fin 2 => localToContact (localFirst s))

def secondSites : List ContactGadgetSite :=
  List.ofFn (fun i : Fin 4 =>
    let st : Fin 2 × Fin 2 := finProdFinEquiv.symm i
    localToContact (localSecond st.1 st.2))

def thirdFirstSites : List ContactGadgetSite :=
  List.ofFn (fun i : Fin 4 =>
    let st : Fin 2 × Fin 2 := finProdFinEquiv.symm i
    localToContact (localThird (Sum.inl st.1) st.2))

def thirdSecondSites : List ContactGadgetSite :=
  List.ofFn (fun sut : Fin 8 =>
    let st : Fin 4 × Fin 2 := finProdFinEquiv.symm sut
    let su : Fin 2 × Fin 2 := finProdFinEquiv.symm st.1
    localToContact (localThird (Sum.inr su) st.2))

def oldPoint (p : ℤ × ℤ) : ℚ × ℚ := (17 * (p.1 : ℚ), 17 * (p.2 : ℚ))

abbrev Input := List (ℤ × ℤ) × List EdgeInput

end ContinuumCoulomb.ContactGeometryBlockProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactGeometryBlockSemantics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The serialized blocks are the original iterated graph's vertex array,
through the explicit site permutation. No graph relabeling is assumed. -/

noncomputable section
namespace ContinuumCoulomb.ContactGeometryBlockProgram
open ContactMediator

def literalEdge (d : SquareLatticeHeisenberg) (P : ℕ)
    (ℓ : ContactMediator.GlobalEdge d → ℚ) (e : Fin d.edges) : EdgeInput :=
  ((d.coordinate (d.left e), d.coordinate (d.right e)),
    ContactRationalLocal.input P (ContactMediator.edgeNegative d.bonds e)
      (fun a => ℓ (ContactMediator.encodeEdge d.edges e a)))

def literalInput (d : SquareLatticeHeisenberg) (P : ℕ)
    (ℓ : ContactMediator.GlobalEdge d → ℚ) : Input :=
  (List.ofFn d.coordinate, List.ofFn (literalEdge d P ℓ))

def firstIndex (d : SquareLatticeHeisenberg) (i : Fin (d.edges * 2)) : GlobalSite d :=
  siteEquiv d.vertices d.edges (Sum.inr (i.divNat, Sum.inl i.modNat))

def secondIndex (d : SquareLatticeHeisenberg) (i : Fin (d.edges * 4)) : GlobalSite d :=
  let st : Fin 2 × Fin 2 := finProdFinEquiv.symm i.modNat
  siteEquiv d.vertices d.edges (Sum.inr (i.divNat, Sum.inr (Sum.inl st)))

def thirdFirstIndex (d : SquareLatticeHeisenberg) (i : Fin (d.edges * 4)) : GlobalSite d :=
  let st : Fin 2 × Fin 2 := finProdFinEquiv.symm i.modNat
  siteEquiv d.vertices d.edges (Sum.inr (i.divNat, Sum.inr (Sum.inr (Sum.inl st.1, st.2))))

def thirdSecondIndex (d : SquareLatticeHeisenberg) (i : Fin (d.edges * 8)) : GlobalSite d :=
  let st : Fin 4 × Fin 2 := finProdFinEquiv.symm i.modNat
  let su : Fin 2 × Fin 2 := finProdFinEquiv.symm st.1
  siteEquiv d.vertices d.edges (Sum.inr (i.divNat, Sum.inr (Sum.inr (Sum.inr su, st.2))))

end ContinuumCoulomb.ContactGeometryBlockProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactEdgeNumber
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Natural-number formulas for the exact final-edge permutation. These
are the indices used to fetch calibrated lengths from the emitted list. -/

namespace ContinuumCoulomb.ContactMediator

def pathNumber (r e : ℕ) : LocalPath → ℕ
  | Sum.inl s => e * 2 + s.val
  | Sum.inr (s, t) => r * 2 + (e * 2 + s.val) * 2 + t.val

def edgeNumber (r e : ℕ) : LocalEdge → ℕ
  | Sum.inl _ => e
  | Sum.inr (Sum.inl p) => r + pathNumber r e p
  | Sum.inr (Sum.inr (p, t)) => r + (r * 2 + r * 2 * 2) + pathNumber r e p * 2 + t.val

end ContinuumCoulomb.ContactMediator

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

abbrev Input := ℕ × ℕ

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

abbrev Input := ℕ × (ℕ × (ℕ × (Bool × List ℚ)))

def lookup (x : Input) (a : LocalEdge) : ℚ :=
  (x.2.2.2.2.drop (edgeNumber x.2.1 x.2.2.1 a)).headD 1

def record (x : Input) : ContactRationalGadget.Input :=
  (x.1, (x.2.2.2.1, (lookup x (Sum.inl ()),
    (List.ofFn (fun k : Fin 9 => lookup x (leftEdge k)),
      List.ofFn (fun k : Fin 9 => lookup x (rightEdge k))))))

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

abbrev Input := ℕ × (List (ℤ × ℤ) × (List MediatorListProgram.Bond × List ℚ))

abbrev LoopInput := ℕ × Input

def bond (x : LoopInput) : MediatorListProgram.Bond :=
  (x.2.2.2.1.drop x.1).headD MediatorListProgram.zeroBond

def edge (x : LoopInput) : ContactPlacedGadgetProgram.Input :=
  (((x.2.2.1.drop (bond x).1).headD (0, 0),
      (x.2.2.1.drop (bond x).2.1).headD (0, 0)),
    ContactLocalInputProgram.record (x.2.1, (x.2.2.2.1.length,
      (x.1, (decide ((bond x).2.2 < 0), x.2.2.2.2)))))

def edges (x : Input) : List ContactPlacedGadgetProgram.Input :=
  (List.range x.2.2.1.length).map (fun i => edge (i, x))

def scalePoint (x : ℚ × (ℚ × ℚ)) : ℚ × ℚ := (x.1 * x.2.1, x.1 * x.2.2)

end ContinuumCoulomb.ContactSourceInputProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactSourceInputCorrectness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The raw-list program uses exactly the original source endpoints and
exactly the calibrated lengths of the final mediator edges. -/

noncomputable section
namespace ContinuumCoulomb.ContactSourceInputProgram
open ContactMediator

def literalInput (d : SquareLatticeHeisenberg) (P : ℕ) (ℓ : GlobalEdge d → ℚ) : Input :=
  (P, (List.ofFn d.coordinate, (d.bonds.toList, List.ofFn ℓ)))

end ContinuumCoulomb.ContactSourceInputProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_RationalLogScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A rational approximation to the logarithmic contact scale. Only a fixed
rational approximation to `log 2` is used. The input-dependent operation is
the bit length of a natural power, so no real logarithm is queried at runtime. -/

noncomputable section
namespace ContinuumCoulomb.RationalLogScale

def value (c : ℚ) (k N : ℕ) : ℚ := c * ((N ^ k).bits.length : ℚ)

end ContinuumCoulomb.RationalLogScale

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CalibrationRationalBracket
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational endpoints lie inside the permitted contact interval and outside
the smaller interval used for the analytic sign estimates. -/

noncomputable section
namespace ContinuumCoulomb.CalibrationRationalBracket

def endpoints (ε q : ℚ) : ℚ × ℚ := ((1 - ε / 2) * q, (1 + ε / 2) * q)

end ContinuumCoulomb.CalibrationRationalBracket

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

theorem subtract_pair_function {X : Type*} (f g : X → ℚ) :
    ((fun q : ℚ × ℚ => q.1 - q.2) ∘ (fun x => (f x, g x))) =
      (fun x => f x - g x) := rfl

end ContinuumCoulomb.CalibratedEvaluation

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

abbrev ScheduledInput := Environment × (ℚ × ℚ)

end ContinuumCoulomb.CalibratedEvaluation

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

abbrev Input := ℕ × (ℕ × ℚ)

def queryBound (k A N : ℕ) : ℕ := 2 * k * N + N ^ A + 1

def environment (k A B : ℕ) (x : Input) : CalibratedEvaluation.Environment :=
  ((queryBound k A x.1, x.2.1), (x.1 ^ k, (((x.1 ^ B : ℕ) : ℚ)⁻¹, x.2.2)))

def interval (ε c : ℚ) (k N : ℕ) : ℚ × ℚ :=
  CalibrationRationalBracket.endpoints ε (RationalLogScale.value c k N)

end ContinuumCoulomb.AutomaticCalibration

end

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

def spacing (c : ℚ) (k N : ℕ) : ℚ := RationalLogScale.value c k N

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

abbrev Environment := ℕ × ℕ
abbrev Input := Environment × List ℚ

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

abbrev Data := List (ℤ × ℤ) × (List MediatorListProgram.Bond × List ℚ)
abbrev Input := ℕ × (AutomaticCalibrationList.Environment × Data)

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

def graphInput (d : SquareLatticeHeisenberg) (N P H : ℕ)
    (K : GlobalEdge d → ℚ) : Input :=
  (H, ((N, P), (List.ofFn d.coordinate, (d.bonds.toList, List.ofFn K))))

end ContinuumCoulomb.CalibratedContactProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CenteredGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete finite family of lattice cubes tiles the enclosing rectangular
slab, including its boundary. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

def centeredGridIndices (r : Fin 3 → ℕ) : Finset (Fin 3 → ℤ) :=
  Fintype.piFinset (fun i => Finset.Icc (-(r i : ℤ)) (r i : ℤ))

theorem mem_centeredGridIndices (r : Fin 3 → ℕ) (k : Fin 3 → ℤ) :
    k ∈ centeredGridIndices r ↔ ∀ i, -(r i : ℤ) ≤ k i ∧ k i ≤ (r i : ℤ) := by
  simp only [centeredGridIndices,Fintype.mem_piFinset,Finset.mem_Icc]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CenteredGaussLabels
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
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

def integers (R : ℕ) : List ℤ :=
  (List.range (2*R+1)).map (fun j : ℕ => (j:ℤ)-(R:ℤ))
def signs : List Signs :=
  [false,true] ×ˢ ([false,true] ×ˢ [false,true])

theorem mem_integers (R : ℕ) (j : ℤ) : j ∈ integers R ↔ -(R:ℤ) ≤ j ∧ j ≤ R := by
  constructor
  · intro h
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp h
    have hi' := List.mem_range.mp hi
    omega
  · rintro ⟨hl,hu⟩
    refine List.mem_map.mpr ⟨(j+(R:ℤ)).toNat,List.mem_range.mpr ?_,?_⟩ <;> omega

theorem integers_nodup (R : ℕ) : (integers R).Nodup :=
  (List.nodup_range).map (by
    intro a b h
    have he : (a:ℤ)-(R:ℤ) = (b:ℤ)-(R:ℤ) := h
    omega)

theorem signs_mem (s : Signs) : s ∈ signs := by
  rcases s with ⟨a,b,c⟩
  cases a <;> cases b <;> cases c <;> simp [signs]

end ContinuumCoulomb.CenteredGaussLabels

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_CenteredGaussProgram
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
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

theorem fold_append {α : Type} (xs : List (List α)) (ys : List α) :
    xs.foldl (fun ys x => ys++x) ys = ys++xs.flatten := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih => simp only [List.foldl_cons,ih,List.flatten_cons,List.append_assoc]

end ContinuumCoulomb.CenteredGaussLabels

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

def factor (rho N : ℕ) : ℚ := (rho:ℚ)/(8*(N:ℚ)^3)

end ContinuumCoulomb.PhysicalNuclearProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CalibrationMesh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact compatibility between polynomial hopping amplification and the
equal masses of the unit-nucleus Gauss mesh. -/

namespace ContinuumCoulomb.CalibrationMesh

def base (n : ℕ) : ℕ := n^30
def mesh (n k : ℕ) : ℕ := n^(10*k)
def prefactor (rho : ℕ) : ℚ := 8/(rho:ℚ)
def amplification (rho n k : ℕ) : ℚ := prefactor rho * (base n:ℚ)^k

end ContinuumCoulomb.CalibrationMesh

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

def decode (i : GaussLatticeIndex) : TransformedGauss.Label :=
  ((i.1 0,(i.1 1,i.1 2)),(decide (i.2 0=1),(decide (i.2 1=1),decide (i.2 2=1))))

theorem bit_value (v : Fin 2) : (if decide (v=1) then (1:Fin 2) else 0) = v := by
  fin_cases v <;> decide

@[simp] theorem index_decode (i : GaussLatticeIndex) :
    RationalGaussNodes.index (decode i).1 (decode i).2 = i := by
  apply Prod.ext
  · funext a
    fin_cases a <;> rfl
  · funext a
    fin_cases a <;> exact bit_value _

@[simp] theorem decode_index (l : TransformedGauss.Label) :
    decode (RationalGaussNodes.index l.1 l.2) = l := by
  apply TransformedGauss.index_injective
  exact index_decode _

def indexEquiv : TransformedGauss.Label ≃ GaussLatticeIndex where
  toFun l := RationalGaussNodes.index l.1 l.2
  invFun := decode
  left_inv := decode_index
  right_inv := index_decode

end ContinuumCoulomb.CenteredGaussLabels

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PrefactorCalibration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed positive rational prefactor in the physical amplification is
absorbed into the requested edge weight. This retains the proved evaluator
and bisection, including their polynomial running times. -/

noncomputable section
namespace ContinuumCoulomb.PrefactorCalibration

def adjustedWeight (a K : ℚ) : ℚ := K / a^2
def precision (C P : ℕ) : ℕ := C*(P+1)
def input (a : ℚ) (C : ℕ) (x : AutomaticCalibration.Input) : AutomaticCalibration.Input :=
  (x.1,(precision C x.2.1,adjustedWeight a x.2.2))

end ContinuumCoulomb.PrefactorCalibration

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

theorem gauss_point_injective {h : ℝ} (hh : 0 < h) :
    Function.Injective (gaussLatticePoint h) := by
  intro a b hab
  by_contra hne
  have hs := gaussLatticePoint_separation hh a b hne
  rw [hab,sub_self,norm_zero] at hs
  linarith

end CenteredGaussLabels
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_SourceContactProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal composition from the encoded source to the calibrated
contact coordinates. The signed retained bonds determine the geometric
strips; the final positive bond list supplies their nineteen target weights. -/

namespace ContinuumCoulomb.SourceContactProgram
open ExactQuantumFactoring.BitStackProgram

def size (d : BinaryHeisenberg) : ℕ := SourceMetadataProgram.size d + 1

end ContinuumCoulomb.SourceContactProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumEvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Norm preservation for the actual verifier evolution. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators

def qmaApplyMatrix {n : ℕ}
    (M : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ)
    (u : EuclideanSpace ℂ (SourceSpinBasis n)) : EuclideanSpace ℂ (SourceSpinBasis n) :=
  WithLp.toLp 2 (M.mulVec (fun s => u s))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumAncilla
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact witness embedding into the zero-ancilla subspace. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators

def QMAAncillaZero (c : QMACircuit) (s : SourceSpinBasis (c.work+1)) : Prop :=
  ∀ i : Fin (c.work+1), c.witness ≤ i.val → s i = 0

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPrefix
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact circuit prefixes and their unitary changes of coordinates. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix

@[simp] theorem qmaApplyMatrix_one {n : ℕ} (u : EuclideanSpace ℂ (SourceSpinBasis n)) :
    qmaApplyMatrix 1 u = u := by
  ext s
  simp [qmaApplyMatrix]

def qmaPrefixMatrix (c : QMACircuit) (t : ℕ) :
    Matrix (SourceSpinBasis (c.work+1)) (SourceSpinBasis (c.work+1)) ℂ :=
  (c.gates.take t).foldl (fun M g => qmaGateMatrix c.work g*M) 1

@[simp] theorem qmaPrefixMatrix_zero (c : QMACircuit) : qmaPrefixMatrix c 0 = 1 := rfl

@[simp] theorem qmaPrefixMatrix_length (c : QMACircuit) :
    qmaPrefixMatrix c c.gates.length = qmaCircuitMatrix c := by
  simp [qmaPrefixMatrix,qmaCircuitMatrix]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumMask
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.ContinuumCoulomb.qmaApplyMatrix_one _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_length _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate projections for the initial and output penalties. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

def qmaMask {n : ℕ} (p : SourceSpinBasis n → Prop) :
    EuclideanSpace ℂ (SourceSpinBasis n) →ₗ[ℂ] EuclideanSpace ℂ (SourceSpinBasis n) := by
  classical
  exact {
    toFun := fun u => WithLp.toLp 2 (fun s => if p s then u s else 0)
    map_add' := by intro u v; ext s; by_cases hs : p s <;> simp [hs]
    map_smul' := by intro a u; ext s; by_cases hs : p s <;> simp [hs] }

@[simp] theorem qmaMask_apply {n : ℕ} (p : SourceSpinBasis n → Prop)
    (u : EuclideanSpace ℂ (SourceSpinBasis n)) (s : SourceSpinBasis n) :
    qmaMask p u s = if p s then u s else 0 := rfl

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFiniteHistory
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite clock coordinates and their exact Euclidean mass. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators

abbrev QMAHistoryBasis (c : QMACircuit) :=
  Fin (c.gates.length+1) × SourceSpinBasis (c.work+1)

def qmaClockIndex (c : QMACircuit) (t : ℕ) : Fin (c.gates.length+1) :=
  ⟨min t c.gates.length,Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

def qmaHistoryFromVector (c : QMACircuit) (u : QMAHistoryBasis c → ℂ)
    (t : ℕ) : EuclideanSpace ℂ (SourceSpinBasis (c.work+1)) :=
  WithLp.toLp 2 (fun s => u (qmaClockIndex c t,s))

@[simp] theorem qmaClockIndex_fin (c : QMACircuit) (t : Fin (c.gates.length+1)) :
    qmaClockIndex c t.val = t := by
  apply Fin.ext
  exact Nat.min_eq_left (Nat.le_of_lt_succ t.isLt)

@[simp] theorem qmaHistoryFromVector_fin (c : QMACircuit)
    (u : QMAHistoryBasis c → ℂ) (t : Fin (c.gates.length+1)) (s : SourceSpinBasis (c.work+1)) :
    qmaHistoryFromVector c u t.val s = u (t,s) := by
  simp [qmaHistoryFromVector]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPinnedClock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two fixed end bits make all clock transitions uniform, including the
empty circuit. Only adjacent-pair and endpoint penalties are used. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

def QMALegalClock (T : ℕ) (s : SourceSpinBasis (T+2)) : Prop :=
  Antitone s ∧ s 0 = 1 ∧ s (Fin.last (T+1)) = 0

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumClockTransition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A guarded single-bit clock update preserves the legal clock sector.
The guard inspects only the two adjacent clock bits. -/

noncomputable section
namespace ContinuumCoulomb

def qmaClockLeft (T : ℕ) (i : Fin T) : Fin (T+2) := ⟨i.val,by omega⟩
def qmaClockRight (T : ℕ) (i : Fin T) : Fin (T+2) := ⟨i.val+2,by omega⟩

def QMAClockGuard (T : ℕ) (i : Fin T) (s : SourceSpinBasis (T+2)) : Prop :=
  s (qmaClockLeft T i) = 1 ∧ s (qmaClockRight T i) = 0

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumLocalLift
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact tensor-local operators, with explicit finite supports. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped Kronecker

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev QMASupportBasis (S : Finset ι) := (i : {i // i ∈ S}) → Fin 2
abbrev QMASpectatorBasis (S : Finset ι) := (i : {i // i ∉ S}) → Fin 2

def qmaSupportSplit (S : Finset ι) :
    (ι → Fin 2) ≃ QMASupportBasis S × QMASpectatorBasis S :=
  Equiv.piEquivPiSubtypeProd (fun i => i ∈ S) (fun _ => Fin 2)

def qmaLocalLift (S : Finset ι) (A : Matrix (QMASupportBasis S) (QMASupportBasis S) ℂ) :
    Matrix (ι → Fin 2) (ι → Fin 2) ℂ :=
  (A ⊗ₖ (1 : Matrix (QMASpectatorBasis S) (QMASpectatorBasis S) ℂ)).submatrix
    (qmaSupportSplit S) (qmaSupportSplit S)

def QMALocalOn (S : Finset ι) (A : Matrix (ι → Fin 2) (ι → Fin 2) ℂ) : Prop :=
  ∃ B : Matrix (QMASupportBasis S) (QMASupportBasis S) ℂ, A = qmaLocalLift S B

theorem qmaLocalLift_add (S : Finset ι) (A B : Matrix (QMASupportBasis S) (QMASupportBasis S) ℂ) :
    qmaLocalLift S (A+B) = qmaLocalLift S A+qmaLocalLift S B := by
  simp [qmaLocalLift,Matrix.add_kronecker,Matrix.submatrix_add]

theorem qmaLocalLift_adjoint (S : Finset ι) (A : Matrix (QMASupportBasis S) (QMASupportBasis S) ℂ) :
    qmaLocalLift S A.conjTranspose = (qmaLocalLift S A).conjTranspose := by
  simp [qmaLocalLift,Matrix.conjTranspose_kronecker,Matrix.conjTranspose_submatrix]

theorem QMALocalOn.add {S : Finset ι} {A B : Matrix (ι → Fin 2) (ι → Fin 2) ℂ}
    (hA : QMALocalOn S A) (hB : QMALocalOn S B) : QMALocalOn S (A+B) := by
  obtain ⟨a,rfl⟩ := hA
  obtain ⟨b,rfl⟩ := hB
  exact ⟨a+b,(qmaLocalLift_add S a b).symm⟩

theorem QMALocalOn.adjoint {S : Finset ι} {A : Matrix (ι → Fin 2) (ι → Fin 2) ℂ}
    (hA : QMALocalOn S A) : QMALocalOn S A.conjTranspose := by
  obtain ⟨a,rfl⟩ := hA
  exact ⟨a.conjTranspose,(qmaLocalLift_adjoint S a).symm⟩

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumLocalTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Tensor products with identity spectators are actual finite-support
operators, with their small matrix given explicitly. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem qmaLocalLift_apply (S : Finset ι)
    (A : Matrix (QMASupportBasis S) (QMASupportBasis S) ℂ) (s t : ι → Fin 2) :
    qmaLocalLift S A s t =
      A (fun i => s i.val) (fun i => t i.val)*
        if (fun i : {i // i ∉ S} => s i.val) = (fun i : {i // i ∉ S} => t i.val) then 1 else 0 := by
  rfl

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumLocalEnlarge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Enlarging an explicit operator support introduces only identity factors. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def qmaSupportExtend (S : Finset ι) (u : QMASupportBasis S) : ι → Fin 2 :=
  fun i => if hi : i ∈ S then u ⟨i,hi⟩ else 0

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumLocalPropagation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every guarded propagation term acts on three clock bits and at most two
computation bits. This is the actual unary-clock operator. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

abbrev QMACircuitQubit (c : QMACircuit) := Fin (c.gates.length+2) ⊕ Fin (c.work+1)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumLocalFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A linear-size explicit interaction family for the verified circuit
Hamiltonian. Its supports contain at most five qubits. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

abbrev QMACircuitTerm (c : QMACircuit) :=
  Fin (c.gates.length+1) ⊕ (Fin 2 ⊕ (Fin (c.work+1) ⊕ (Unit ⊕ Fin c.gates.length)))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumBlockEdges
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit finite list of physical exchanges, with no implicit many-body terms. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {n : ℕ} {κ τ : Type*} [Fintype κ] [Fintype τ]

abbrev QMAFourExchangeIndex (n : ℕ) (κ τ : Type*) :=
  (Fin n × Fin 6) ⊕ ((κ × Fin 4 × Fin 4) ⊕ ((κ × Fin 2 × Fin 3) ⊕ (τ × Fin 3)))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumEntryParity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real and purely imaginary entry parities determine the mediator phase. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

variable {σ : Type*}

def QMAEntryParity (p : Bool) (M : Matrix σ σ ℂ) : Prop :=
  if p = true then ∀ s t, (M s t).re = 0 else ∀ s t, (M s t).im = 0

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumNearestGate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Replacing a gate by an exact bounded-length nearest-neighbor gate sequence. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped Classical

def QMAGate.Adjacent : QMAGate → Prop
  | .controlledNot i j => i+1 = j ∨ j+1 = i
  | _ => True

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumReferenceBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A local Y-eigenbasis for distributing the realification reference qubit. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped Kronecker Classical

def qmaEntryReal {ι : Type*} (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  fun i j => (A i j).re

def qmaEntryImag {ι : Type*} (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  fun i j => (A i j).im

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit consecutive labels for every term in the distributed history. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

abbrev qmaHistoryReferenceWork (c : QMACircuit) : ℕ := 2*c.gates.length+c.work+4

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumReferenceHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual distributed-reference history retains the verifier promise gap. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

abbrev QMAHistoryReferenceBasis (c : QMACircuit) :=
  SourceSpinBasis (qmaHistoryReferenceWork c+1) × (QMACircuitQubit c → Fin 2)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumReferenceLocal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A separate reference qubit adds exactly one site to each original support. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem QMALocalOn.entryReal {S : Finset ι}
    {A : Matrix (ι → Fin 2) (ι → Fin 2) ℂ} (hA : QMALocalOn S A) :
    QMALocalOn S (qmaEntryReal A) := by
  obtain ⟨B,rfl⟩ := hA
  refine ⟨qmaEntryReal B,?_⟩
  ext s t
  simp only [qmaEntryReal,qmaLocalLift_apply]
  split_ifs <;> simp

theorem QMALocalOn.entryImag {S : Finset ι}
    {A : Matrix (ι → Fin 2) (ι → Fin 2) ℂ} (hA : QMALocalOn S A) :
    QMALocalOn S (qmaEntryImag A) := by
  obtain ⟨B,rfl⟩ := hA
  refine ⟨qmaEntryImag B,?_⟩
  ext s t
  simp only [qmaEntryImag,qmaLocalLift_apply]
  split_ifs <;> simp

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumStageStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Consecutive clock anchors within a stage are neighboring columns. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

def QMALabeledColumnNear {width : ℕ} (p q : QMAGate × Fin (width+1)) : Prop :=
  p.2.val ≤ q.2.val+1 ∧ q.2.val ≤ p.2.val+1

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumTaggedSweep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal sparse sweep comes with row and column labels. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

abbrev QMAGridCell (rows width : ℕ) := Fin (rows+1) × Fin (width+1)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumStagePath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Row-labelled stages form bounded-step spatial paths with explicit endpoints. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

def QMAGridTagNear {rows width : ℕ} (p q : QMAGate × QMAGridCell rows width) : Prop :=
  p.2.1.val ≤ q.2.1.val+1 ∧ q.2.1.val ≤ p.2.1.val+1 ∧
    p.2.2.val ≤ q.2.2.val+1 ∧ q.2.2.val ≤ p.2.2.val+1

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumClockCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual unary clock bits stay next to their computation gates with bounded cell occupancy. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

def QMAGridCellsNear {rows width : ℕ} (p q : QMAGridCell rows width) : Prop :=
  p.1.val ≤ q.1.val+1 ∧ q.1.val ≤ p.1.val+1 ∧
    p.2.val ≤ q.2.val+1 ∧ q.2.val ≤ p.2.val+1

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumGridSlots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A bounded cell fiber admits distinct fine-grid slots for all its qubits. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical
variable {Q : Type*} [Fintype Q] {rows width A : ℕ}

def qmaGridFiberSlot (cell : Q → QMAGridCell rows width)
    (h : ∀ p, (Finset.univ.filter (fun q => cell q = p)).card ≤ A)
    (p : QMAGridCell rows width) : {q // cell q = p} ↪ Fin A :=
  (Fintype.equivFin {q // cell q = p}).toEmbedding.trans {
    toFun := fun i => ⟨i.val,lt_of_lt_of_le i.isLt (by
      simpa only [Fintype.card_subtype] using h p)⟩
    inj' := fun _ _ he => Fin.ext (congrArg (fun i : Fin A => i.val) he) }

def qmaGridSlot (cell : Q → QMAGridCell rows width)
    (h : ∀ p, (Finset.univ.filter (fun q => cell q = p)).card ≤ A) (q : Q) : Fin A :=
  qmaGridFiberSlot cell h (cell q) ⟨q,rfl⟩

theorem qmaGridSlot_eq (cell : Q → QMAGridCell rows width)
    (h : ∀ p, (Finset.univ.filter (fun q => cell q = p)).card ≤ A)
    (q : Q) (p : QMAGridCell rows width) (hq : cell q = p) :
    qmaGridSlot cell h q = qmaGridFiberSlot cell h p ⟨q,hq⟩ := by
  subst p
  rfl

theorem qmaGridSlot_injective_on_cell (cell : Q → QMAGridCell rows width)
    (h : ∀ p, (Finset.univ.filter (fun q => cell q = p)).card ≤ A)
    {q r : Q} (hc : cell q = cell r) (hs : qmaGridSlot cell h q = qmaGridSlot cell h r) : q = r := by
  have he : qmaGridFiberSlot cell h (cell r) ⟨q,hc⟩ =
      qmaGridFiberSlot cell h (cell r) ⟨r,rfl⟩ := by
    rw [qmaGridSlot_eq cell h q (cell r) hc] at hs
    exact hs
  exact congrArg Subtype.val ((qmaGridFiberSlot cell h (cell r)).injective he)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumManhattanRoute
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Short, simple lattice paths between the bounded-density fine-grid sites. -/

namespace ContinuumCoulomb

def qmaAxisWalk (a b k : ℕ) : ℕ := if a ≤ b then a+k else a-k

@[simp] theorem qmaAxisWalk_zero (a b : ℕ) : qmaAxisWalk a b 0 = a := by
  simp [qmaAxisWalk]

@[simp] theorem qmaAxisWalk_last (a b : ℕ) : qmaAxisWalk a b (Nat.dist a b) = b := by
  unfold qmaAxisWalk Nat.dist
  split_ifs <;> omega

theorem qmaAxisWalk_bounds (a b k : ℕ) (hk : k ≤ Nat.dist a b) :
    min a b ≤ qmaAxisWalk a b k ∧ qmaAxisWalk a b k ≤ max a b := by
  unfold qmaAxisWalk Nat.dist at *
  split_ifs <;> omega

def qmaManhattanLength (p q : ℕ × ℕ) : ℕ := Nat.dist p.1 q.1+Nat.dist p.2 q.2

def qmaManhattanPoint (p q : ℕ × ℕ) (k : ℕ) : ℕ × ℕ :=
  if k ≤ Nat.dist p.1 q.1 then (qmaAxisWalk p.1 q.1 k,p.2)
  else (q.1,qmaAxisWalk p.2 q.2 (k-Nat.dist p.1 q.1))

@[simp] theorem qmaManhattanPoint_zero (p q : ℕ × ℕ) : qmaManhattanPoint p q 0 = p := by
  simp [qmaManhattanPoint]

@[simp] theorem qmaManhattanPoint_last (p q : ℕ × ℕ) :
    qmaManhattanPoint p q (qmaManhattanLength p q) = q := by
  by_cases h : Nat.dist p.2 q.2 = 0
  · have he := Nat.eq_of_dist_eq_zero h
    simp [qmaManhattanLength,qmaManhattanPoint,he]
  · have hn : ¬qmaManhattanLength p q ≤ Nat.dist p.1 q.1 := by unfold qmaManhattanLength; omega
    simp only [qmaManhattanPoint,ite_eq_right hn]
    simp [qmaManhattanLength]

theorem qmaManhattanPoint_bounds (p q : ℕ × ℕ) (k : ℕ) (hk : k ≤ qmaManhattanLength p q) :
    min p.1 q.1 ≤ (qmaManhattanPoint p q k).1 ∧
    (qmaManhattanPoint p q k).1 ≤ max p.1 q.1 ∧
    min p.2 q.2 ≤ (qmaManhattanPoint p q k).2 ∧
    (qmaManhattanPoint p q k).2 ≤ max p.2 q.2 := by
  by_cases hx : k ≤ Nat.dist p.1 q.1
  · simpa only [qmaManhattanPoint,hx,ite_true, if_true] using
      And.intro (qmaAxisWalk_bounds _ _ _ hx).1
        (And.intro (qmaAxisWalk_bounds _ _ _ hx).2 (And.intro (min_le_left _ _) (le_max_left _ _)))
  · have hy : k-Nat.dist p.1 q.1 ≤ Nat.dist p.2 q.2 := by unfold qmaManhattanLength at hk; omega
    simpa only [qmaManhattanPoint,hx,ite_false, if_false] using
      And.intro (min_le_right _ _)
        (And.intro (le_max_right _ _) (qmaAxisWalk_bounds _ _ _ hy))

end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCrossingPatch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete square-grid subdivision of the nine-edge crossing gadget.
Its four terminals lie on the boundary with their outward directions free. -/

namespace ContinuumCoulomb
open scoped Classical

def qmaCrossingPatchVertex : Fin 6 → ℕ × ℕ := ![(0,6),(6,12),(12,6),(6,0),(4,8),(8,4)]
def qmaCrossingPatchLeft : Fin 9 → Fin 6 := ![4,0,1,2,3,0,1,2,3]
def qmaCrossingPatchRight : Fin 9 → Fin 6 := ![5,4,4,5,5,1,2,3,0]
def qmaCrossingPatchPath : Fin 9 → List (ℕ × ℕ) := ![
  [(4,8),(5,8),(6,8),(7,8),(8,8),(8,7),(8,6),(8,5),(8,4)],
  [(0,6),(1,6),(2,6),(2,7),(2,8),(3,8),(4,8)],
  [(6,12),(6,11),(6,10),(5,10),(4,10),(4,9),(4,8)],
  [(12,6),(11,6),(10,6),(10,5),(10,4),(9,4),(8,4)],
  [(6,0),(6,1),(6,2),(7,2),(8,2),(8,3),(8,4)],
  [(0,6),(0,7),(0,8),(0,9),(0,10),(0,11),(0,12),(1,12),(2,12),(3,12),(4,12),(5,12),(6,12)],
  [(6,12),(7,12),(8,12),(9,12),(10,12),(11,12),(12,12),(12,11),(12,10),(12,9),(12,8),(12,7),(12,6)],
  [(12,6),(12,5),(12,4),(12,3),(12,2),(12,1),(12,0),(11,0),(10,0),(9,0),(8,0),(7,0),(6,0)],
  [(6,0),(5,0),(4,0),(3,0),(2,0),(1,0),(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6)]]

theorem qmaCrossingPatch_endpoints (e : Fin 9) :
    (qmaCrossingPatchPath e).head? = some (qmaCrossingPatchVertex (qmaCrossingPatchLeft e)) ∧
    (qmaCrossingPatchPath e).getLast? = some (qmaCrossingPatchVertex (qmaCrossingPatchRight e)) := by
  fin_cases e <;> decide

theorem qmaCrossingPatch_chain (e : Fin 9) :
    (qmaCrossingPatchPath e).IsChain
      (fun p q => Nat.dist p.1 q.1+Nat.dist p.2 q.2 = 1) := by
  fin_cases e <;> decide

theorem qmaCrossingPatch_simple (e : Fin 9) : (qmaCrossingPatchPath e).Nodup := by
  fin_cases e <;> decide

theorem qmaCrossingPatch_length (e : Fin 9) : (qmaCrossingPatchPath e).length ≤ 13 := by
  fin_cases e <;> decide

end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumGridWalk
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite unit-step route has a simple subroute with no larger length. -/

namespace ContinuumCoulomb

def qmaSquareGrid : SimpleGraph (ℕ × ℕ) where
  Adj p q := Nat.dist p.1 q.1 + Nat.dist p.2 q.2 = 1
  symm := ⟨by intro p q h; simpa only [Nat.dist_comm] using h⟩
  loopless := ⟨by intro p; simp⟩

end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumGridNeighborsFour
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The four local ports of an interior square-grid point. -/

namespace ContinuumCoulomb

def qmaGridNeighbor (p : ℕ × ℕ) (a : Fin 4) : ℕ × ℕ :=
  ![(p.1+1,p.2),(p.1,p.2+1),(p.1-1,p.2),(p.1,p.2-1)] a

theorem qmaGridNeighbor_adj (p : ℕ × ℕ) (hx : 0 < p.1) (hy : 0 < p.2) (a : Fin 4) :
    qmaSquareGrid.Adj p (qmaGridNeighbor p a) := by
  fin_cases a <;> simp [qmaGridNeighbor,qmaSquareGrid,Nat.dist] <;> omega

def qmaGridNeighborIndex (p q : ℕ × ℕ) : Fin 4 :=
  if q.1 = p.1+1 then 0 else if q.2 = p.2+1 then 1 else if q.1+1 = p.1 then 2 else 3

end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCellPathTemplates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The six possible ordinary-cell connections and four source rays. The two
opposite pairs are the only disjoint-port pair whose paths cross. -/

namespace ContinuumCoulomb

def qmaCellPairLeft : Fin 6 → Fin 4 := ![0,0,0,1,1,2]
def qmaCellPairRight : Fin 6 → Fin 4 := ![1,2,3,2,3,3]
def qmaCellPairPath : Fin 6 → List (ℕ × ℕ) := ![
  [(23,16),(23,17),(23,18),(23,19),(23,20),(23,21),(23,22),(23,23),(22,23),(21,23),(20,23),(19,23),(18,23),(17,23),(16,23)],
  [(23,16),(22,16),(21,16),(20,16),(19,16),(18,16),(17,16),(16,16),(15,16),(14,16),(13,16),(12,16),(11,16),(10,16),(9,16)],
  [(23,16),(23,15),(23,14),(23,13),(23,12),(23,11),(23,10),(23,9),(22,9),(21,9),(20,9),(19,9),(18,9),(17,9),(16,9)],
  [(16,23),(15,23),(14,23),(13,23),(12,23),(11,23),(10,23),(9,23),(9,22),(9,21),(9,20),(9,19),(9,18),(9,17),(9,16)],
  [(16,23),(16,22),(16,21),(16,20),(16,19),(16,18),(16,17),(16,16),(16,15),(16,14),(16,13),(16,12),(16,11),(16,10),(16,9)],
  [(9,16),(9,15),(9,14),(9,13),(9,12),(9,11),(9,10),(9,9),(10,9),(11,9),(12,9),(13,9),(14,9),(15,9),(16,9)]]

def qmaCellRayPath : Fin 4 → List (ℕ × ℕ) := ![
  [(16,16),(17,16),(18,16),(19,16),(20,16),(21,16),(22,16),(23,16)],
  [(16,16),(16,17),(16,18),(16,19),(16,20),(16,21),(16,22),(16,23)],
  [(16,16),(15,16),(14,16),(13,16),(12,16),(11,16),(10,16),(9,16)],
  [(16,16),(16,15),(16,14),(16,13),(16,12),(16,11),(16,10),(16,9)]]

def qmaCellPort : Fin 4 → ℕ × ℕ := ![(23,16),(16,23),(9,16),(16,9)]

theorem qmaCellPair_endpoints (e : Fin 6) :
    (qmaCellPairPath e).head? = some (qmaCellPort (qmaCellPairLeft e)) ∧
    (qmaCellPairPath e).getLast? = some (qmaCellPort (qmaCellPairRight e)) := by
  fin_cases e <;> decide

theorem qmaCellPair_length (e : Fin 6) : (qmaCellPairPath e).length = 15 := by
  fin_cases e <;> decide

theorem qmaCellPair_chain (e : Fin 6) : (qmaCellPairPath e).IsChain
    (fun p q => Nat.dist p.1 q.1+Nat.dist p.2 q.2 = 1) := by
  fin_cases e <;> decide

theorem qmaCellPair_simple (e : Fin 6) : (qmaCellPairPath e).Nodup := by
  fin_cases e <;> decide

theorem qmaCellPair_bounded (e : Fin 6) :
    ∀ p ∈ qmaCellPairPath e, 9 ≤ p.1 ∧ p.1 ≤ 23 ∧ 9 ≤ p.2 ∧ p.2 ≤ 23 := by
  fin_cases e <;> decide

theorem qmaCellRay_endpoints (a : Fin 4) :
    (qmaCellRayPath a).head? = some (16,16) ∧
    (qmaCellRayPath a).getLast? = some (qmaCellPort a) := by
  fin_cases a <;> decide

theorem qmaCellRay_length (a : Fin 4) : (qmaCellRayPath a).length = 8 := by
  fin_cases a <;> decide

theorem qmaCellRay_chain (a : Fin 4) : (qmaCellRayPath a).IsChain
    (fun p q => Nat.dist p.1 q.1+Nat.dist p.2 q.2 = 1) := by
  fin_cases a <;> decide

theorem qmaCellRay_simple (a : Fin 4) : (qmaCellRayPath a).Nodup := by
  fin_cases a <;> decide

theorem qmaCellRay_bounded (a : Fin 4) :
    ∀ p ∈ qmaCellRayPath a, 9 ≤ p.1 ∧ p.1 ≤ 23 ∧ 9 ≤ p.2 ∧ p.2 ≤ 23 := by
  fin_cases a <;> decide

end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFineRoute
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite lattice routes stay in the neighboring coarse cells of their endpoints. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

abbrev QMAFineGrid (rows width A : ℕ) := Fin ((rows+1)*A) × Fin (width+1)

def qmaFineGridCell {rows width A : ℕ} (hA : 0 < A) (p : QMAFineGrid rows width A) :
    QMAGridCell rows width :=
  (⟨p.1.val/A,(Nat.div_lt_iff_lt_mul hA).mpr p.1.isLt⟩,p.2)

def qmaFineGridNat {rows width A : ℕ} (p : QMAFineGrid rows width A) : ℕ × ℕ :=
  (p.1.val,p.2.val)

def qmaFineRoute {rows width A : ℕ} (p q : QMAFineGrid rows width A)
    (k : Fin (qmaManhattanLength (qmaFineGridNat p) (qmaFineGridNat q)+1)) :
    QMAFineGrid rows width A :=
  let z := qmaManhattanPoint (qmaFineGridNat p) (qmaFineGridNat q) k.val
  let hb := qmaManhattanPoint_bounds (qmaFineGridNat p) (qmaFineGridNat q) k.val (by omega)
  (⟨z.1,lt_of_le_of_lt hb.2.1 (max_lt p.1.isLt q.1.isLt)⟩,
   ⟨z.2,lt_of_le_of_lt hb.2.2.2 (max_lt p.2.isLt q.2.isLt)⟩)

@[simp] theorem qmaFineRoute_nat {rows width A : ℕ} (p q : QMAFineGrid rows width A)
    (k : Fin (qmaManhattanLength (qmaFineGridNat p) (qmaFineGridNat q)+1)) :
    qmaFineGridNat (qmaFineRoute p q k) = qmaManhattanPoint (qmaFineGridNat p) (qmaFineGridNat q) k.val := rfl

@[simp] theorem qmaFineRoute_zero {rows width A : ℕ} (p q : QMAFineGrid rows width A) :
    qmaFineRoute p q ⟨0,by omega⟩ = p := by
  apply Prod.ext <;> apply Fin.ext
  · exact congrArg Prod.fst (qmaManhattanPoint_zero (qmaFineGridNat p) (qmaFineGridNat q))
  · exact congrArg Prod.snd (qmaManhattanPoint_zero (qmaFineGridNat p) (qmaFineGridNat q))

@[simp] theorem qmaFineRoute_last {rows width A : ℕ} (p q : QMAFineGrid rows width A) :
    qmaFineRoute p q (Fin.last (qmaManhattanLength (qmaFineGridNat p) (qmaFineGridNat q))) = q := by
  apply Prod.ext <;> apply Fin.ext
  · exact congrArg Prod.fst (qmaManhattanPoint_last (qmaFineGridNat p) (qmaFineGridNat q))
  · exact congrArg Prod.snd (qmaManhattanPoint_last (qmaFineGridNat p) (qmaFineGridNat q))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPatchSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Disjoint twelve-wide crossing patches after a fixed integer expansion. -/

namespace ContinuumCoulomb

def qmaExpandedPoint (p : ℕ × ℕ) : ℕ × ℕ := (32*p.1+16,32*p.2+16)

end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumTranslatedPatch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Translating the fixed crossing patch to every isolated route crossing. -/

namespace ContinuumCoulomb

def qmaPatchTranslate (p z : ℕ × ℕ) : ℕ × ℕ := (32*p.1+10+z.1,32*p.2+10+z.2)

theorem qmaPatchTranslate_injective (p : ℕ × ℕ) : Function.Injective (qmaPatchTranslate p) := by
  intro x y h
  apply Prod.ext
  · exact Nat.add_left_cancel (congrArg Prod.fst h)
  · exact Nat.add_left_cancel (congrArg Prod.snd h)

theorem qmaPatchTranslate_distance (p x y : ℕ × ℕ) :
    Nat.dist (qmaPatchTranslate p x).1 (qmaPatchTranslate p y).1+
      Nat.dist (qmaPatchTranslate p x).2 (qmaPatchTranslate p y).2 =
        Nat.dist x.1 y.1+Nat.dist x.2 y.2 := by
  simp only [qmaPatchTranslate,Nat.dist_add_add_left]

def qmaCrossingPathAt (p : ℕ × ℕ) (e : Fin 9) : List (ℕ × ℕ) :=
  (qmaCrossingPatchPath e).map (qmaPatchTranslate p)

theorem qmaCrossingPathAt_chain (p : ℕ × ℕ) (e : Fin 9) :
    (qmaCrossingPathAt p e).IsChain
      (fun x y => Nat.dist x.1 y.1+Nat.dist x.2 y.2 = 1) := by
  apply List.isChain_map_of_isChain (qmaPatchTranslate p) _ (qmaCrossingPatch_chain e)
  intro x y h
  simpa only [qmaPatchTranslate_distance] using h

theorem qmaCrossingPathAt_simple (p : ℕ × ℕ) (e : Fin 9) : (qmaCrossingPathAt p e).Nodup :=
  (qmaCrossingPatch_simple e).map (qmaPatchTranslate_injective p)

end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumGridPorts
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Distinct entry and exit spin locations for every grid cell. -/

namespace ContinuumCoulomb

def qmaGridPort (p : ℕ × ℕ) (a : Fin 4) : ℕ × ℕ :=
  ![(32*p.1+23,32*p.2+16),(32*p.1+16,32*p.2+23),
    (32*p.1+9,32*p.2+16),(32*p.1+16,32*p.2+9)] a

theorem qmaGridPort_cell (p : ℕ × ℕ) (a : Fin 4) :
    ((qmaGridPort p a).1/32,(qmaGridPort p a).2/32) = p := by
  apply Prod.ext <;> fin_cases a <;> simp [qmaGridPort,Nat.add_div]

def qmaDirectedPort (p q : ℕ × ℕ) : ℕ × ℕ := qmaGridPort p (qmaGridNeighborIndex p q)

end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumInnerPorts
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Moving crossing terminals one unit into their private patch leaves the
external corridors free and creates space for the two mediator spins. -/

namespace ContinuumCoulomb

def qmaInnerPort (p : ℕ × ℕ) (a : Fin 4) : ℕ × ℕ :=
  ![(32*p.1+22,32*p.2+16),(32*p.1+16,32*p.2+22),
    (32*p.1+10,32*p.2+16),(32*p.1+16,32*p.2+10)] a

theorem qmaExpandedPoint_cell (p : ℕ × ℕ) :
    ((qmaExpandedPoint p).1/32,(qmaExpandedPoint p).2/32) = p := by
  apply Prod.ext <;> simp [qmaExpandedPoint,Nat.add_div]

end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHalfCorridor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Each external corridor splits into two paths contained in their own cells,
joined by one unit edge. These paths meet the internal templates only at ports. -/

namespace ContinuumCoulomb

def qmaHalfCorridorPath (cross : Bool) : Fin 4 → List (ℕ × ℕ) :=
  if cross then ![
    [(22,16),(23,16),(24,16),(25,16),(26,16),(27,16),(28,16),(29,16),(30,16),(31,16)],
    [(16,22),(16,23),(16,24),(16,25),(16,26),(16,27),(16,28),(16,29),(16,30),(16,31)],
    [(10,16),(9,16),(8,16),(7,16),(6,16),(5,16),(4,16),(3,16),(2,16),(1,16),(0,16)],
    [(16,10),(16,9),(16,8),(16,7),(16,6),(16,5),(16,4),(16,3),(16,2),(16,1),(16,0)]] else ![
    [(23,16),(24,16),(25,16),(26,16),(27,16),(28,16),(29,16),(30,16),(31,16)],
    [(16,23),(16,24),(16,25),(16,26),(16,27),(16,28),(16,29),(16,30),(16,31)],
    [(9,16),(8,16),(7,16),(6,16),(5,16),(4,16),(3,16),(2,16),(1,16),(0,16)],
    [(16,9),(16,8),(16,7),(16,6),(16,5),(16,4),(16,3),(16,2),(16,1),(16,0)]]

def qmaLocalPatchPath (e : Fin 9) : List (ℕ × ℕ) :=
  (qmaCrossingPatchPath e).map (fun z => (10+z.1,10+z.2))

def qmaCellBoundary : Fin 4 → ℕ × ℕ := ![(31,16),(16,31),(0,16),(16,0)]

def qmaLocalPort (cross : Bool) (a : Fin 4) : ℕ × ℕ :=
  if cross then qmaInnerPort (0,0) a else qmaCellPort a

theorem qmaHalfCorridor_endpoints (cross : Bool) (a : Fin 4) :
    (qmaHalfCorridorPath cross a).head? = some (qmaLocalPort cross a) ∧
    (qmaHalfCorridorPath cross a).getLast? = some (qmaCellBoundary a) := by
  cases cross <;> fin_cases a <;> decide

theorem qmaHalfCorridor_chain (cross : Bool) (a : Fin 4) :
    (qmaHalfCorridorPath cross a).IsChain
      (fun p q => Nat.dist p.1 q.1+Nat.dist p.2 q.2 = 1) := by
  cases cross <;> fin_cases a <;> decide

theorem qmaHalfCorridor_simple (cross : Bool) (a : Fin 4) :
    (qmaHalfCorridorPath cross a).Nodup := by
  cases cross <;> fin_cases a <;> decide

theorem qmaHalfCorridor_bounded (cross : Bool) (a : Fin 4) :
    ∀ p ∈ qmaHalfCorridorPath cross a, p.1 < 32 ∧ p.2 < 32 := by
  cases cross <;> fin_cases a <;> decide

end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCellTranslate
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cell-local paths translate injectively and different cells are disjoint. -/

namespace ContinuumCoulomb

def qmaCellTranslate (p z : ℕ × ℕ) : ℕ × ℕ := (32*p.1+z.1,32*p.2+z.2)

theorem qmaCellTranslate_injective (p : ℕ × ℕ) : Function.Injective (qmaCellTranslate p) := by
  intro x y h
  exact Prod.ext (Nat.add_left_cancel (congrArg Prod.fst h))
    (Nat.add_left_cancel (congrArg Prod.snd h))

theorem qmaCellTranslate_cell (p z : ℕ × ℕ) (hz : z.1 < 32 ∧ z.2 < 32) :
    ((qmaCellTranslate p z).1/32,(qmaCellTranslate p z).2/32) = p := by
  apply Prod.ext <;> dsimp [qmaCellTranslate] <;> omega

theorem qmaCellTranslate_unique {p q x y : ℕ × ℕ}
    (hx : x.1 < 32 ∧ x.2 < 32) (hy : y.1 < 32 ∧ y.2 < 32)
    (h : qmaCellTranslate p x = qmaCellTranslate q y) : p = q ∧ x = y := by
  have he := congrArg (fun z : ℕ × ℕ => (z.1/32,z.2/32)) h
  rw [qmaCellTranslate_cell p x hx,qmaCellTranslate_cell q y hy] at he
  subst q
  exact ⟨rfl,qmaCellTranslate_injective p h⟩

theorem qmaCellTranslate_step (p x y : ℕ × ℕ) :
    Nat.dist (qmaCellTranslate p x).1 (qmaCellTranslate p y).1+
      Nat.dist (qmaCellTranslate p x).2 (qmaCellTranslate p y).2 =
        Nat.dist x.1 y.1+Nat.dist x.2 y.2 := by
  simp only [qmaCellTranslate,Nat.dist_add_add_left]

theorem qmaCellTranslate_port (p : ℕ × ℕ) (a : Fin 4) :
    qmaCellTranslate p (qmaCellPort a) = qmaGridPort p a := by
  fin_cases a <;> rfl

theorem qmaCellTranslate_patch (p z : ℕ × ℕ) :
    qmaCellTranslate p (10+z.1,10+z.2) = qmaPatchTranslate p z := by
  simp only [qmaCellTranslate,qmaPatchTranslate,Nat.add_assoc]

end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCellCorridor
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual short lattice corridor between neighboring cells, with either
ordinary or inward-moved terminals at each end. -/

namespace ContinuumCoulomb

def qmaPortOpposite : Fin 4 → Fin 4 := ![2,3,0,1]

theorem qmaCellBoundary_step (p : ℕ × ℕ) (hp : 0 < p.1 ∧ 0 < p.2) (a : Fin 4) :
    qmaSquareGrid.Adj (qmaCellTranslate p (qmaCellBoundary a))
      (qmaCellTranslate (qmaGridNeighbor p a) (qmaCellBoundary (qmaPortOpposite a))) := by
  fin_cases a <;>
    dsimp [qmaCellTranslate,qmaCellBoundary,qmaPortOpposite,qmaGridNeighbor]
  all_goals change Nat.dist _ _ + Nat.dist _ _ = 1
  all_goals unfold Nat.dist; omega

def qmaHalfPathAt (p : ℕ × ℕ) (cross : Bool) (a : Fin 4) : List (ℕ × ℕ) :=
  (qmaHalfCorridorPath cross a).map (qmaCellTranslate p)

theorem qmaHalfPathAt_endpoints (p : ℕ × ℕ) (cross : Bool) (a : Fin 4) :
    (qmaHalfPathAt p cross a).head? = some (qmaCellTranslate p (qmaLocalPort cross a)) ∧
    (qmaHalfPathAt p cross a).getLast? = some (qmaCellTranslate p (qmaCellBoundary a)) := by
  simp only [qmaHalfPathAt,List.head?_map,List.getLast?_map,
    (qmaHalfCorridor_endpoints cross a).1,(qmaHalfCorridor_endpoints cross a).2,Option.map_some]
  constructor <;> trivial

theorem qmaHalfPathAt_chain (p : ℕ × ℕ) (cross : Bool) (a : Fin 4) :
    (qmaHalfPathAt p cross a).IsChain (fun x y => qmaSquareGrid.Adj x y) := by
  apply List.isChain_map_of_isChain (qmaCellTranslate p) _ (qmaHalfCorridor_chain cross a)
  intro x y h
  change Nat.dist _ _ + Nat.dist _ _ = 1
  simpa only [qmaCellTranslate_step] using h

theorem qmaHalfPathAt_simple (p : ℕ × ℕ) (cross : Bool) (a : Fin 4) :
    (qmaHalfPathAt p cross a).Nodup :=
  (qmaHalfCorridor_simple cross a).map (qmaCellTranslate_injective p)

theorem qmaHalfPathAt_mem {p z : ℕ × ℕ} {cross : Bool} {a : Fin 4}
    (hz : z ∈ qmaHalfPathAt p cross a) :
    ∃ u, u.1 < 32 ∧ u.2 < 32 ∧ qmaCellTranslate p u = z := by
  obtain ⟨u,hu,he⟩ := List.mem_map.mp hz
  exact ⟨u,(qmaHalfCorridor_bounded cross a u hu).1,
    (qmaHalfCorridor_bounded cross a u hu).2,he⟩

def qmaCellCorridor (p : ℕ × ℕ) (a : Fin 4) (cross nextCross : Bool) : List (ℕ × ℕ) :=
  qmaHalfPathAt p cross a ++
    (qmaHalfPathAt (qmaGridNeighbor p a) nextCross (qmaPortOpposite a)).reverse

theorem qmaCellCorridor_endpoints (p : ℕ × ℕ) (a : Fin 4) (cross nextCross : Bool) :
    (qmaCellCorridor p a cross nextCross).head? =
      some (qmaCellTranslate p (qmaLocalPort cross a)) ∧
    (qmaCellCorridor p a cross nextCross).getLast? =
      some (qmaCellTranslate (qmaGridNeighbor p a) (qmaLocalPort nextCross (qmaPortOpposite a))) := by
  simp only [qmaCellCorridor,List.head?_append,List.getLast?_append,List.head?_reverse,List.getLast?_reverse,
    (qmaHalfPathAt_endpoints p cross a).1,
    (qmaHalfPathAt_endpoints (qmaGridNeighbor p a) nextCross (qmaPortOpposite a)).1,Option.some_or]
  constructor <;> trivial

theorem qmaCellCorridor_chain (p : ℕ × ℕ) (hp : 0 < p.1 ∧ 0 < p.2) (a : Fin 4)
    (cross nextCross : Bool) :
    (qmaCellCorridor p a cross nextCross).IsChain (fun x y => qmaSquareGrid.Adj x y) := by
  apply (qmaHalfPathAt_chain p cross a).append
  · apply List.isChain_reverse.mpr
    exact (qmaHalfPathAt_chain (qmaGridNeighbor p a) nextCross (qmaPortOpposite a)).imp
      (fun _ _ h => h.symm)
  · intro x hx y hy
    rw [(qmaHalfPathAt_endpoints p cross a).2] at hx
    rw [List.head?_reverse,
      (qmaHalfPathAt_endpoints (qmaGridNeighbor p a) nextCross (qmaPortOpposite a)).2] at hy
    have hx' := Option.mem_def.mp hx
    have hy' := Option.mem_def.mp hy
    cases hx'
    cases hy'
    exact qmaCellBoundary_step p hp a

theorem qmaCellCorridor_simple (p : ℕ × ℕ) (hp : 0 < p.1 ∧ 0 < p.2) (a : Fin 4)
    (cross nextCross : Bool) : (qmaCellCorridor p a cross nextCross).Nodup := by
  apply (qmaHalfPathAt_simple p cross a).append
    (List.nodup_reverse.mpr (qmaHalfPathAt_simple (qmaGridNeighbor p a) nextCross (qmaPortOpposite a)))
  apply List.disjoint_left.mpr
  intro z hz hy
  obtain ⟨u,hu,hv,he⟩ := qmaHalfPathAt_mem hz
  obtain ⟨v,hv1,hv2,hf⟩ := qmaHalfPathAt_mem (List.mem_reverse.mp hy)
  have hh := qmaCellTranslate_unique ⟨hu,hv⟩ ⟨hv1,hv2⟩ (he.trans hf.symm)
  exact (qmaGridNeighbor_adj p hp.1 hp.2 a).ne hh.1

theorem qmaCellCorridor_length (p : ℕ × ℕ) (a : Fin 4) (cross nextCross : Bool) :
    18 ≤ (qmaCellCorridor p a cross nextCross).length ∧
      (qmaCellCorridor p a cross nextCross).length ≤ 21 := by
  simp only [qmaCellCorridor,qmaHalfPathAt,List.length_append,List.length_reverse,List.length_map]
  cases cross <;> cases nextCross <;> fin_cases a <;> decide

end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCellRouteCatalog
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite catalog of the four local route types used by the physical graph.
Every valid catalog entry is a simple grid path of at most twenty steps. -/

namespace ContinuumCoulomb

inductive QMACellRouteBody where
  | ray (cell : ℕ × ℕ) (port : Fin 4)
  | pair (cell : ℕ × ℕ) (edge : Fin 6)
  | patch (cell : ℕ × ℕ) (edge : Fin 9)
  | corridor (cell : ℕ × ℕ) (port : Fin 4) (cross nextCross : Bool)

namespace QMACellRouteBody

def path : QMACellRouteBody → List (ℕ × ℕ)
  | .ray p a => (qmaCellRayPath a).map (qmaCellTranslate p)
  | .pair p e => (qmaCellPairPath e).map (qmaCellTranslate p)
  | .patch p e => qmaCrossingPathAt p e
  | .corridor p a b c => qmaCellCorridor p a b c

def source : QMACellRouteBody → ℕ × ℕ
  | .ray p _ => qmaExpandedPoint p
  | .pair p e => qmaGridPort p (qmaCellPairLeft e)
  | .patch p e => qmaPatchTranslate p (qmaCrossingPatchVertex (qmaCrossingPatchLeft e))
  | .corridor p a b _ => qmaCellTranslate p (qmaLocalPort b a)

def target : QMACellRouteBody → ℕ × ℕ
  | .ray p a => qmaGridPort p a
  | .pair p e => qmaGridPort p (qmaCellPairRight e)
  | .patch p e => qmaPatchTranslate p (qmaCrossingPatchVertex (qmaCrossingPatchRight e))
  | .corridor p a _ c => qmaCellTranslate (qmaGridNeighbor p a) (qmaLocalPort c (qmaPortOpposite a))

def Valid : QMACellRouteBody → Prop
  | .corridor p _ _ _ => 0 < p.1 ∧ 0 < p.2
  | _ => True

theorem endpoints (R : QMACellRouteBody) :
    R.path.head? = some R.source ∧ R.path.getLast? = some R.target := by
  cases R with
  | ray p a =>
    simpa only [path,source,target,List.head?_map,List.getLast?_map,
      (qmaCellRay_endpoints a).1,(qmaCellRay_endpoints a).2,Option.map_some,
      qmaCellTranslate_port] using
      (show some (qmaCellTranslate p (16,16)) = some (qmaExpandedPoint p) ∧
        some (qmaGridPort p a) = some (qmaGridPort p a) from ⟨rfl,rfl⟩)
  | pair p e =>
    simp only [path,source,target,List.head?_map,List.getLast?_map,
      (qmaCellPair_endpoints e).1,(qmaCellPair_endpoints e).2,Option.map_some,qmaCellTranslate_port]
    constructor <;> trivial
  | patch p e =>
    simp only [path,source,target,qmaCrossingPathAt,List.head?_map,List.getLast?_map,
      (qmaCrossingPatch_endpoints e).1,(qmaCrossingPatch_endpoints e).2,Option.map_some]
    constructor <;> trivial
  | corridor p a b c => exact qmaCellCorridor_endpoints p a b c

theorem length_bounds (R : QMACellRouteBody) : 3 ≤ R.path.length ∧ R.path.length ≤ 21 := by
  cases R with
  | ray p a => simp only [path,List.length_map,qmaCellRay_length]; omega
  | pair p e => simp only [path,List.length_map,qmaCellPair_length]; omega
  | patch p e =>
    have hlo : 3 ≤ (qmaCrossingPatchPath e).length := by fin_cases e <;> decide
    have hhi := qmaCrossingPatch_length e
    simp only [path,qmaCrossingPathAt,List.length_map]
    omega
  | corridor p a b c =>
    have h := qmaCellCorridor_length p a b c
    exact ⟨(by decide : 3 ≤ 18).trans h.1,h.2⟩

theorem simple (R : QMACellRouteBody) (hR : R.Valid) : R.path.Nodup := by
  cases R with
  | ray p a => exact (qmaCellRay_simple a).map (qmaCellTranslate_injective p)
  | pair p e => exact (qmaCellPair_simple e).map (qmaCellTranslate_injective p)
  | patch p e => exact qmaCrossingPathAt_simple p e
  | corridor p a b c => exact qmaCellCorridor_simple p hR a b c

theorem chain (R : QMACellRouteBody) (hR : R.Valid) :
    R.path.IsChain (fun x y => qmaSquareGrid.Adj x y) := by
  cases R with
  | ray p a =>
    apply List.isChain_map_of_isChain (qmaCellTranslate p) _ (qmaCellRay_chain a)
    intro x y h
    change Nat.dist _ _ + Nat.dist _ _ = 1
    simpa only [qmaCellTranslate_step] using h
  | pair p e =>
    apply List.isChain_map_of_isChain (qmaCellTranslate p) _ (qmaCellPair_chain e)
    intro x y h
    change Nat.dist _ _ + Nat.dist _ _ = 1
    simpa only [qmaCellTranslate_step] using h
  | patch p e => exact qmaCrossingPathAt_chain p e
  | corridor p a b c => exact qmaCellCorridor_chain p hR a b c

end QMACellRouteBody

structure QMACellRoute where
  body : QMACellRouteBody
  reversed : Bool

namespace QMACellRoute

def path (R : QMACellRoute) := if R.reversed then R.body.path.reverse else R.body.path
def source (R : QMACellRoute) := if R.reversed then R.body.target else R.body.source
def target (R : QMACellRoute) := if R.reversed then R.body.source else R.body.target
def Valid (R : QMACellRoute) := R.body.Valid

theorem endpoints (R : QMACellRoute) :
    R.path.head? = some R.source ∧ R.path.getLast? = some R.target := by
  rcases R with ⟨body,b⟩
  cases b
  · exact body.endpoints
  · simpa only [path,source,target,ite_true, if_true,List.head?_reverse,List.getLast?_reverse] using
      body.endpoints.symm

theorem length_bounds (R : QMACellRoute) : 3 ≤ R.path.length ∧ R.path.length ≤ 21 := by
  rcases R with ⟨body,b⟩
  cases b <;> simpa only [path,Bool.false_eq_true,ite_false, if_false,ite_true, if_true,List.length_reverse] using body.length_bounds

theorem simple (R : QMACellRoute) (hR : R.Valid) : R.path.Nodup := by
  rcases R with ⟨body,b⟩
  cases b
  · exact body.simple hR
  · exact List.nodup_reverse.mpr (body.simple hR)

theorem chain (R : QMACellRoute) (hR : R.Valid) :
    R.path.IsChain (fun x y => qmaSquareGrid.Adj x y) := by
  rcases R with ⟨body,b⟩
  cases b
  · exact body.chain hR
  · exact List.isChain_reverse.mpr ((body.chain hR).imp (fun _ _ h => h.symm))

end QMACellRoute
end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumParallelGraph
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit ordinary-spin graph for an entire parallel singlet-routing layer. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix MediatorGraph
open scoped BigOperators Kronecker Classical
variable {ν κ : Type*} [Fintype ν] [Fintype κ]

def qmaParallelGraphLeft {n r : ℕ} (base : ν → Fin n) (site : Fin r → κ → Fin n) :
    ν ⊕ (Fin r ⊕ (Fin r × κ)) → Fin (n+r*2)
  | .inl a => old n r (base a)
  | .inr (.inl e) => fresh n r e 0
  | .inr (.inr p) => old n r (site p.1 p.2)

def qmaParallelGraphRight {n r : ℕ} (base : ν → Fin n) (member : Fin r → κ → Fin 2) :
    ν ⊕ (Fin r ⊕ (Fin r × κ)) → Fin (n+r*2)
  | .inl a => old n r (base a)
  | .inr (.inl e) => fresh n r e 1
  | .inr (.inr p) => fresh n r p.1 (member p.1 p.2)

omit [Fintype ν] [Fintype κ] in
theorem qmaParallelGraph_distinct {n r : ℕ} (left right : ν → Fin n)
    (hneq : ∀ a, left a ≠ right a) (site : Fin r → κ → Fin n) (member : Fin r → κ → Fin 2) :
    ∀ a, qmaParallelGraphLeft left site a ≠ qmaParallelGraphRight right member a := by
  intro a
  rcases a with a | a
  · exact fun h => hneq a (old_injective n r h)
  rcases a with e | p
  · intro h
    have hh := congrArg Prod.snd (fresh_injective n r (a₁ := (e,0)) (a₂ := (e,1)) h)
    norm_num at hh
  · exact old_ne_fresh n r _ _ _

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumGraphDegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Incidence counts for the actual ordinary-spin routing graphs. -/

noncomputable section
namespace ContinuumCoulomb
open MediatorGraph
open scoped BigOperators Classical
variable {ν κ : Type*} [Fintype ν] [Fintype κ]

def qmaGraphDegree {n : ℕ} (left right : ν → Fin n) (v : Fin n) : ℕ :=
  ∑ e, if left e = v ∨ right e = v then 1 else 0

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPathSubdivision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational two-edge and three-edge exchange subdivision, including the
pendant singlet partner needed by an even-length lattice path. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaPathMember (even : Bool) : Fin 2 → Fin 2 := if even then ![0,0] else ![0,1]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRoutingSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Linear graph-size growth and an explicit polynomial routing penalty bound. -/

noncomputable section
namespace ContinuumCoulomb

abbrev QMACrossingsGraphEdge (ν : Type*) (r : ℕ) :=
  (ν ⊕ (Fin r × Fin 4)) ⊕ (Fin r ⊕ (Fin r × Fin 4))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPartialPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Subdivide any selected subset of a finite exchange graph in one calibrated layer. -/

noncomputable section
namespace ContinuumCoulomb
open MediatorGraph Matrix
open scoped BigOperators Classical

variable {ν : Type*} [Fintype ν] {n : ℕ}

def qmaSelectedIndex (s : Finset ν) (i : Fin s.card) : ν := (s.equivFin.symm i).val

def qmaSelectedSite (left right : ν → Fin n) (s : Finset ν) (i : Fin s.card) : Fin 2 → Fin n :=
  ![left (qmaSelectedIndex s i),right (qmaSelectedIndex s i)]


abbrev QMAPartialPathsEdge (s : Finset ν) :=
  {e // e ∉ s} ⊕ (Fin s.card ⊕ (Fin s.card × Fin 2))

def qmaPartialPathsLeft (left right : ν → Fin n) (s : Finset ν) : QMAPartialPathsEdge s → Fin (n+s.card*2) :=
  qmaParallelGraphLeft (fun e : {e // e ∉ s} => left e.val) (qmaSelectedSite left right s)

def qmaPartialPathsRight (right : ν → Fin n) (s : Finset ν) (even : Fin s.card → Bool) :
    QMAPartialPathsEdge s → Fin (n+s.card*2) :=
  qmaParallelGraphRight (fun e : {e // e ∉ s} => right e.val) (fun i => qmaPathMember (even i))

omit [Fintype ν] in
theorem qmaPartialPaths_distinct (left right : ν → Fin n) (hn : ∀ e, left e ≠ right e)
    (s : Finset ν) (even : Fin s.card → Bool) :
    ∀ e, qmaPartialPathsLeft left right s e ≠ qmaPartialPathsRight right s even e :=
  qmaParallelGraph_distinct (fun e : {e // e ∉ s} => left e.val) (fun e => right e.val)
    (fun e => hn e.val) _ _

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPathProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal polynomial coefficient program for both parities of a path gadget. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPathCode
open ExactQuantumFactoring.BitStackProgram

abbrev Input := Bool × (ℚ × ℚ)

def coefficients (x : Input) : Fin 4 → ℚ :=
  ![x.2.1^2,x.2.1,if x.1 then -2*x.2.1*x.2.2 else 2*x.2.1*x.2.2,
    3/4+3*x.2.2^2+3*x.2.1^2]

end ContinuumCoulomb.QuantumPathCode

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRationalPathStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact rational graph data for a selected path-subdivision layer. -/

noncomputable section
namespace ContinuumCoulomb
open MediatorGraph
open scoped BigOperators Classical

structure QMARationalExchangeGraph where
  n : ℕ
  Edge : Type
  [edgeFinite : Fintype Edge]
  left : Edge → Fin n
  right : Edge → Fin n
  distinct : ∀ e, left e ≠ right e
  weight : Edge → ℚ
  constant : ℚ

attribute [instance] QMARationalExchangeGraph.edgeFinite

namespace QMARationalExchangeGraph

def pathScale (G : QMARationalExchangeGraph) (s : Finset G.Edge) (N : ℚ) : ℚ :=
  let B := 3*(∑ e : {e // e ∉ s}, |G.weight e.val|)+|G.constant|
  let A := 3*∑ i : Fin s.card, (1+2*|G.weight (qmaSelectedIndex s i)|)
  let D := B+4*∑ i : Fin s.card, (1+|G.weight (qmaSelectedIndex s i)|)^2
  16*(A+D+1)^3*N+4*(A+D+1)+1

def subdivide (G : QMARationalExchangeGraph) (s : Finset G.Edge)
    (even : Fin s.card → Bool) (N : ℚ) : QMARationalExchangeGraph where
  n := G.n+s.card*2
  Edge := QMAPartialPathsEdge s
  left := qmaPartialPathsLeft G.left G.right s
  right := qmaPartialPathsRight G.right s even
  distinct := qmaPartialPaths_distinct G.left G.right G.distinct s even
  weight := fun e => match e with
    | .inl e => G.weight e.val
    | .inr (.inl _) => (G.pathScale s N)^2
    | .inr (.inr (i,a)) => QuantumPathCode.coefficients
        (even i,G.pathScale s N,G.weight (qmaSelectedIndex s i)) ⟨a.val+1,by omega⟩
  constant := (G.constant+∑ i : Fin s.card, (3/4+3*(G.weight (qmaSelectedIndex s i))^2))+
    3*(s.card:ℚ)*(G.pathScale s N)^2

end QMARationalExchangeGraph
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPortChain
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Each coarse route is replaced by its ordered incoming and outgoing cell ports. -/

namespace ContinuumCoulomb

def qmaPortNeighborIndex (k : ℕ) : ℕ := if k%2 = 1 then k/2+1 else k/2-1

def qmaRoutePort (p : ℕ → ℕ × ℕ) (k : ℕ) : ℕ × ℕ :=
  qmaDirectedPort (p (k/2)) (p (qmaPortNeighborIndex k))

def qmaPortChain (p : ℕ → ℕ × ℕ) (L k : ℕ) : ℕ × ℕ :=
  if k = 0 then qmaExpandedPoint (p 0) else
    if k = 2*L+1 then qmaExpandedPoint (p L) else qmaRoutePort p k

@[simp] theorem qmaPortChain_zero (p : ℕ → ℕ × ℕ) (L : ℕ) :
    qmaPortChain p L 0 = qmaExpandedPoint (p 0) := by simp [qmaPortChain]

@[simp] theorem qmaPortChain_last (p : ℕ → ℕ × ℕ) (L : ℕ) :
    qmaPortChain p L (2*L+1) = qmaExpandedPoint (p L) := by simp [qmaPortChain]

end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPathSchedule
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A bounded number of selected odd subdivisions realizes independently prescribed
path lengths. Only edges with remaining work receive a new mediator pair. -/

noncomputable section
namespace ContinuumCoulomb
open MediatorGraph
open scoped BigOperators Classical

structure QMAPathSchedule where
  graph : QMARationalExchangeGraph
  work : graph.Edge → ℕ

namespace QMAPathSchedule

def active (W : QMAPathSchedule) : Finset W.graph.Edge :=
  Finset.univ.filter (fun e => 0 < W.work e)

@[simp] theorem mem_active (W : QMAPathSchedule) (e : W.graph.Edge) :
    e ∈ W.active ↔ 0 < W.work e := by simp [active]

end QMAPathSchedule
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPathEmbedding
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Geometric invariants for the variable-length path-subdivision schedule. -/

noncomputable section
namespace ContinuumCoulomb
open MediatorGraph
open scoped Classical

structure QMAPathEmbedding (W : QMAPathSchedule)
    (Γ : SimpleGraph (ℕ × ℕ) := qmaSquareGrid) where
  position : Fin W.graph.n → ℕ × ℕ
  position_injective : Function.Injective position
  point : W.graph.Edge → ℕ → ℕ × ℕ
  first : ∀ e, point e 0 = position (W.graph.left e)
  last : ∀ e, point e (2*W.work e+1) = position (W.graph.right e)
  simple : ∀ e i j, i ≤ 2*W.work e+1 → j ≤ 2*W.work e+1 → point e i = point e j → i = j
  step : ∀ e i, i < 2*W.work e+1 → Γ.Adj (point e i) (point e (i+1))
  avoids : ∀ e i v, 0 < i → i < 2*W.work e+1 → point e i ≠ position v
  disjoint : ∀ e f i j, e ≠ f → 0 < i → i < 2*W.work e+1 → j ≤ 2*W.work f+1 →
    point e i ≠ point f j

namespace QMAPathEmbedding
variable {W : QMAPathSchedule} {Γ : SimpleGraph (ℕ × ℕ)} (P : QMAPathEmbedding W Γ)

def freshPosition (i : Fin W.active.card) (b : Fin 2) : ℕ × ℕ :=
  P.point (qmaSelectedIndex W.active i) (b.val+1)

def nextPosition (v : Fin (W.graph.n+W.active.card*2)) : ℕ × ℕ :=
  Sum.elim P.position (fun p => P.freshPosition p.1 p.2) ((vertexEquiv _ _).symm v)

@[simp] theorem nextPosition_old (v : Fin W.graph.n) :
    P.nextPosition (old _ _ v) = P.position v := by simp [nextPosition,old]

@[simp] theorem nextPosition_fresh (e : Fin W.active.card) (b : Fin 2) :
    P.nextPosition (fresh _ _ e b) = P.freshPosition e b := by simp [nextPosition,fresh]

end QMAPathEmbedding
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPortCellPositive
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every cell touched by an actual port-graph edge lies in the positive quadrant. -/

namespace ContinuumCoulomb

def qmaPointCell (z : ℕ × ℕ) : ℕ × ℕ := (z.1/32,z.2/32)

@[simp] theorem qmaPointCell_center (p : ℕ × ℕ) : qmaPointCell (qmaExpandedPoint p) = p :=
  qmaExpandedPoint_cell p

@[simp] theorem qmaPointCell_port (p : ℕ × ℕ) (a : Fin 4) : qmaPointCell (qmaGridPort p a) = p :=
  qmaGridPort_cell p a

end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumLocalPathClearance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact endpoint clearance inside one cell. These finite facts separate
external corridors from the rays, ordinary pairs and nine gadget paths. -/

namespace ContinuumCoulomb

theorem qmaLocalPatch_bounded (e : Fin 9) :
    ∀ p ∈ qmaLocalPatchPath e, 10 ≤ p.1 ∧ p.1 ≤ 22 ∧ 10 ≤ p.2 ∧ p.2 ≤ 22 := by
  fin_cases e <;> decide

end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumInternalRouteSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Distinct permitted internal routes in a cell have disjoint interiors. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

abbrev QMAInternalEdge := Fin 4 ⊕ (Fin 6 ⊕ Fin 9)

def qmaInternalPath : QMAInternalEdge → List (ℕ × ℕ)
  | .inl a => qmaCellRayPath a
  | .inr (.inl e) => qmaCellPairPath e
  | .inr (.inr e) => qmaLocalPatchPath e

def qmaInternalBody (p : ℕ × ℕ) : QMAInternalEdge → QMACellRouteBody
  | .inl a => .ray p a
  | .inr (.inl e) => .pair p e
  | .inr (.inr e) => .patch p e

theorem qmaInternalPath_bounded (e : QMAInternalEdge) :
    ∀ p ∈ qmaInternalPath e, p.1 < 32 ∧ p.2 < 32 := by
  rcases e with a | (e | e)
  · intro p hp
    obtain ⟨_,hx,_,hy⟩ := qmaCellRay_bounded a p hp
    omega
  · intro p hp
    obtain ⟨_,hx,_,hy⟩ := qmaCellPair_bounded e p hp
    omega
  · intro p hp
    obtain ⟨_,hx,_,hy⟩ := qmaLocalPatch_bounded e p hp
    omega

theorem qmaInternalBody_path (p : ℕ × ℕ) (e : QMAInternalEdge) :
    (qmaInternalBody p e).path = (qmaInternalPath e).map (qmaCellTranslate p) := by
  rcases e with a | (e | e)
  · rfl
  · rfl
  · change (qmaCrossingPatchPath e).map (qmaPatchTranslate p) =
      ((qmaCrossingPatchPath e).map (fun z => (10+z.1,10+z.2))).map (qmaCellTranslate p)
    rw [List.map_map]
    apply List.map_congr_left
    intro z _
    exact (qmaCellTranslate_patch p z).symm

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRouteEnumeration
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Only 140 explicit catalog routes need be tested for a physical edge: the
seventy oriented routes in each endpoint cell. This supplies a fixed finite
search space for the literal planar-route compiler. -/

namespace ContinuumCoulomb

def QMACellRouteBody.cell : QMACellRouteBody → ℕ × ℕ
  | .ray p _ => p
  | .pair p _ => p
  | .patch p _ => p
  | .corridor p _ _ _ => p

theorem QMACellRouteBody.source_cell (B : QMACellRouteBody) : qmaPointCell B.source = B.cell := by
  cases B with
  | ray p a => exact qmaPointCell_center p
  | pair p e => exact qmaPointCell_port p (qmaCellPairLeft e)
  | patch p e =>
    apply Prod.ext <;> fin_cases e <;>
      simp [QMACellRouteBody.source,QMACellRouteBody.cell,qmaPointCell,qmaPatchTranslate,
        qmaCrossingPatchLeft,qmaCrossingPatchVertex,Nat.add_div]
  | corridor p a b c =>
    have h : (qmaLocalPort b a).1 < 32 ∧ (qmaLocalPort b a).2 < 32 := by
      cases b <;> fin_cases a <;> decide
    exact qmaCellTranslate_cell p _ h

end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumMergedOutputRoutes
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact parallel-edge merging preserves the physical placement and reverses
the catalog route when canonical endpoint ordering requires it. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical
namespace QMACellRoute

def reverse (R : QMACellRoute) : QMACellRoute := ⟨R.body,!R.reversed⟩

@[simp] theorem reverse_body (R : QMACellRoute) : R.reverse.body = R.body := rfl

@[simp] theorem reverse_source (R : QMACellRoute) : R.reverse.source = R.target := by
  rcases R with ⟨b,r⟩
  cases r <;> rfl

@[simp] theorem reverse_target (R : QMACellRoute) : R.reverse.target = R.source := by
  rcases R with ⟨b,r⟩
  cases r <;> rfl

@[simp] theorem reverse_valid (R : QMACellRoute) : R.reverse.Valid = R.Valid := rfl

end QMACellRoute
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumMergedEndpointPairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Distinct merged interactions have different unordered physical endpoints. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

namespace QMACellRoute

def endpointPair (R : QMACellRoute) : Sym2 (ℕ × ℕ) := s(R.source,R.target)

theorem endpointPair_body (R : QMACellRoute) : R.endpointPair = s(R.body.source,R.body.target) := by
  rcases R with ⟨b,r⟩
  cases r
  · rfl
  · exact Sym2.eq_swap

end QMACellRoute
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPermittedRouteSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete permitted catalog is planar: different unordered physical
endpoint pairs have disjoint path interiors. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaCellBody_cases (R : QMACellRouteBody) :
    (∃ p e, R = qmaInternalBody p e) ∨ ∃ p a b c, R = .corridor p a b c := by
  cases R with
  | ray p a => exact Or.inl ⟨p,.inl a,rfl⟩
  | pair p e => exact Or.inl ⟨p,.inr (.inl e),rfl⟩
  | patch p e => exact Or.inl ⟨p,.inr (.inr e),rfl⟩
  | corridor p a b c => exact Or.inr ⟨p,a,b,c,rfl⟩

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCellRouteSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A catalog path stays in the cells of its two endpoints. This transfers
positivity and box bounds from physical spins to all subdivision sites. -/

namespace ContinuumCoulomb

theorem qmaLocalPort_bounded (b : Bool) (a : Fin 4) :
    (qmaLocalPort b a).1 < 32 ∧ (qmaLocalPort b a).2 < 32 := by
  cases b <;> fin_cases a <;> decide

theorem qmaPointCell_localPort (p : ℕ × ℕ) (b : Bool) (a : Fin 4) :
    qmaPointCell (qmaCellTranslate p (qmaLocalPort b a)) = p :=
  qmaCellTranslate_cell p _ (qmaLocalPort_bounded b a)

theorem qmaPointCell_halfPath {p z : ℕ × ℕ} {b : Bool} {a : Fin 4}
    (hz : z ∈ qmaHalfPathAt p b a) : qmaPointCell z = p := by
  obtain ⟨u,hu,hv,rfl⟩ := qmaHalfPathAt_mem hz
  exact qmaCellTranslate_cell p u ⟨hu,hv⟩

theorem qmaPointCell_internalPath {p z : ℕ × ℕ} {e : QMAInternalEdge}
    (hz : z ∈ (qmaInternalBody p e).path) : qmaPointCell z = p := by
  rw [qmaInternalBody_path] at hz
  obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hz
  exact qmaCellTranslate_cell p u (qmaInternalPath_bounded e u hu)

namespace QMACellRouteBody

theorem path_cells (R : QMACellRouteBody) {z : ℕ × ℕ} (hz : z ∈ R.path) :
    qmaPointCell z = qmaPointCell R.source ∨ qmaPointCell z = qmaPointCell R.target := by
  rcases qmaCellBody_cases R with ⟨p,e,rfl⟩ | ⟨p,a,b,c,rfl⟩
  · have hp := qmaPointCell_internalPath hz
    have hs := qmaPointCell_internalPath (List.mem_of_head? (qmaInternalBody p e).endpoints.1)
    exact Or.inl (hp.trans hs.symm)
  · rcases List.mem_append.mp hz with h | h
    · have hp := qmaPointCell_halfPath h
      exact Or.inl (hp.trans (qmaPointCell_localPort p b a).symm)
    · have hp := qmaPointCell_halfPath (List.mem_reverse.mp h)
      exact Or.inr (hp.trans (qmaPointCell_localPort (qmaGridNeighbor p a) c (qmaPortOpposite a)).symm)

end QMACellRouteBody
namespace QMACellRoute

theorem path_cells (R : QMACellRoute) {z : ℕ × ℕ} (hz : z ∈ R.path) :
    qmaPointCell z = qmaPointCell R.source ∨ qmaPointCell z = qmaPointCell R.target := by
  rcases R with ⟨R,b⟩
  cases b
  · exact R.path_cells hz
  · have h := R.path_cells (List.mem_reverse.mp hz)
    exact h.elim Or.inr Or.inl

theorem path_positive (R : QMACellRoute)
    (hs : 0 < (qmaPointCell R.source).1 ∧ 0 < (qmaPointCell R.source).2)
    (ht : 0 < (qmaPointCell R.target).1 ∧ 0 < (qmaPointCell R.target).2)
    {z : ℕ × ℕ} (hz : z ∈ R.path) : 0 < z.1 ∧ 0 < z.2 := by
  have hp : 0 < (qmaPointCell z).1 ∧ 0 < (qmaPointCell z).2 := by
    rcases R.path_cells hz with h | h
    · simpa only [h] using hs
    · simpa only [h] using ht
  change 0 < z.1/32 ∧ 0 < z.2/32 at hp
  omega

end QMACellRoute
end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumChosenSlots
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Geometry only needs a bounded slot map injective inside each cell. This
interface permits the literal ordinal slot map without fixing abstract choices. -/

noncomputable section
namespace ContinuumCoulomb

structure QMACellSlots {Q : Type*} {rows width : ℕ}
    (cell : Q → QMAGridCell rows width) (A : ℕ) where
  index : Q → Fin A
  injective : ∀ {q r}, cell q = cell r → index q = index r → q=r

namespace QMACellSlots
variable {Q : Type*} {rows width A : ℕ} {cell : Q → QMAGridCell rows width}

 def ofDensity [Fintype Q]
    (h : ∀ p, (Finset.univ.filter (fun q => cell q=p)).card ≤ A) : QMACellSlots cell A :=
  ⟨qmaGridSlot cell h,qmaGridSlot_injective_on_cell cell h⟩

 def site (S : QMACellSlots cell A) (q : Q) : QMAFineGrid rows width A :=
  (finProdFinEquiv ((cell q).1,S.index q),(cell q).2)

 theorem site_injective (S : QMACellSlots cell A) : Function.Injective S.site := by
  intro q r h
  have hx := finProdFinEquiv.injective (congrArg Prod.fst h)
  have hrow : (cell q).1 = (cell r).1 :=
    congrArg (fun x : Fin (rows+1) × Fin A => x.1) hx
  have hcol : (cell q).2 = (cell r).2 :=
    congrArg (fun x : QMAFineGrid rows width A => x.2) h
  have hslot : S.index q = S.index r :=
    congrArg (fun x : Fin (rows+1) × Fin A => x.2) hx
  exact S.injective (Prod.ext hrow hcol) hslot

 theorem site_cell (S : QMACellSlots cell A) (hA : 0 < A) (q : Q) :
    qmaFineGridCell hA (S.site q) = cell q := by
  apply Prod.ext
  · apply Fin.ext
    change ((S.index q).val+A*(cell q).1.val)/A = (cell q).1.val
    rw [Nat.add_mul_div_left _ _ hA,Nat.div_eq_of_lt (S.index q).isLt,zero_add]
  · rfl

 theorem site_bounds (S : QMACellSlots cell A) (q : Q) (p : QMAGridCell rows width)
    (hne : QMAGridCellsNear (cell q) p) :
    (S.site q).1.val < (p.1.val+2)*A ∧ p.1.val*A ≤ (S.site q).1.val+A ∧
      (S.site q).2.val ≤ p.2.val+1 ∧ p.2.val ≤ (S.site q).2.val+1 := by
  obtain ⟨hr,hr',hc,hc'⟩ := hne
  have hs := (S.index q).isLt
  have hm := Nat.mul_le_mul_right A hr
  have hm' := Nat.mul_le_mul_right A hr'
  change (S.index q).val+A*(cell q).1.val < (p.1.val+2)*A ∧
    p.1.val*A ≤ (S.index q).val+A*(cell q).1.val+A ∧ _
  exact ⟨by nlinarith,by nlinarith,hc,hc'⟩

 theorem route_length (S : QMACellSlots cell A) (p q : Q)
    (a : QMAGridCell rows width) (hp : QMAGridCellsNear (cell p) a)
    (hq : QMAGridCellsNear (cell q) a) :
    qmaManhattanLength (qmaFineGridNat (S.site p)) (qmaFineGridNat (S.site q)) ≤ 3*A+2 := by
  obtain ⟨hp1,hp2,hp3,hp4⟩ := S.site_bounds p a hp
  obtain ⟨hq1,hq2,hq3,hq4⟩ := S.site_bounds q a hq
  simp only [Nat.add_mul] at hp1 hq1
  unfold qmaManhattanLength qmaFineGridNat Nat.dist
  omega

 def color (S : QMACellSlots cell A) (q : Q) : Fin 3 × Fin 3 × Fin A :=
  (⟨(cell q).1.val%3,Nat.mod_lt _ (by decide)⟩,
    ⟨(cell q).2.val%3,Nat.mod_lt _ (by decide)⟩,S.index q)

 theorem color_eq (S : QMACellSlots cell A) {p q : Q} (he : S.color p = S.color q)
    (hr : (cell p).1.val ≤ (cell q).1.val+2) (hr' : (cell q).1.val ≤ (cell p).1.val+2)
    (hc : (cell p).2.val ≤ (cell q).2.val+2) (hc' : (cell q).2.val ≤ (cell p).2.val+2) : p=q := by
  have hrow := congrArg (fun c : Fin 3 × Fin 3 × Fin A => c.1.val) he
  have hcol := congrArg (fun c : Fin 3 × Fin 3 × Fin A => c.2.1.val) he
  have hslot := congrArg (fun c : Fin 3 × Fin 3 × Fin A => c.2.2) he
  change (cell p).1.val%3 = (cell q).1.val%3 at hrow
  change (cell p).2.val%3 = (cell q).2.val%3 at hcol
  apply S.injective _ hslot
  apply Prod.ext <;> apply Fin.ext <;> omega

 theorem color_disjoint {E : Type*} (S : QMACellSlots cell A)
    (location : E → QMAGridCell rows width) (sites : Q → Finset E)
    (hl : ∀ q, ∀ z ∈ sites q, QMAGridCellsNear (location z) (cell q))
    {p q : Q} (hpq : p ≠ q) (he : S.color p = S.color q) : Disjoint (sites p) (sites q) := by
  apply Finset.disjoint_left.mpr
  intro z hz hz'
  have hp := hl p z hz
  have hq := hl q z hz'
  apply hpq
  apply S.color_eq he <;> dsimp [QMAGridCellsNear] at hp hq <;> omega

end QMACellSlots
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumEvenRouteData
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Even route lengths use one singlet leaf. The leaf sits beside the first
interior route point and outside all routed edges. -/

noncomputable section
namespace ContinuumCoulomb
open MediatorGraph
open scoped Classical

structure QMAEvenRouteData (G : QMARationalExchangeGraph) where
  work : G.Edge → ℕ
  position : Fin G.n → ℕ × ℕ
  position_injective : Function.Injective position
  point : G.Edge → ℕ → ℕ × ℕ
  first : ∀ e, point e 0 = position (G.left e)
  last : ∀ e, point e (2*work e+2) = position (G.right e)
  simple : ∀ e i j, i ≤ 2*work e+2 → j ≤ 2*work e+2 → point e i = point e j → i = j
  step : ∀ e i, i < 2*work e+2 → qmaSquareGrid.Adj (point e i) (point e (i+1))
  avoids : ∀ e i v, 0 < i → i < 2*work e+2 → point e i ≠ position v
  disjoint : ∀ e f i j, e ≠ f → 0 < i → i < 2*work e+2 → j ≤ 2*work f+2 →
    point e i ≠ point f j
  leaf : G.Edge → ℕ × ℕ
  leaf_injective : Function.Injective leaf
  leaf_step : ∀ e, qmaSquareGrid.Adj (point e 1) (leaf e)
  leaf_avoids : ∀ e f k, k ≤ 2*work f+2 → leaf e ≠ point f k
  leaf_old : ∀ e v, leaf e ≠ position v

namespace QMAEvenRouteData
variable {G : QMARationalExchangeGraph} (P : QMAEvenRouteData G)

def selected (i : Fin (Finset.univ : Finset G.Edge).card) : G.Edge :=
  qmaSelectedIndex Finset.univ i

theorem selected_injective : Function.Injective (selected (G := G)) := by
  intro i j h
  apply (Finset.univ : Finset G.Edge).equivFin.symm.injective
  exact Subtype.ext h

def freshPosition (i : Fin (Finset.univ : Finset G.Edge).card) (b : Fin 2) : ℕ × ℕ :=
  if b = 0 then P.point (selected i) 1 else P.leaf (selected i)

theorem freshPosition_ne_old (i : Fin (Finset.univ : Finset G.Edge).card) (b : Fin 2)
    (v : Fin G.n) : P.freshPosition i b ≠ P.position v := by
  fin_cases b
  · exact P.avoids _ 1 v (by omega) (by omega)
  · exact P.leaf_old _ v

theorem freshPosition_injective : Function.Injective
    (fun x : Fin (Finset.univ : Finset G.Edge).card × Fin 2 => P.freshPosition x.1 x.2) := by
  rintro ⟨i,a⟩ ⟨j,b⟩ h
  change P.freshPosition i a = P.freshPosition j b at h
  fin_cases a <;> fin_cases b
  · have he : selected i = selected j := by
      by_contra hn
      exact P.disjoint _ _ 1 1 hn (by omega) (by omega) (by omega) h
    have hij := selected_injective he
    subst j
    rfl
  · exact (P.leaf_avoids (selected j) (selected i) 1 (by omega) h.symm).elim
  · exact (P.leaf_avoids (selected i) (selected j) 1 (by omega) h).elim
  · have he := P.leaf_injective h
    have hij := selected_injective he
    subst j
    rfl

def nextPosition (v : Fin (G.n+(Finset.univ : Finset G.Edge).card*2)) : ℕ × ℕ :=
  Sum.elim P.position (fun p => P.freshPosition p.1 p.2) ((vertexEquiv _ _).symm v)

@[simp] theorem nextPosition_old (v : Fin G.n) : P.nextPosition (old _ _ v) = P.position v := by
  simp only [nextPosition,old,Equiv.symm_apply_apply,Sum.elim_inl]

@[simp] theorem nextPosition_fresh (i : Fin (Finset.univ : Finset G.Edge).card) (b : Fin 2) :
    P.nextPosition (fresh _ _ i b) = P.freshPosition i b := by
  simp only [nextPosition,fresh,Equiv.symm_apply_apply,Sum.elim_inr]

theorem nextPosition_injective : Function.Injective P.nextPosition := by
  intro x y h
  obtain ⟨x,rfl⟩ := (vertexEquiv G.n (Finset.univ : Finset G.Edge).card).surjective x
  obtain ⟨y,rfl⟩ := (vertexEquiv G.n (Finset.univ : Finset G.Edge).card).surjective y
  simp only [nextPosition,Equiv.symm_apply_apply] at h
  apply (vertexEquiv _ _).congr_arg
  cases x with
  | inl x =>
    cases y with
    | inl y => exact congrArg Sum.inl (P.position_injective h)
    | inr y => exact (P.freshPosition_ne_old y.1 y.2 x h.symm).elim
  | inr x =>
    cases y with
    | inl y => exact (P.freshPosition_ne_old x.1 x.2 y h).elim
    | inr y => exact congrArg Sum.inr (P.freshPosition_injective h)

def nextWork : QMAPartialPathsEdge (Finset.univ : Finset G.Edge) → ℕ
  | .inl _ => 0
  | .inr (.inl _) => 0
  | .inr (.inr (i,a)) => if a = 1 then P.work (selected i) else 0

def schedule (N : ℚ) : QMAPathSchedule where
  graph := G.subdivide Finset.univ (fun _ => true) N
  work := P.nextWork

end QMAEvenRouteData
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumEvenRoutePlacement
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The even gadget places its interacting vertex at route point one and its
second singlet spin at the reserved leaf. The remaining routes have odd length. -/

noncomputable section
namespace ContinuumCoulomb
open MediatorGraph
open scoped Classical
namespace QMAEvenRouteData
variable {G : QMARationalExchangeGraph} (P : QMAEvenRouteData G)

def nextPoint (e : QMAPartialPathsEdge (Finset.univ : Finset G.Edge)) (k : ℕ) : ℕ × ℕ :=
  match e with
  | .inl e => P.point e.val k
  | .inr (.inl i) => if k = 0 then P.point (selected i) 1 else P.leaf (selected i)
  | .inr (.inr (i,a)) => if a = 0 then P.point (selected i) k
      else P.point (selected i) (2*P.work (selected i)+2-k)

theorem nextPoint_first (e : QMAPartialPathsEdge (Finset.univ : Finset G.Edge)) :
    P.nextPoint e 0 = P.nextPosition (qmaPartialPathsLeft G.left G.right Finset.univ e) := by
  rcases e with e | (i | ⟨i,a⟩)
  · exact (e.property (Finset.mem_univ _)).elim
  · change P.point (selected i) 1 = P.nextPosition (fresh _ _ i 0)
    rw [nextPosition_fresh]
    rfl
  · fin_cases a
    · change P.point (selected i) 0 = P.nextPosition (old _ _ (G.left (selected i)))
      rw [nextPosition_old]
      exact P.first _
    · change P.point (selected i) (2*P.work (selected i)+2) =
        P.nextPosition (old _ _ (G.right (selected i)))
      rw [nextPosition_old]
      exact P.last _

theorem nextPoint_last (e : QMAPartialPathsEdge (Finset.univ : Finset G.Edge)) :
    P.nextPoint e (2*P.nextWork e+1) =
      P.nextPosition (qmaPartialPathsRight G.right Finset.univ (fun _ => true) e) := by
  rcases e with e | (i | ⟨i,a⟩)
  · exact (e.property (Finset.mem_univ _)).elim
  · change P.leaf (selected i) = P.nextPosition (fresh _ _ i 1)
    rw [nextPosition_fresh]
    rfl
  · fin_cases a
    · change P.point (selected i) 1 = P.nextPosition (fresh _ _ i 0)
      rw [nextPosition_fresh]
      rfl
    · change P.point (selected i) (2*P.work (selected i)+2-(2*P.work (selected i)+1)) =
        P.nextPosition (fresh _ _ i 0)
      rw [nextPosition_fresh]
      change P.point (selected i) _ = P.point (selected i) 1
      congr 1
      omega

theorem nextPoint_simple (e : QMAPartialPathsEdge (Finset.univ : Finset G.Edge)) (i j : ℕ)
    (hi : i ≤ 2*P.nextWork e+1) (hj : j ≤ 2*P.nextWork e+1)
    (h : P.nextPoint e i = P.nextPoint e j) : i = j := by
  rcases e with e | (a | ⟨a,b⟩)
  · exact (e.property (Finset.mem_univ _)).elim
  · simp only [nextWork,Nat.mul_zero,Nat.zero_add] at hi hj
    by_cases hi0 : i = 0 <;> by_cases hj0 : j = 0
    · omega
    · have hj1 : j = 1 := by omega
      subst i
      subst j
      exact (P.leaf_avoids (selected a) (selected a) 1 (by omega) h.symm).elim
    · have hi1 : i = 1 := by omega
      subst i
      subst j
      exact (P.leaf_avoids (selected a) (selected a) 1 (by omega) h).elim
    · omega
  · fin_cases b
    · simp [nextWork] at hi hj
      exact P.simple (selected a) i j (by omega) (by omega) h
    · simp [nextWork] at hi hj
      change P.point (selected a) (2*P.work (selected a)+2-i) =
        P.point (selected a) (2*P.work (selected a)+2-j) at h
      have he := P.simple (selected a) _ _ (Nat.sub_le _ _) (Nat.sub_le _ _) h
      omega

theorem nextPoint_step (e : QMAPartialPathsEdge (Finset.univ : Finset G.Edge)) (i : ℕ)
    (hi : i < 2*P.nextWork e+1) : qmaSquareGrid.Adj (P.nextPoint e i) (P.nextPoint e (i+1)) := by
  rcases e with e | (a | ⟨a,b⟩)
  · exact (e.property (Finset.mem_univ _)).elim
  · have hi0 : i = 0 := by simp [nextWork] at hi; omega
    subst i
    exact P.leaf_step (selected a)
  · fin_cases b
    · have hi0 : i = 0 := by simp [nextWork] at hi; omega
      subst i
      exact P.step (selected a) 0 (by omega)
    · simp [nextWork] at hi
      have hk : 2*P.work (selected a)+2-(i+1) < 2*P.work (selected a)+2 := by omega
      have he : 2*P.work (selected a)+2-i = (2*P.work (selected a)+2-(i+1))+1 := by omega
      change qmaSquareGrid.Adj (P.point (selected a) (2*P.work (selected a)+2-i))
        (P.point (selected a) (2*P.work (selected a)+2-(i+1)))
      rw [he]
      exact (P.step (selected a) _ hk).symm

theorem nextPoint_avoids (e : QMAPartialPathsEdge (Finset.univ : Finset G.Edge)) (i : ℕ)
    (v : Fin (G.n+(Finset.univ : Finset G.Edge).card*2))
    (hi0 : 0 < i) (hi : i < 2*P.nextWork e+1) : P.nextPoint e i ≠ P.nextPosition v := by
  rcases e with e | (a | ⟨a,b⟩)
  · exact (e.property (Finset.mem_univ _)).elim
  · simp [nextWork] at hi
    omega
  · fin_cases b
    · simp [nextWork] at hi
      omega
    simp [nextWork] at hi
    have hidx0 : 1 < 2*P.work (selected a)+2-i := by omega
    have hidx : 2*P.work (selected a)+2-i < 2*P.work (selected a)+2 := by omega
    obtain ⟨v,rfl⟩ := (vertexEquiv G.n (Finset.univ : Finset G.Edge).card).surjective v
    rcases v with v | ⟨c,d⟩
    · change P.point (selected a) (2*P.work (selected a)+2-i) ≠ P.nextPosition (old _ _ v)
      rw [nextPosition_old]
      exact P.avoids _ _ v (by omega) hidx
    · change P.point (selected a) (2*P.work (selected a)+2-i) ≠ P.nextPosition (fresh _ _ c d)
      rw [nextPosition_fresh]
      fin_cases d
      · intro h
        by_cases he : selected a = selected c
        · change P.point (selected a) _ = P.point (selected c) 1 at h
          rw [← he] at h
          have hx := P.simple (selected a) _ 1 (Nat.sub_le _ _) (by omega) h
          omega
        · exact P.disjoint _ _ _ 1 he (by omega) hidx (by omega) h
      · intro h
        exact P.leaf_avoids (selected c) (selected a) _ (Nat.sub_le _ _) h.symm

theorem nextPoint_disjoint (e f : QMAPartialPathsEdge (Finset.univ : Finset G.Edge)) (i j : ℕ)
    (hef : e ≠ f) (hi0 : 0 < i) (hi : i < 2*P.nextWork e+1) (hj : j ≤ 2*P.nextWork f+1) :
    P.nextPoint e i ≠ P.nextPoint f j := by
  rcases e with e | (a | ⟨a,b⟩)
  · exact (e.property (Finset.mem_univ _)).elim
  · simp [nextWork] at hi
    omega
  · fin_cases b
    · simp [nextWork] at hi
      omega
    simp [nextWork] at hi
    have hidx0 : 1 < 2*P.work (selected a)+2-i := by omega
    have hidx : 2*P.work (selected a)+2-i < 2*P.work (selected a)+2 := by omega
    intro h
    rcases f with f | (c | ⟨c,d⟩)
    · exact (f.property (Finset.mem_univ _)).elim
    · by_cases hj0 : j = 0
      · change P.point (selected a) _ = (if j = 0 then P.point (selected c) 1 else _) at h
        simp only [hj0,ite_true, if_true] at h
        by_cases he : selected a = selected c
        · rw [← he] at h
          have hx := P.simple (selected a) _ 1 (Nat.sub_le _ _) (by omega) h
          omega
        · exact P.disjoint _ _ _ 1 he (by omega) hidx (by omega) h
      · change P.point (selected a) _ = (if j = 0 then _ else P.leaf (selected c)) at h
        simp only [hj0,ite_false, if_false] at h
        exact P.leaf_avoids (selected c) (selected a) _ (Nat.sub_le _ _) h.symm
    · fin_cases d
      · simp [nextWork] at hj
        change P.point (selected a) _ = P.point (selected c) j at h
        by_cases he : selected a = selected c
        · rw [← he] at h
          have hx := P.simple (selected a) _ j (Nat.sub_le _ _) (by omega) h
          omega
        · exact P.disjoint _ _ _ j he (by omega) hidx (by omega) h
      · simp [nextWork] at hj
        change P.point (selected a) _ = P.point (selected c) (2*P.work (selected c)+2-j) at h
        have he : selected a = selected c := by
          by_contra hn
          exact P.disjoint _ _ _ _ hn (by omega) hidx (Nat.sub_le _ _) h
        have hac := selected_injective he
        subst c
        exact hef rfl

def embedding (N : ℚ) : QMAPathEmbedding (P.schedule N) where
  position := P.nextPosition
  position_injective := P.nextPosition_injective
  point := P.nextPoint
  first := P.nextPoint_first
  last := P.nextPoint_last
  simple := P.nextPoint_simple
  step := P.nextPoint_step
  avoids := P.nextPoint_avoids
  disjoint := P.nextPoint_disjoint

end QMAEvenRouteData
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumEvenRouteRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full even-route realization from the reserved-leaf placement. -/

noncomputable section
namespace ContinuumCoulomb
open MediatorGraph
open scoped Classical
namespace QMAEvenRouteData
variable {G : QMARationalExchangeGraph} (P : QMAEvenRouteData G)

def Bounded (X Y : ℕ) : Prop :=
  (∀ v, (P.position v).1 < X ∧ (P.position v).2 < Y) ∧
  (∀ e k, k ≤ 2*P.work e+2 → (P.point e k).1 < X ∧ (P.point e k).2 < Y) ∧
  ∀ e, (P.leaf e).1 < X ∧ (P.leaf e).2 < Y

end QMAEvenRouteData
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkDegreeBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree control for many fork centers sharing a retained background graph. -/

noncomputable section
namespace ContinuumCoulomb
open MediatorGraph
open scoped BigOperators Classical
variable {ν : Type*} [Fintype ν]

theorem qmaGraphDegree_sum {n : ℕ} {κ : Type*} [Fintype κ]
    (left right : ν → Fin n) (left' right' : κ → Fin n) (v : Fin n) :
    qmaGraphDegree (Sum.elim left left') (Sum.elim right right') v =
      qmaGraphDegree left right v+qmaGraphDegree left' right' v := by
  simp only [qmaGraphDegree,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr]
  rfl

theorem qmaCount_eq_le_one {α β : Type*} [Fintype α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (v : β) :
    (∑ a, if f a = v then 1 else 0 : ℕ) ≤ 1 := by
  simp only [Finset.sum_boole]
  apply Finset.card_le_one.mpr
  intro a ha b hb
  exact hf ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkPorts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Private active ports remain private after a simultaneous fork round. -/

noncomputable section
namespace ContinuumCoulomb
open MediatorGraph
open scoped BigOperators Classical

structure QMAForkPorts (n c : ℕ) (d : Fin c → ℕ) where
  center : Fin c → Fin n
  port : (Σ i, Fin (d i)) → Fin n
  center_injective : Function.Injective center
  port_injective : Function.Injective port
  center_ne_port : ∀ i p, center i ≠ port p

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A repeatable fork stage: only active stars may have large degree. -/

noncomputable section
namespace ContinuumCoulomb
open MediatorGraph
open scoped BigOperators Classical

structure QMAForkState (n c : ℕ) (d : Fin c → ℕ) (ν : Type*) [Fintype ν] where
  ports : QMAForkPorts n c d
  left : ν → Fin n
  right : ν → Fin n
  distinct : ∀ e, left e ≠ right e
  degree_le : ∀ v, qmaGraphDegree left right v ≤ 3
  center_degree : ∀ i, qmaGraphDegree left right (ports.center i) = 0
  port_degree : ∀ p, qmaGraphDegree left right (ports.port p) ≤ 1

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkStateDegree
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree and size of the entire graph represented by active stars and background edges. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical
namespace QMAForkState
variable {n c : ℕ} {d : Fin c → ℕ} {ν : Type*} [Fintype ν]
variable (G : QMAForkState n c d ν)

def fullLeft : ν ⊕ (Σ i, Fin (d i)) → Fin n :=
  Sum.elim G.left (fun p => G.ports.center p.1)
def fullRight : ν ⊕ (Σ i, Fin (d i)) → Fin n :=
  Sum.elim G.right G.ports.port

theorem full_center_degree (i : Fin c) :
    qmaGraphDegree G.fullLeft G.fullRight (G.ports.center i) = d i := by
  rw [fullLeft,fullRight,qmaGraphDegree_sum,G.center_degree,zero_add]
  have hp (p : Σ i, Fin (d i)) : G.ports.port p ≠ G.ports.center i :=
    (G.ports.center_ne_port i p).symm
  simp only [qmaGraphDegree,hp,or_false,G.ports.center_injective.eq_iff,Fintype.sum_sigma]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

theorem full_noncenter_degree (v : Fin n) (hv : ∀ i, G.ports.center i ≠ v) :
    qmaGraphDegree G.fullLeft G.fullRight v ≤ 3 := by
  rw [fullLeft,fullRight,qmaGraphDegree_sum]
  have hc : qmaGraphDegree (fun p : Σ i, Fin (d i) => G.ports.center p.1) G.ports.port v =
      ∑ p, if G.ports.port p = v then 1 else 0 := by
    simp only [qmaGraphDegree,hv,false_or]
  rw [hc]
  by_cases hp : ∃ p, G.ports.port p = v
  · obtain ⟨p,rfl⟩ := hp
    have hb := G.port_degree p
    have hs := qmaCount_eq_le_one G.ports.port G.ports.port_injective (G.ports.port p)
    omega
  · have hn (p : Σ i, Fin (d i)) : G.ports.port p ≠ v := fun h => hp ⟨p,h⟩
    simpa [hn] using G.degree_le v

theorem full_degree_le_three (hd : ∀ i, d i ≤ 3) (v : Fin n) :
    qmaGraphDegree G.fullLeft G.fullRight v ≤ 3 := by
  by_cases h : ∃ i, G.ports.center i = v
  · obtain ⟨i,rfl⟩ := h
    rw [G.full_center_degree]
    exact hd i
  · exact G.full_noncenter_degree v (by simpa using h)

end QMAForkState
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkRounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Constantly many actual fork rounds give a degree-three graph of linear size. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

structure QMAForkNetwork (c : ℕ) where
  n : ℕ
  degree : Fin c → ℕ
  Edge : Type
  [edgeFinite : Fintype Edge]
  state : QMAForkState n c degree Edge

attribute [instance] QMAForkNetwork.edgeFinite

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSpatialExchange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual rational four-spin simulator retains bounded spatial density. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

structure QMASpatialExchangeModel (A B : ℕ) where
  n : ℕ
  Term : Type
  [termFinite : Fintype Term]
  left : Term → Fin n
  right : Term → Fin n
  distinct : ∀ e, left e ≠ right e
  weight : Term → ℚ
  constant : ℚ
  rows : ℕ
  width : ℕ
  cell : Fin n → QMAGridCell rows width
  anchor : Term → QMAGridCell rows width
  geometry : ∀ e, QMAGridCellsNear (cell (left e)) (anchor e) ∧
    QMAGridCellsNear (cell (right e)) (anchor e)
  qubitDensity : ∀ p, (Finset.univ.filter (fun i => cell i = p)).card ≤ A
  termDensity : ∀ p, (Finset.univ.filter (fun e => anchor e = p)).card ≤ B
  qubitSlots : QMACellSlots cell A := QMACellSlots.ofDensity qubitDensity
  termSlots : QMACellSlots anchor B := QMACellSlots.ofDensity termDensity

attribute [instance] QMASpatialExchangeModel.termFinite

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrdinalSpatial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Replace the abstract default slots by the explicit ordinal choice on the
encoded spin and interaction labels. The finite Hamiltonian is unchanged. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

namespace QMACellSlots
 def transport {Q R : Type*} {rows width A : ℕ} {cell : Q → QMAGridCell rows width}
    (e : Q ≃ R) (S : QMACellSlots (cell ∘ e.symm) A) : QMACellSlots cell A where
  index q := S.index (e q)
  injective := by
    intro q r hc hs
    apply e.injective
    apply S.injective _ hs
    simpa only [Function.comp_apply,Equiv.symm_apply_apply] using hc
end QMACellSlots

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRouteProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal polynomial programs for the lattice route length and each route point. -/

noncomputable section
namespace ContinuumCoulomb.QuantumRouteCode
open ExactQuantumFactoring.BitStackProgram

abbrev Pair := ℕ × ℕ

end ContinuumCoulomb.QuantumRouteCode

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRoutingTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite source cells, internal visits and crossing cells determine every
routing permission. These tests inspect finite encoded lists, including both
orientations of each internal port pair. -/

noncomputable section
namespace ContinuumCoulomb.QuantumRoutingTable
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

abbrev Visit := Pair × Pair
abbrev Table := List Pair × (List Visit × List Pair)

end ContinuumCoulomb.QuantumRoutingTable

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceNormalizedLattice
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_internal _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_old _root_.OAI.ContinuumCoulomb.MediatorIteration.Bonds.toList_length _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.contactEdge_left _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.contactEdge_right _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal coefficient rounding and zero deletion preserve the original
square-lattice geometry and the simple unordered edge enumeration. -/

noncomputable section
namespace ContinuumCoulomb.SourceNormalizedSpectrum
open MediatorIteration MediatorListProgram SourceBondLists

theorem rounded_injective (d : SquareLatticeHeisenberg) (M : ℕ) :
    Function.Injective (fun e : Fin d.edges => ((d.left e).val, (d.right e).val,
      SourceCoefficientRounding.coefficient M (d.coefficient e))) := by
  intro e f h
  by_contra hne
  apply (d.edge_simple e f hne).1
  exact ⟨Fin.ext (congrArg Prod.fst h),
    Fin.ext (congrArg (fun b : _root_.OAI.ContinuumCoulomb.MediatorListProgram.Bond => b.2.1) h)⟩

theorem retained_nodup (d : SquareLatticeHeisenberg) (M : ℕ) : (retained d M).Nodup :=
  (List.nodup_ofFn_ofInjective (rounded_injective d M)).filter _

/-- Every retained bond has the same two endpoints as a definite original
source bond; only its coefficient has been rounded. -/
theorem family_original_edge (d : SquareLatticeHeisenberg) (M : ℕ)
    (e : Fin (retained d M).length) :
    ∃ i : Fin d.edges, (family d M).left e = d.left i ∧
      (family d M).right e = d.right i ∧
      (retained d M).get e = ((d.left i).val, (d.right i).val,
        SourceCoefficientRounding.coefficient M (d.coefficient i)) := by
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp (List.mem_filter.mp (List.get_mem (retained d M) e)).1
  refine ⟨i, ?_, ?_, hi.symm⟩
  · exact Fin.ext (congrArg Prod.fst hi.symm)
  · exact Fin.ext (congrArg (fun b : _root_.OAI.ContinuumCoulomb.MediatorListProgram.Bond => b.2.1) hi.symm)

theorem family_adjacent (d : SquareLatticeHeisenberg) (M : ℕ)
    (e : Fin (retained d M).length) :
    Int.natAbs ((d.coordinate ((family d M).left e)).1 -
        (d.coordinate ((family d M).right e)).1) +
      Int.natAbs ((d.coordinate ((family d M).left e)).2 -
        (d.coordinate ((family d M).right e)).2) = 1 := by
  obtain ⟨i, hi, hj, _⟩ := family_original_edge d M e
  rw [hi, hj]
  exact d.adjacent i

theorem family_edge_simple (d : SquareLatticeHeisenberg) (M : ℕ)
    (e f : Fin (retained d M).length) (hef : e ≠ f) :
    ¬((family d M).left e = (family d M).left f ∧
      (family d M).right e = (family d M).right f) ∧
    ¬((family d M).left e = (family d M).right f ∧
      (family d M).right e = (family d M).left f) := by
  obtain ⟨i, hei, hei', hgeti⟩ := family_original_edge d M e
  obtain ⟨j, hfj, hfj', hgetj⟩ := family_original_edge d M f
  have hij : i ≠ j := by
    intro h
    subst j
    exact hef ((retained_nodup d M).injective_get (hgeti.trans hgetj.symm))
  have hs := d.edge_simple i j hij
  constructor
  · rintro ⟨hl, hr⟩
    exact hs.1 ⟨hei.symm.trans (hl.trans hfj), hei'.symm.trans (hr.trans hfj')⟩
  · rintro ⟨hl, hr⟩
    exact hs.2 ⟨hei.symm.trans (hl.trans hfj'), hei'.symm.trans (hr.trans hfj)⟩

/-- The normalized graph in the same geometric source type. Its thresholds
are inherited only to satisfy the record; all coefficient and matrix
normalization theorems continue to use the literal `family` definition. -/
def lattice (d : SquareLatticeHeisenberg) (M : ℕ) : SquareLatticeHeisenberg where
  vertices := d.vertices
  vertices_pos := d.vertices_pos
  coordinate := d.coordinate
  coordinate_injective := d.coordinate_injective
  edges := (retained d M).length
  left := (family d M).left
  right := (family d M).right
  adjacent := family_adjacent d M
  edge_simple := family_edge_simple d M
  coefficient := (family d M).weight
  lower := d.lower
  upper := d.upper
  gap_pos := d.gap_pos

@[simp] theorem lattice_bonds (d : SquareLatticeHeisenberg) (M : ℕ) :
    (lattice d M).bonds = family d M := rfl

@[simp] theorem lattice_coordinate (d : SquareLatticeHeisenberg) (M : ℕ) :
    (lattice d M).coordinate = d.coordinate := rfl

end ContinuumCoulomb.SourceNormalizedSpectrum

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceGeometryBounds
attribute [-simp] _root_.OAI.ContinuumCoulomb.MediatorIteration.Bonds.toList_length _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial site counts, coordinate extent and coefficient ranges for
the literal normalized source passed to the contact realization. -/

noncomputable section
namespace ContinuumCoulomb.SourceMetadataProgram
open ContactMediator

def geometricSource (k : ℕ) (d : BinaryHeisenberg) (h : d.Valid) : SquareLatticeHeisenberg :=
  SourceNormalizedSpectrum.lattice (d.toSource h) (roundingDenominator k d)

@[simp] theorem geometricSource_bonds (k : ℕ) (d : BinaryHeisenberg) (h : d.Valid) :
    (geometricSource k d h).bonds =
      SourceNormalizedSpectrum.family (d.toSource h) (roundingDenominator k d) := rfl

end ContinuumCoulomb.SourceMetadataProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceFinalGraph
attribute [-simp] _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact final graph indexed by the literal output vertex count.
Changing only the proof of that count preserves every bond and weight. -/

noncomputable section
namespace ContinuumCoulomb.MediatorIteration

def Bonds.castSites {n n' r : ℕ} (h : n=n') (F : Bonds n r) : Bonds n' r := h ▸ F

@[simp] theorem Bonds.castSites_toList {n n' r : ℕ} (h : n=n') (F : Bonds n r) :
    (F.castSites h).toList=F.toList := by cases h; rfl

@[simp] theorem Bonds.castSites_weight {n n' r : ℕ} (h : n=n') (F : Bonds n r) :
    (F.castSites h).weight=F.weight := by cases h; rfl

@[simp] theorem Bonds.castSites_left {n n' r : ℕ} (h : n=n') (F : Bonds n r) (e : Fin r) :
    (F.castSites h).left e=Fin.cast h (F.left e) := by cases h; rfl

@[simp] theorem Bonds.castSites_right {n n' r : ℕ} (h : n=n') (F : Bonds n r) (e : Fin r) :
    (F.castSites h).right e=Fin.cast h (F.right e) := by cases h; rfl

end ContinuumCoulomb.MediatorIteration

end

end OAI
end


