-- Prove2me | Definitions.Def_OAIQ092A007
-- name    : OAIQ092A007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T19:50:56.742994+00:00
-- url     : https://prove2.me/theorems/f1523845-a455-446e-a7a2-21438637bc2d
-- title:
--   Definitions bundle OAIQ092A007 of the split of OpenAI, QMA-hardness of continuum Coulomb energy (result family 275)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ContinuumCoulomb.binary_coulomb_qmaHard` and `OAI.ContinuumCoulomb.unit_coulomb_qmaHard`, carved from OpenAI's openai/math development (OpenAI, *QMA-hardness of continuum Coulomb energy (result family 275)*, OpenAI Math Release, September 24, 2026, result family 275, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 375 declarations of OpenAI's Lean: 299 definitions, 1 instance and 75 theorems. The definitions and types are `OAI.ContinuumCoulomb.QuantumOrderedLabelCompile.finalEnergy`, `OAI.ContinuumCoulomb.QuantumOrderedXZ.energy`, `OAI.ContinuumCoulomb.QuantumOrderedXZ.threeEnergy`, `OAI.ContinuumCoulomb.QuantumOrderedXZ.twoEnergy`, `OAI.ContinuumCoulomb.QuantumOrderedXZ.xzThreeEnergy`, `OAI.ContinuumCoulomb.QuantumPaddedLocal.reindex`, `OAI.ContinuumCoulomb.QuantumPropagationOrder.term`, `OAI.ContinuumCoulomb.RationalBoxRound.value`, `OAI.ContinuumCoulomb.RationalHeatBox.spatialNode`, `OAI.ContinuumCoulomb.RationalHeatBox.timeEndpoint`, `OAI.ContinuumCoulomb.RawCoulombSample.inBox`, `OAI.ContinuumCoulomb.RawCoulombSample.sampled`, `OAI.ContinuumCoulomb.SlabOriginQuadrature.capped`, `OAI.ContinuumCoulomb.SourceMetadataProgram.finalBound`, `OAI.ContinuumCoulomb.SourceNuclearProgram.amplification`, `OAI.ContinuumCoulomb.SourcePhysicalThreshold.horizontalRadius`, `OAI.ContinuumCoulomb.SourcePhysicalThreshold.mesh`, `OAI.ContinuumCoulomb.SourcePhysicalThreshold.slabHorizontal`, `OAI.ContinuumCoulomb.SourcePhysicalThreshold.slabVertical`, `OAI.ContinuumCoulomb.SourcePhysicalThreshold.verticalRadius`, `OAI.ContinuumCoulomb.SourcePositiveProgram.graphEdgeCount`, `OAI.ContinuumCoulomb.SourcePositiveProgram.sourceFamily`, `OAI.ContinuumCoulomb.SpatialPath`, `OAI.ContinuumCoulomb.SquareLatticeHeisenberg.withCoefficients`, `OAI.ContinuumCoulomb.UniformFlowDerivativeBound`, `OAI.ContinuumCoulomb.actualMediatorCoupling`, `OAI.ContinuumCoulomb.actualMediatorHighBlock`, `OAI.ContinuumCoulomb.actualMediatorLowBlock`, `OAI.ContinuumCoulomb.actualMediatorWeight`, `OAI.ContinuumCoulomb.adjustedContactVertex`, `OAI.ContinuumCoulomb.assembleMediator`, `OAI.ContinuumCoulomb.atomicThresholdOutput`, `OAI.ContinuumCoulomb.bellMediatorHamiltonian`, `OAI.ContinuumCoulomb.bellMediatorPenaltyMatrix`, `OAI.ContinuumCoulomb.classicalTensorState`, `OAI.ContinuumCoulomb.complexMollification`, `OAI.ContinuumCoulomb.contactGadgetLinked`, `OAI.ContinuumCoulomb.contactGadgetPosition`, `OAI.ContinuumCoulomb.contactGadgetRightNode`, `OAI.ContinuumCoulomb.coreOrbitalMass` and 259 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, lean/OAI/Computability, lean/OAI/MathematicalPhysics, in whole or in part: `Analysis_FunctionalSpaces_Sobolev_Euclidean_H1`, `BiholderTransport_LocalFlow_ImplicitODE`, `ContinuumCoulomb_ManyBody_ElectronSlotBound`, `ContinuumCoulomb_ManyBody_FiniteAtomicOutputs`, `ContinuumCoulomb_ManyBody_FiniteTensorProjection`, `ContinuumCoulomb_ManyBody_FiniteTensorState`, `ContinuumCoulomb_ManyBody_GlobalSinglet`, `ContinuumCoulomb_ManyBody_HeisenbergOffsets`, `ContinuumCoulomb_ManyBody_HubbardReduction`, `ContinuumCoulomb_ManyBody_MediatorBlocks`, `ContinuumCoulomb_ManyBody_MediatorCompression`, `ContinuumCoulomb_ManyBody_MediatorEffective`, `ContinuumCoulomb_ManyBody_MediatorForms`, `ContinuumCoulomb_ManyBody_MediatorOffsets`, `ContinuumCoulomb_ManyBody_MediatorPhysical`, `ContinuumCoulomb_ManyBody_MediatorSector`, `ContinuumCoulomb_ManyBody_MediatorSpectrum`, `ContinuumCoulomb_ManyBody_OrthonormalLocalizedModes`, `ContinuumCoulomb_ManyBody_RepulsionBound`, `ContinuumCoulomb_ManyBody_RepulsionCross`, `ContinuumCoulomb_Nuclei_Cubature`, `ContinuumCoulomb_Nuclei_DensitySynthesis`, `ContinuumCoulomb_Nuclei_FlowPathJets`, `ContinuumCoulomb_Nuclei_FlowUniform`, `ContinuumCoulomb_Nuclei_GaussPositionCell`, `ContinuumCoulomb_Nuclei_NuclearGridPotential`, `ContinuumCoulomb_Nuclei_NuclearPerturbedComplement`, `ContinuumCoulomb_Nuclei_SlabConfinement`, `ContinuumCoulomb_Nuclei_SlabCoordinates`, `ContinuumCoulomb_Nuclei_SlabOrbitalResidual`, `ContinuumCoulomb_Nuclei_SlabOriginQuadrature`, `ContinuumCoulomb_Nuclei_SlabPlanarTail`, `ContinuumCoulomb_Nuclei_SlabRegularity`, `ContinuumCoulomb_Nuclei_SlabRegularization`, `ContinuumCoulomb_Nuclei_SlabVerticalCoordinates`, `ContinuumCoulomb_OneParticle_BoundedFormCross`, `ContinuumCoulomb_OneParticle_ClassicalTensor`, `ContinuumCoulomb_OneParticle_ComplexMollification`, `ContinuumCoulomb_OneParticle_ContactAdjustment`, `ContinuumCoulomb_OneParticle_ContactBaseSeparation`, `ContinuumCoulomb_OneParticle_ContactExtent`, `ContinuumCoulomb_OneParticle_ContactGadgets`, `ContinuumCoulomb_OneParticle_ContactPathBounds`, `ContinuumCoulomb_OneParticle_ContactStrips`, `ContinuumCoulomb_OneParticle_CoreOrbitalProjection`, `ContinuumCoulomb_OneParticle_CorrectedOneElectronProjection`, `ContinuumCoulomb_OneParticle_CorrectedResidualPairing`, `ContinuumCoulomb_OneParticle_CoulombCubeModulus`, `ContinuumCoulomb_OneParticle_CoulombQuadrature`, `ContinuumCoulomb_OneParticle_CubeIntegral`, `ContinuumCoulomb_OneParticle_GridNuclei`, `ContinuumCoulomb_OneParticle_H1BoundedForm`, `ContinuumCoulomb_OneParticle_H1FiniteProjection`, `ContinuumCoulomb_OneParticle_H1GraphCore`, `ContinuumCoulomb_OneParticle_LocalizedCoulomb`, `ContinuumCoulomb_OneParticle_LocalizedCoulombNumerics`, `ContinuumCoulomb_OneParticle_LocalizedCoulombRadial`, `ContinuumCoulomb_OneParticle_LocalizedDualMatrix`, `ContinuumCoulomb_OneParticle_LocalizedFockStates`, `ContinuumCoulomb_OneParticle_LocalizedGramSpacing`, `ContinuumCoulomb_OneParticle_LocalizedLeakage`, `ContinuumCoulomb_OneParticle_LocalizedLinearOrbitals`, `ContinuumCoulomb_OneParticle_LocalizedMomentTail`, `ContinuumCoulomb_OneParticle_LocalizedOrbitalGram`, `ContinuumCoulomb_OneParticle_LocalizedRawDensity`, `ContinuumCoulomb_OneParticle_LocalizedTransition`, `ContinuumCoulomb_OneParticle_ManufacturedWeakResidual`, `ContinuumCoulomb_OneParticle_ManufacturedWellField`, `ContinuumCoulomb_OneParticle_PlanarCutoffTail`, `ContinuumCoulomb_OneParticle_PlanarDistributionAxes`, `ContinuumCoulomb_OneParticle_PlanarGroundIdentity`, `ContinuumCoulomb_OneParticle_PlanarHeatBoxBounds`, `ContinuumCoulomb_OneParticle_PlanarHeatBoxCoordinates`, `ContinuumCoulomb_OneParticle_PlanarHeatDifferential`, `ContinuumCoulomb_OneParticle_PlanarHeatTruncation`, `ContinuumCoulomb_OneParticle_PlanarHoppingBounds`, `ContinuumCoulomb_OneParticle_PlanarLowerTail`, `ContinuumCoulomb_OneParticle_PlanarNormalizationBox`, `ContinuumCoulomb_OneParticle_PlanarNormalizationTail`, `ContinuumCoulomb_OneParticle_PlanarNormalized`, `ContinuumCoulomb_OneParticle_PlanarOverlap`, `ContinuumCoulomb_OneParticle_PlanarPartition`, `ContinuumCoulomb_OneParticle_PlanarRadial`, `ContinuumCoulomb_OneParticle_PlanarSliceProjection`, `ContinuumCoulomb_OneParticle_PlanarWeakConstant`, `ContinuumCoulomb_OneParticle_RationalBoxRound`, `ContinuumCoulomb_OneParticle_RationalHeatPlaneError`, `ContinuumCoulomb_OneParticle_RationalResolventError`, `ContinuumCoulomb_OneParticle_RealMollification`, `ContinuumCoulomb_OneParticle_RealOneElectronState`, `ContinuumCoulomb_OneParticle_SmoothCutoffApproximation`, `ContinuumCoulomb_OneParticle_SobolevDensity`, `ContinuumCoulomb_OneParticle_SplitCoordinates`, `ContinuumCoulomb_OneParticle_SplitPullback`, `ContinuumCoulomb_OneParticle_SplitSpectralBudget`, `ContinuumCoulomb_OneParticle_SplitTestFunctions`, `ContinuumCoulomb_OneParticle_UnitBinaryInclusion`, `ContinuumCoulomb_OneParticle_VerticalCappedForm`, `ContinuumCoulomb_OneParticle_VerticalCutoffTail`, `ContinuumCoulomb_OneParticle_VerticalMode`, `ContinuumCoulomb_OneParticle_VerticalResidual`, `ContinuumCoulomb_OneParticle_VerticalSliceProjection`, `ContinuumCoulomb_OneParticle_WellCover`, `ContinuumCoulomb_Programs_RawCoulombSample`, `ContinuumCoulomb_Programs_RawDensityModulus`, `ContinuumCoulomb_Programs_SourceNuclearProgram`, `ContinuumCoulomb_Programs_UnitBinaryProgram`, `ContinuumCoulomb_Quantum_QuantumAncilla`, `ContinuumCoulomb_Quantum_QuantumAncillaCount`, `ContinuumCoulomb_Quantum_QuantumBlockBasis`, `ContinuumCoulomb_Quantum_QuantumBlockBudget`, `ContinuumCoulomb_Quantum_QuantumBlockEdges`, `ContinuumCoulomb_Quantum_QuantumBlockFull`, `ContinuumCoulomb_Quantum_QuantumBlockHamiltonian`, `ContinuumCoulomb_Quantum_QuantumClockSector`, `ContinuumCoulomb_Quantum_QuantumCrossingEffective`, `ContinuumCoulomb_Quantum_QuantumDiagonalTensor`, `ContinuumCoulomb_Quantum_QuantumEndpoint`, `ContinuumCoulomb_Quantum_QuantumForkEffective`, `ContinuumCoulomb_Quantum_QuantumFourAxis`, `ContinuumCoulomb_Quantum_QuantumFourBasis`, `ContinuumCoulomb_Quantum_QuantumFourFields`, `ContinuumCoulomb_Quantum_QuantumFourGapCertificate`, `ContinuumCoulomb_Quantum_QuantumFourPositive`, `ContinuumCoulomb_Quantum_QuantumFourSpin`, `ContinuumCoulomb_Quantum_QuantumFourTensorCross`, `ContinuumCoulomb_Quantum_QuantumFourTensorEffective`, `ContinuumCoulomb_Quantum_QuantumFourTensorEffectiveError`, `ContinuumCoulomb_Quantum_QuantumFourTensorFamily`, `ContinuumCoulomb_Quantum_QuantumFourTensorFamilyAccuracy`, `ContinuumCoulomb_Quantum_QuantumFourTensorForms`, `ContinuumCoulomb_Quantum_QuantumFourTensorFullFamily`, `ContinuumCoulomb_Quantum_QuantumFourTensorGap`, `ContinuumCoulomb_Quantum_QuantumFourTensorGround`, `ContinuumCoulomb_Quantum_QuantumFourTensorHilbert`, `ContinuumCoulomb_Quantum_QuantumFourTensorOnsite`, `ContinuumCoulomb_Quantum_QuantumFourTensorOperatorBounds`, `ContinuumCoulomb_Quantum_QuantumFourTensorWeighted`, `ContinuumCoulomb_Quantum_QuantumGateProduct`, `ContinuumCoulomb_Quantum_QuantumGridFrame`, `ContinuumCoulomb_Quantum_QuantumHistory`, `ContinuumCoulomb_Quantum_QuantumHistoryEnergy`, `ContinuumCoulomb_Quantum_QuantumHistorySpectrum`, `ContinuumCoulomb_Quantum_QuantumHistoryWitness`, `ContinuumCoulomb_Quantum_QuantumInputProjection`, `ContinuumCoulomb_Quantum_QuantumListScheduleGeometry`, `ContinuumCoulomb_Quantum_QuantumLocalCore`, `ContinuumCoulomb_Quantum_QuantumOrderedLabelEnergy`, `ContinuumCoulomb_Quantum_QuantumOrderedXZEnergy`, `ContinuumCoulomb_Quantum_QuantumPaddedBasis`, `ContinuumCoulomb_Quantum_QuantumPaddedLocal`, `ContinuumCoulomb_Quantum_QuantumParallelGraph`, `ContinuumCoulomb_Quantum_QuantumPartialPaths`, `ContinuumCoulomb_Quantum_QuantumPathSubdivision`, `ContinuumCoulomb_Quantum_QuantumPinnedClock`, `ContinuumCoulomb_Quantum_QuantumPropagationOrder`, `ContinuumCoulomb_Quantum_QuantumReferencePenalty`, `ContinuumCoulomb_Quantum_QuantumReferenceWalls`, `ContinuumCoulomb_Quantum_QuantumRoutingBlocks`, `ContinuumCoulomb_Quantum_QuantumRoutingForms`, `ContinuumCoulomb_Quantum_QuantumRoutingPhysical`, `ContinuumCoulomb_Quantum_QuantumRowTransfer`, `ContinuumCoulomb_Quantum_QuantumSingletStar`, `ContinuumCoulomb_Quantum_QuantumTensorSucc`, `ContinuumCoulomb_Quantum_QuantumUnaryClock`, `ContinuumCoulomb_Quantum_QuantumUnaryPenalty`, `ContinuumCoulomb_Quantum_QuantumWireGrid`, `ContinuumCoulomb_Quantum_QuantumWireRelabel`, `ContinuumCoulomb_Quantum_QuantumWireSwap`, `ContinuumCoulomb_Quantum_QuantumXZFamilySplit`, `ContinuumCoulomb_Quantum_QuantumXZHeisenberg`, `ContinuumCoulomb_Quantum_QubitMediatorForms`, `ContinuumCoulomb_Quantum_QubitMediatorHilbert`, `ContinuumCoulomb_Quantum_QubitMediatorMatrix`, `ContinuumCoulomb_Quantum_QubitMediatorPenalty`, `ContinuumCoulomb_Quantum_QubitMediatorPhysical`, `ContinuumCoulomb_Quantum_QubitMediatorTrial`, `ContinuumCoulomb_Quantum_QubitPhase`, `ContinuumCoulomb_Quantum_QubitPhasePhysical`, `ContinuumCoulomb_Quantum_QubitSubdivisionDecomposition`, `ContinuumCoulomb_Quantum_QubitSubdivisionLocalFamily`, `ContinuumCoulomb_Quantum_QubitSubdivisionMatrix`, `ContinuumCoulomb_Quantum_QubitThirdGadget`, `ContinuumCoulomb_Quantum_QubitThirdPhased`, `ContinuumCoulomb_Reduction_PhysicalOneElectronLower`, `ContinuumCoulomb_Reduction_SourceFinalGraph`, `ContinuumCoulomb_Reduction_SourceHamiltonian`, `ContinuumCoulomb_Reduction_SourceNormalizationCorrectness`, `ContinuumCoulomb_Reduction_SourcePhysicalThreshold`, `ContinuumCoulomb_Reduction_SourcePositiveBounds`, `ContinuumCoulomb_Reduction_SourcePositiveCorrectness`, `ContinuumCoulomb_Reduction_SourceSpectrum`, `CoulombRadii_FieldAnalysis_ConfigurationMeasurableEquiv`, `CoulombRadii_FieldAnalysis_FermionicCoefficients`, `CoulombRadii_FieldAnalysis_SlotTensor`, `CoulombRadii_FormDomain_HardyMollifier`, `CoulombRadii_Packets_CoulombKernel`, `CoulombRadii_Variational_CorrectionDensity`, `Laughlin_Exterior_OccupationMetric`, `Laughlin_Exterior_Scaling`, `Laughlin_Fock_Adjoint`, `Laughlin_Fock_Annihilation`, `Laughlin_Fock_Creation`, `Laughlin_Model`, `Laughlin_Tensor_ExteriorContraction`, `Laughlin_Tensor_ExteriorIsometry`, `Laughlin_Tensor_ExteriorRotation`.
--
--   **Imports.** It imports the published bundle `Def_ContinuumCoulombHardness`; the bundles `OAIQ092A000`, `OAIQ092A001`, `OAIQ092A002` and `OAIQ092A003` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ092A009`, `OAIQ092A012`, `OAIQ092A013`, `OAIQ092A014`, `OAIQ092A015`, `OAIQ092A016` and `OAIQ092A017`; the statements `OAI.ContinuumCoulomb.ContactCalibratedGeometry.calibrated_edge_residual`, `OAI.ContinuumCoulomb.QuantumOrderedXZ.threeEnergy_error`, `OAI.ContinuumCoulomb.finiteTensorState_form_approximation`, `OAI.ContinuumCoulomb.qmaFourRawCorrelation_eq_row0`, `OAI.ContinuumCoulomb.qmaFourRawCorrelation_eq_row1`, `OAI.ContinuumCoulomb.qmaFourRawCorrelation_eq_row2`, `OAI.ContinuumCoulomb.qmaFourRawCorrelation_eq_row3`, `OAI.ContinuumCoulomb.qmaFourRawEncoding_action`, `OAI.ContinuumCoulomb.qmaFourSpinRawAction_eigen_row0`, `OAI.ContinuumCoulomb.qmaFourSpinRawAction_eigen_row1`, `OAI.ContinuumCoulomb.qmaFourSpinRawAction_eigen_row2`, `OAI.ContinuumCoulomb.qmaFourSpinRawAction_eigen_row3`, `OAI.ContinuumCoulomb.qmaFourSpinRawAction_orthogonal_row0`, `OAI.ContinuumCoulomb.qmaFourSpinRawAction_orthogonal_row1`, `OAI.ContinuumCoulomb.qmaFourSpinRawAction_orthogonal_row2`, `OAI.ContinuumCoulomb.qmaFourSpinRawAction_orthogonal_row3`, `OAI.ContinuumCoulomb.qmaFourSpinRawAction_table`, `OAI.ContinuumCoulomb.qmaFourTensorFull_accuracy_of_budget`, `OAI.ContinuumCoulomb.qmaFourTensorFull_effective`, `OAI.ContinuumCoulomb.qmaFourTensorInverse_high`, `OAI.ContinuumCoulomb.qmaFourTensorPadded_symmetric`, `OAI.ContinuumCoulomb.qmaFourTensorPhysical_symmetric`, `OAI.ContinuumCoulomb.qmaFourTensor_padded_gap` and `OAI.ContinuumCoulomb.qmaThirdGadget_polynomial_accuracy`; the proofs of `OAI.ContinuumCoulomb.QuantumOrderedXZ.threeEnergy_error`, `OAI.ContinuumCoulomb.finiteTensorState_form_approximation`, `OAI.ContinuumCoulomb.qmaFourRawCorrelation_eq_row0`, `OAI.ContinuumCoulomb.qmaFourRawCorrelation_eq_row1`, `OAI.ContinuumCoulomb.qmaFourRawCorrelation_eq_row2`, `OAI.ContinuumCoulomb.qmaFourRawCorrelation_eq_row3`, `OAI.ContinuumCoulomb.qmaFourRawEncoding_action`, `OAI.ContinuumCoulomb.qmaFourSpinRawAction_eigen_row0`, `OAI.ContinuumCoulomb.qmaFourSpinRawAction_eigen_row1`, `OAI.ContinuumCoulomb.qmaFourSpinRawAction_eigen_row2`, `OAI.ContinuumCoulomb.qmaFourSpinRawAction_eigen_row3`, `OAI.ContinuumCoulomb.qmaFourSpinRawAction_orthogonal_row0`, `OAI.ContinuumCoulomb.qmaFourSpinRawAction_orthogonal_row1`, `OAI.ContinuumCoulomb.qmaFourSpinRawAction_orthogonal_row2`, `OAI.ContinuumCoulomb.qmaFourSpinRawAction_orthogonal_row3`, `OAI.ContinuumCoulomb.qmaFourSpinRawAction_table`, `OAI.ContinuumCoulomb.qmaFourTensorFull_accuracy_of_budget`, `OAI.ContinuumCoulomb.qmaFourTensorFull_effective`, `OAI.ContinuumCoulomb.qmaFourTensorInverse_high`, `OAI.ContinuumCoulomb.qmaFourTensorPadded_symmetric`, `OAI.ContinuumCoulomb.qmaFourTensorPhysical_symmetric`, `OAI.ContinuumCoulomb.qmaFourTensor_padded_gap`, `OAI.ContinuumCoulomb.qmaThirdGadget_polynomial_accuracy` and `OAI.ContinuumCoulomb.qmaXZSubdivision_accuracy`.
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
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
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
import Mathlib.Data.Finset.Sort
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
import Mathlib.NumberTheory.Real.Irrational
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
import Definitions.Def_OAIQ092A000
import Definitions.Def_OAIQ092A001
import Definitions.Def_OAIQ092A002
import Definitions.Def_OAIQ092A003

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

attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instMeasurableSpace_solutions
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instBorelSpace_solutions
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instOpensMeasurableSpace_solutions
variable (μ : Measure E) [IsFiniteMeasureOnCompacts μ]

/-- `H¹` is complete (a Hilbert space once the ambient `L²` spaces are). -/
instance instCompleteSpace_h1 : CompleteSpace (↥(h1 (μ := μ) (E := E))) := by
  classical
  exact (isClosed_h1 (μ := μ) (E := E)).isComplete.completeSpace_coe

/-- The continuous gradient map `H¹ → L²(E)`. -/
noncomputable def h1ToL2Grad : (↥(h1 (μ := μ) (E := E))) →L[ℝ] L2E (μ := μ) :=
  (ContinuousLinearMap.snd ℝ (L2ℝ (μ := μ)) (L2E (μ := μ))).comp
    (Submodule.subtypeL (h1 (μ := μ) (E := E)))

end

end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov
end

section
-- module Solutions.OAIQ092_CC.BiholderTransport_LocalFlow_ImplicitODE
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace WeakMTWTransport

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

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def rescaledIntegralCurve (f : C(E,E)) (t : ℝ) (x : E) (u : C(UnitTime,E)) (s : ℝ) : E :=
  x + t • ∫ r in (0:ℝ)..s, extendUnitPath (f.comp u) r

omit [CompleteSpace E] in
@[simp] lemma rescaledIntegralCurve_zero (f : C(E,E)) (t : ℝ) (x : E) (u : C(UnitTime,E)) :
    rescaledIntegralCurve f t x u 0 = x := by simp [rescaledIntegralCurve]

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_FormDomain_HardyMollifier
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb
open ContinuousLinearMap
open scoped Convolution

lemma hardyMollifier_tendsto {n : ℕ} :
    Filter.Tendsto (fun k => (hardyMollifier (n := n) k).rOut) Filter.atTop (nhds 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
  simpa only [hardyMollifier, mul_one_div, mul_zero] using h

lemma weak_compact_hardy {n : ℕ} (i : Fin n) (R : HardyCoordinates n i)
    (u : Configuration n → ℝ) (g : Fin 3 → Configuration n → ℝ)
    (hu : MemLp u 2) (hg : ∀ b, MemLp (g b) 2)
    (huC : HasCompactSupport u)
    (hw : ∀ b (φ : Configuration n → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, u x * fderiv ℝ φ x (EuclideanSpace.single (i,b) 1)) =
        -(∫ x, g b x * φ x)) :
    Integrable (fun x => (blockRadiusSq i R x)⁻¹ * (u x)^2) ∧
    (∫ x, (blockRadiusSq i R x)⁻¹ * (u x)^2) ≤
      4 * ∑ b : Fin 3, ∫ x, (g b x)^2 := by
  let κ : ℕ → Configuration n → ℝ := fun k => (hardyMollifier k).normed volume
  have hκ : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (κ k) := fun k =>
    (hardyMollifier k).contDiff_normed
  have hκC : ∀ k, HasCompactSupport (κ k) := fun k =>
    (hardyMollifier k).hasCompactSupport_normed
  have hκn : ∀ k x, 0 ≤ κ k x := fun k x => (hardyMollifier k).nonneg_normed x
  have hκI : ∀ k, (∫ x, κ k x) = 1 := fun k => (hardyMollifier k).integral_normed
  have hul : LocallyIntegrable u := hu.locallyIntegrable (by norm_num)
  have hus : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (κ k ⋆ u) := fun k =>
    (hκC k).contDiff_convolution_left (lsmul ℝ ℝ) (hκ k) hul
  have huc : ∀ k, HasCompactSupport (κ k ⋆ u) := fun k =>
    (hκC k).convolution (lsmul ℝ ℝ) huC
  have hh := fun k => smooth_compact_hardy i R (κ k ⋆ u) (hus k) (huc k)
  have ht : ∀ᵐ x ∂volume,
      Filter.Tendsto (fun k => (κ k ⋆ u) x) Filter.atTop (nhds (u x)) := by
    apply ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
      (φ := fun k => hardyMollifier k) (K := 2) hardyMollifier_tendsto _ hul
    apply Filter.Eventually.of_forall
    intro k
    simp only [hardyMollifier]
    simp only [mul_one_div, le_refl]
  apply ae_nonneg_fatou_integrable volume _
    (fun k x => (blockRadiusSq i R x)⁻¹ * ((κ k ⋆ u) x)^2) _
    (fun k => (hh k).1)
    (fun k x => mul_nonneg (inv_nonneg.mpr (blockRadiusSq_nonneg i R x)) (sq_nonneg _))
    (fun x => mul_nonneg (inv_nonneg.mpr (blockRadiusSq_nonneg i R x)) (sq_nonneg _))
  · filter_upwards [ht] with x hx
    exact (hx.pow 2).const_mul _
  · intro k
    apply (hh k).2.trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Finset.sum_le_sum
    intro b _
    have heq : ∀ x, fderiv ℝ (κ k ⋆ u) x (EuclideanSpace.single (i,b) 1) =
        (κ k ⋆ g b) x := by
      intro x
      exact weak_convolution_partial u (g b) (κ k) _ hul (hκ k) (hκC k) (hw b) x
    simp_rw [heq]
    exact (convolution_sq_integral_le (κ k) (g b) (hκ k).continuous (hκC k)
      (hκn k) (hκI k) ((hg b).locallyIntegrable (by norm_num)) (hg b).integrable_sq).2

lemma weak_hardy {n : ℕ} (i : Fin n) (R : HardyCoordinates n i)
    (u : Configuration n → ℝ) (g : Fin 3 → Configuration n → ℝ)
    (hu : MemLp u 2) (hg : ∀ b, MemLp (g b) 2)
    (hw : ∀ b (φ : Configuration n → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, u x * fderiv ℝ φ x (EuclideanSpace.single (i,b) 1)) =
        -(∫ x, g b x * φ x)) :
    Integrable (fun x => (blockRadiusSq i R x)⁻¹ * (u x)^2) ∧
    (∫ x, (blockRadiusSq i R x)⁻¹ * (u x)^2) ≤
      4 * ∑ b : Fin 3, ∫ x, (g b x)^2 := by
  obtain ⟨χ, D, hχ, hχC, hχB, hχD, hχt, hχdt⟩ := exists_hardyCutoffs n
  let G : ℕ → Fin 3 → Configuration n → ℝ := fun k b x =>
    χ k x * g b x + fderiv ℝ (χ k) x (EuclideanSpace.single (i,b) 1) * u x
  have hdf : ∀ k b, Continuous (fun x => fderiv ℝ (χ k) x
      (EuclideanSpace.single (i,b) 1)) := fun k b =>
    ((hχ k).continuous_fderiv (by simp)).clm_apply continuous_const
  have hG : ∀ k b, MemLp (G k b) 2 := fun k b =>
    (realMemLp_bounded_mul (g b) (χ k) (hg b) (hχ k).continuous (hχB k)).add
      (realMemLp_bounded_mul u _ hu (hdf k b) (hχD k (i,b)))
  have hU : ∀ k, MemLp (fun x => χ k x * u x) 2 := fun k =>
    realMemLp_bounded_mul u (χ k) hu (hχ k).continuous (hχB k)
  have hUC : ∀ k, HasCompactSupport (fun x => χ k x * u x) := fun k =>
    (hχC k).mul_right
  have hW := fun k => weak_compact_hardy i R (fun x => χ k x * u x) (G k)
    (hU k) (hG k) (hUC k) (fun b φ hφ hφC =>
      weak_partial_bounded_mul u (g b) (χ k) _ hu (hg b) (hχ k) (hχB k)
        (hχD k (i,b)) (hw b) φ hφ hφC)
  have hGt : ∀ b x, Filter.Tendsto (fun k => G k b x) Filter.atTop (nhds (g b x)) := by
    intro b x
    have h := ((hχt x).mul_const (g b x)).add ((hχdt (i,b) x).mul_const (u x))
    simpa only [G, one_mul, zero_mul, add_zero] using h
  have hDnonneg : 0 ≤ D := (abs_nonneg _).trans (hχD 0 (i,0) 0)
  have hbound : ∀ k b x, |(G k b x)^2| ≤ 2 * (g b x)^2 + 2 * D^2 * (u x)^2 := by
    intro k b x
    rw [abs_of_nonneg (sq_nonneg _)]
    have hX : (χ k x)^2 ≤ 1 := by
      nlinarith [(sq_le_sq₀ (abs_nonneg (χ k x)) zero_le_one).mpr (hχB k x), sq_abs (χ k x)]
    have hY : (fderiv ℝ (χ k) x (EuclideanSpace.single (i,b) 1))^2 ≤ D^2 := by
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg _) hDnonneg).mpr (hχD k (i,b) x)
    have hx := mul_le_mul_of_nonneg_right hX (sq_nonneg (g b x))
    have hy := mul_le_mul_of_nonneg_right hY (sq_nonneg (u x))
    dsimp only [G]
    nlinarith [sq_nonneg (χ k x * g b x -
      fderiv ℝ (χ k) x (EuclideanSpace.single (i,b) 1) * u x)]
  have hIt : ∀ b, Filter.Tendsto (fun k => ∫ x, (G k b x)^2) Filter.atTop
      (nhds (∫ x, (g b x)^2)) := by
    intro b
    apply tendsto_integral_of_dominated_convergence
      (fun x => 2 * (g b x)^2 + 2 * D^2 * (u x)^2)
    · intro k
      exact ((hG k b).aestronglyMeasurable.pow 2)
    · exact ((hg b).integrable_sq.const_mul 2).add (hu.integrable_sq.const_mul (2 * D^2))
    · intro k
      exact Filter.Eventually.of_forall (fun x => hbound k b x)
    · exact Filter.Eventually.of_forall (fun x => (hGt b x).pow 2)
  apply ae_nonneg_fatou_integrable_of_bound_tendsto volume _
    (fun k x => (blockRadiusSq i R x)⁻¹ * (χ k x * u x)^2) _
    (fun k => 4 * ∑ b : Fin 3, ∫ x, (G k b x)^2)
    (fun k => (hW k).1)
    (fun k x => mul_nonneg (inv_nonneg.mpr (blockRadiusSq_nonneg i R x)) (sq_nonneg _))
    (fun x => mul_nonneg (inv_nonneg.mpr (blockRadiusSq_nonneg i R x)) (sq_nonneg _))
  · apply Filter.Eventually.of_forall
    intro x
    have ht := (((hχt x).mul_const (u x)).pow 2).const_mul ((blockRadiusSq i R x)⁻¹)
    simpa only [one_mul] using ht
  · exact fun k => (hW k).2
  · exact (tendsto_finsetSum _ (fun b _ => hIt b)).const_mul 4

lemma complex_weak_hardy {n : ℕ} (i : Fin n) (R : HardyCoordinates n i)
    (u : Configuration n → ℂ) (g : Fin 3 → Configuration n → ℂ)
    (hu : MemLp u 2) (hg : ∀ b, MemLp (g b) 2)
    (hw : ∀ b (φ : Configuration n → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, u x * (fderiv ℝ φ x (EuclideanSpace.single (i,b) 1) : ℂ)) =
        -(∫ x, g b x * (φ x : ℂ))) :
    Integrable (fun x => (blockRadiusSq i R x)⁻¹ * ‖u x‖^2) ∧
    (∫ x, (blockRadiusSq i R x)⁻¹ * ‖u x‖^2) ≤
      4 * ∑ b : Fin 3, ∫ x, ‖g b x‖^2 := by
  have huR := Complex.reCLM.comp_memLp' hu
  have huI := Complex.imCLM.comp_memLp' hu
  have hgR := fun b => Complex.reCLM.comp_memLp' (hg b)
  have hgI := fun b => Complex.imCLM.comp_memLp' (hg b)
  have hr := weak_hardy i R (fun x => (u x).re) (fun b x => (g b x).re) huR hgR
    (fun b φ hφ hφC => weak_complex_component u (g b) hu (hg b) _ (hw b)
      Complex.reCLM φ hφ hφC)
  have hi := weak_hardy i R (fun x => (u x).im) (fun b x => (g b x).im) huI hgI
    (fun b φ hφ hφC => weak_complex_component u (g b) hu (hg b) _ (hw b)
      Complex.imCLM φ hφ hφC)
  have hsplit : ∀ x, (blockRadiusSq i R x)⁻¹ * ‖u x‖^2 =
      (blockRadiusSq i R x)⁻¹ * (u x).re^2 + (blockRadiusSq i R x)⁻¹ * (u x).im^2 :=
    fun x => by rw [complex_norm_sq_components, mul_add]
  constructor
  · have hsum : Integrable (fun x => (blockRadiusSq i R x)⁻¹ * (u x).re^2 +
        (blockRadiusSq i R x)⁻¹ * (u x).im^2) := hr.1.add hi.1
    exact hsum.congr (Filter.Eventually.of_forall (fun x => (hsplit x).symm))
  · simp_rw [hsplit]
    rw [integral_add hr.1 hi.1]
    have hb : ∀ b, (∫ x, ‖g b x‖^2) =
        (∫ x, (g b x).re^2) + (∫ x, (g b x).im^2) := by
      intro b
      simp_rw [complex_norm_sq_components]
      exact integral_add (hgR b).integrable_sq (hgI b).integrable_sq
    simp_rw [hb]
    rw [Finset.sum_add_distrib, mul_add]
    exact add_le_add hr.2 hi.2

lemma H1Vector.hardy {n : ℕ} (ψ : H1Vector n) (s : Spins n)
    (i : Fin n) (R : HardyCoordinates n i) :
    Integrable (fun x => (blockRadiusSq i R x)⁻¹ * ‖ψ.value s x‖^2) ∧
    (∫ x, (blockRadiusSq i R x)⁻¹ * ‖ψ.value s x‖^2) ≤
      4 * ∑ b : Fin 3, ∫ x, ‖ψ.gradient s (i,b) x‖^2 :=
  complex_weak_hardy i R (ψ.value s) (fun b => ψ.gradient s (i,b))
    (ψ.value_L2 s) (fun b => ψ.partial_L2 s (i,b)) (fun b => ψ.weak_partial s (i,b))

end Coulomb
end
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_SmoothCutoffApproximation
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact cutoffs of actual smooth weak-H1 vectors. This is the cutoff
step needed after the published smooth-density theorem. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace ContinuumCoulomb

def smoothCutoffState {n : ℕ} (u : Coulomb.H1Vector n)
    (hu : ∀ s, ContDiff ℝ 1 (u.value s)) (χ : Configuration n → ℝ)
    (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ) : Coulomb.H1Vector n :=
  classicalH1State (fun s x => (χ x : ℂ) * u.value s x)
    (fun s => (cutoff_complex_C1 χ hχ).mul (hu s))
    (fun s => ((cutoff_complex_C1 χ hχ).mul (hu s)).continuous.memLp_of_hasCompactSupport
      ((hc.comp_left Complex.ofReal_zero).mul_right))
    (fun s a =>
      (show Continuous (fun x => fderiv ℝ (fun y => (χ y : ℂ) * u.value s y) x
        (EuclideanSpace.single a 1)) from
          (((cutoff_complex_C1 χ hχ).mul (hu s)).continuous_fderiv (by norm_num)).clm_apply
            continuous_const).memLp_of_hasCompactSupport
        (((hc.comp_left Complex.ofReal_zero).mul_right).fderiv_apply ℝ _))

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

def h1CoordinateFunction {n : ℕ} (u : Coulomb.H1Vector n) :
    H1Index n → Configuration n → ℂ
  | Sum.inl s => u.value s
  | Sum.inr (s, a) => u.gradient s a

theorem h1Coordinate_memLp {n : ℕ} (u : Coulomb.H1Vector n) (a : H1Index n) :
    MemLp (h1CoordinateFunction u a) 2 := by
  cases a with
  | inl s => exact u.value_L2 s
  | inr sa => exact u.partial_L2 sa.1 sa.2

def h1Coordinates {n : ℕ} (u : Coulomb.H1Vector n) :
    H1Index n → Lp ℂ 2 (volume : Measure (Configuration n)) :=
  fun a => (h1Coordinate_memLp u a).toLp (h1CoordinateFunction u a)

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

def graphMass {n : ℕ} (f : H1Coordinates n) : ℝ :=
  ∑ s, ‖f (Sum.inl s)‖^2

def graphKinetic {n : ℕ} (f : H1Coordinates n) : ℝ :=
  (1/2 : ℝ) * ∑ s, ∑ a, ‖f (Sum.inr (s,a))‖^2

def graphBoundedForm {n : ℕ}
    (A : Lp ℂ 2 (volume : Measure (Configuration n)) →L[ℝ]
      Lp ℂ 2 (volume : Measure (Configuration n))) (f : H1Coordinates n) : ℝ :=
  graphKinetic f + ∑ s, inner ℝ (f (Sum.inl s)) (A (f (Sum.inl s)))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_H1FiniteProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite orbital penalties pass from compact tests to the complete weak-H1
domain without asking approximants to preserve exact orthogonality. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def graphOrbitalMass {n : ℕ} {ι : Type*} [Fintype ι]
    (ψ : ι → Lp ℂ 2 (volume : Measure (Configuration n))) (f : H1Coordinates n) : ℝ :=
  ∑ s, ∑ i, ‖inner ℂ (ψ i) (f (Sum.inl s))‖^2

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_FieldAnalysis_FermionicCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb

open scoped Classical

noncomputable def orbitalCoefficient {n : ℕ} {α : Type*} (ψ : H1Vector n)
    (v : α → Space → Fin 2 → ℂ) (b : Fin n → α) : ℂ :=
  ∑ s, ∫ x, star (tensorOrbital v b s x) * ψ.value s x

end Coulomb

end
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_FieldAnalysis_ConfigurationMeasurableEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb

open scoped Classical

open scoped Classical

theorem configurationMeasurableEquiv_measurePreserving (n : ℕ) :
    MeasurePreserving (configurationMeasurableEquiv n) volume volume := by
  apply MeasurePreserving.trans
    (MeasurePreserving.trans (PiLp.volume_preserving_ofLp (Fin n × Fin 3))
      (measurePreserving_uncurry (fun (_ : Fin n) (_ : Fin 3) =>
         (volume : Measure ℝ))).symm)
  exact volume_preserving_pi (fun _ => PiLp.volume_preserving_toLp (Fin 3))

theorem tensorOrbital_memLp {n : ℕ} {α : Type*}
    (v : α → Space → Fin 2 → ℂ)
    (hv : ∀ a s, MemLp (fun x => v a x s) 2 volume)
    (b : Fin n → α) (s : Spins n) :
    MemLp (tensorOrbital v b s) 2 volume := by
  have hm : AEStronglyMeasurable (fun x : Fin n → Space => ∏ i, v (b i) (x i) (s i))
      volume := by
    apply Finset.aestronglyMeasurable_fun_prod
    intro i _
    exact (hv (b i) (s i)).aestronglyMeasurable.comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_eval (fun _ : Fin n => (volume : Measure Space)) i)
  have hi : Integrable (fun x : Fin n → Space => ∏ i, ‖v (b i) (x i) (s i)‖ ^ 2) volume :=
    Integrable.fintype_prod (fun i => (hv (b i) (s i)).norm.integrable_sq)
  have hl : MemLp (fun x : Fin n → Space => ∏ i, v (b i) (x i) (s i)) 2 volume := by
    apply (memLp_two_iff_integrable_sq_norm hm).2
    simpa only [norm_prod, ← Finset.prod_pow] using hi
  exact hl.comp_measurePreserving (configurationMeasurableEquiv_measurePreserving n)

noncomputable def tensorHilbert {n : ℕ} {α : Type*}
    (v : α → Space → Fin 2 → ℂ)
    (hv : ∀ a s, MemLp (fun x => v a x s) 2 volume)
    (b : Fin n → α) : StateHilbert n :=
  WithLp.toLp 2 (fun s => (tensorOrbital_memLp v hv b s).toLp (tensorOrbital v b s))

end Coulomb
end
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CoreOrbitalProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrating the one-particle projection estimate over the other electron
coordinates. Slices belong to the full weak-H1 domain almost everywhere. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def coreOrbitalMass {n : ℕ} {ι : Type*} [Fintype ι]
    (u : Coulomb.H1Vector (n+1))
    (φ : ι → Lp ℂ 2 (volume : Measure (Configuration 1))) : ℝ :=
  ∑ s, ∫ x, graphOrbitalMass φ (h1Coordinates (u.coreSlice s x))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_Packets_CoulombKernel
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

theorem measurable_coulombKernel : Measurable coulombKernel :=
  measurable_norm.inv

theorem coulombKernel_integrableOn_ball (r : ℝ) :
    IntegrableOn coulombKernel (Metric.ball (0 : Position) r) := by
  apply integrableOn_ball_of_norm_le_rpow
    (by simp : 1 ≤ Module.finrank ℝ Position)
    (C := 1) (α := 1) (by norm_num : (1:ℝ) < Module.finrank ℝ Position)
    _ measurable_coulombKernel.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    simp [coulombKernel, Real.rpow_neg_one])

def regularizedKernel (ε : ℝ) (x : Position) : ℝ :=
  (‖x‖^2+ε^2)^(-1/2 : ℝ)

def regularizedCharge (ε : ℝ) (x : Position) : ℝ :=
  3*ε^2*(‖x‖^2+ε^2)^(-5/2 : ℝ)

theorem bounded_density_convolution {k ρ : Position → ℝ} {A : ℝ}
    (hk : Measurable k) (hkpos : ∀ x, 0 ≤ k x)
    (hki : IntegrableOn k (Metric.ball 0 1))
    (hkfar : ∀ x, 1 ≤ ‖x‖ → k x ≤ 1)
    (hρ : Integrable ρ) (hρpos : ∀ x, 0 ≤ ρ x) (hA : ∀ x, ρ x ≤ A) (x : Position) :
    Integrable (fun y => k (x-y)*ρ y) ∧
      (∫ y, k (x-y)*ρ y) ≤ A*(∫ y in Metric.ball 0 1, k y)+(∫ y, ρ y) := by
  let kn := (Metric.ball (0 : Position) 1).indicator k
  have hi : Integrable (fun y => kn (x-y)) :=
    (integrable_comp_sub_left kn x).mpr (hki.integrable_indicator measurableSet_ball)
  have hb : Integrable (fun y => A*kn (x-y)+ρ y) := (hi.const_mul A).add hρ
  have hd : ∀ y, k (x-y)*ρ y ≤ A*kn (x-y)+ρ y := by
    intro y
    by_cases hy : x-y ∈ Metric.ball (0 : Position) 1
    · simp only [kn, Set.indicator_of_mem hy]
      nlinarith [mul_le_mul_of_nonneg_left (hA y) (hkpos (x-y)), hρpos y]
    · simp only [kn, Set.indicator_of_notMem hy, mul_zero, zero_add]
      have hh : 1 ≤ ‖x-y‖ := by simpa only [Metric.mem_ball, dist_zero_right, not_lt] using hy
      simpa using mul_le_mul_of_nonneg_right (hkfar _ hh) (hρpos y)
  have hm : AEStronglyMeasurable (fun y => k (x-y)*ρ y) volume :=
    (hk.comp (measurable_const.sub measurable_id)).aestronglyMeasurable.mul hρ.aestronglyMeasurable
  have hp : Integrable (fun y => k (x-y)*ρ y) :=
    hb.mono' hm (Filter.Eventually.of_forall (fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hkpos _) (hρpos _))]
      exact hd y))
  refine ⟨hp, (integral_mono hp hb hd).trans_eq ?_⟩
  rw [integral_add (hi.const_mul A) hρ, integral_const_mul, integral_sub_left_eq_self]
  rw [integral_indicator measurableSet_ball]

end NeutralAtom
end
end
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

theorem slabDomain_isClosed (H S : ℝ) : IsClosed (slabDomain H S) := by
  have h0 : IsClosed {x : Position | |x 0| ≤ H} :=
    isClosed_le (by fun_prop) continuous_const
  have h1 : IsClosed {x : Position | |x 1| ≤ H} :=
    isClosed_le (by fun_prop) continuous_const
  have h2 : IsClosed {x : Position | |x 2| ≤ S} :=
    isClosed_le (by fun_prop) continuous_const
  exact h0.inter (h1.inter h2)

theorem slabDomain_isCompact {H S : ℝ} (hH : 0 ≤ H) (hS : 0 ≤ S) :
    IsCompact (slabDomain H S) := by
  apply (isCompact_closedBall (0 : Position) (3 * (H + S + 1))).of_isClosed_subset
    (slabDomain_isClosed H S)
  intro x hx
  have hcoord (a : Fin 3) : |x a| ≤ H + S := by
    fin_cases a
    · exact hx.1.trans (by linarith)
    · exact hx.2.1.trans (by linarith)
    · exact hx.2.2.trans (by linarith)
  have hsq : ‖x‖ ^ 2 ≤ 3 * (H + S) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    have h := Finset.sum_le_sum (s := Finset.univ) fun a _ =>
      (sq_le_sq₀ (abs_nonneg (x a)) (by linarith : 0 ≤ H + S)).mpr (hcoord a)
    simpa only [sq_abs, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_ofNat] using h
  rw [Metric.mem_closedBall, dist_zero_right]
  nlinarith [norm_nonneg x, sq_nonneg (H + S)]

theorem slabDensity_integrable {H S : ℝ} (hH : 0 ≤ H) (hS : 0 ≤ S) (rho : ℝ) :
    Integrable (slabDensity rho H S) :=
  (integrable_indicator_iff (slabDomain_isClosed H S).measurableSet).mpr
    (integrableOn_const (slabDomain_isCompact hH hS).measure_ne_top)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_FieldAnalysis_SlotTensor
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
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

lemma slotTensor_factor {A : Type*} {n : ℕ} (v d : Fin n → A → ℂ)
    (p : Equiv.Perm (Fin n)) (i : Fin n) (x : Fin n → A) :
    slotTensor v d p i x = d (p i) (x i) * ∏ j ∈ Finset.univ.erase i, v (p j) (x j) := by
  unfold slotTensor
  rw [← Finset.mul_prod_erase Finset.univ
    (fun j => if j = i then d (p j) (x j) else v (p j) (x j)) (Finset.mem_univ i)]
  simp only [ite_true, if_true]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  exact ite_eq_right (Finset.mem_erase.mp hj).1

lemma slotTensor_memLp {A : Type*} [MeasurableSpace A] {μ : Measure A}
    [SigmaFinite μ] {n : ℕ} (v d : Fin n → A → ℂ)
    (hv : ∀ a, MemLp (v a) 2 μ) (hd : ∀ a, MemLp (d a) 2 μ)
    (p : Equiv.Perm (Fin n)) (i : Fin n) :
    MemLp (slotTensor v d p i) 2 (Measure.pi fun _ : Fin n => μ) := by
  have H (j : Fin n) : MemLp (fun a => if j = i then d (p j) a else v (p j) a) 2 μ := by
    by_cases h : j = i
    · simpa only [ite_eq_left h] using hd (p j)
    · simpa only [ite_eq_right h] using hv (p j)
  exact scalarTensor_memLp (fun j a => if j = i then d (p j) a else v (p j) a) H id

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarHeatDifferential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pointwise differential identities for the actual two-dimensional Gaussian
kernel. Its time derivative is its coordinate Laplacian. -/

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace BigOperators
namespace ContinuumCoulomb

def planarHeatTimeDerivative (t : ℝ) (r : PlanarPosition) : ℝ :=
  (‖r‖ ^ 2 / (4 * t ^ 2) - 1 / t) * planarHeatKernel t r

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarNormalized
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Analytic identities for the actual normalized planar mode. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem normalizedPlanarMode_eq_const_mul : normalizedPlanarMode =
    fun r => (Real.sqrt (∫ s, planarResolventMode s ^ 2))⁻¹ * planarResolventMode r := by
  funext r
  simp only [normalizedPlanarMode, div_eq_mul_inv, mul_comm]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_VerticalMode
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual normalized Gaussian in the transverse direction. -/

noncomputable section
open MeasureTheory
open scoped ContDiff
namespace ContinuumCoulomb

theorem verticalMode_positive {freq : ℝ} (hfreq : 0 < freq) (z : ℝ) :
    0 < verticalMode freq z :=
  div_pos (Real.exp_pos _) (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (div_pos Real.pi_pos hfreq)))

theorem verticalMode_smooth (freq : ℝ) : ContDiff ℝ ∞ (verticalMode freq) := by
  unfold verticalMode
  fun_prop

theorem verticalMode_hasDerivAt (freq z : ℝ) :
    HasDerivAt (verticalMode freq) (-freq * z * verticalMode freq z) z := by
  have h := ((((hasDerivAt_id z).pow 2).const_mul (-freq)).div_const 2).exp
  refine (h.div_const (Real.sqrt (Real.sqrt (Real.pi / freq)))).congr_deriv ?_
  · simp only [verticalMode, id_eq, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub,
      pow_one, mul_one]
    ring

theorem verticalMode_deriv (freq z : ℝ) :
    deriv (verticalMode freq) z = -freq * z * verticalMode freq z :=
  (verticalMode_hasDerivAt freq z).deriv

theorem verticalMode_square {freq : ℝ} (_hfreq : 0 < freq) (z : ℝ) :
    verticalMode freq z ^ 2 = Real.exp (-freq * z ^ 2) / Real.sqrt (Real.pi / freq) := by
  unfold verticalMode
  rw [div_pow, Real.sq_sqrt (Real.sqrt_nonneg _), ← Real.exp_nat_mul]
  congr 2
  ring

theorem verticalMode_moment_integrable {freq : ℝ} (hfreq : 0 < freq) (n : ℕ) :
    Integrable (fun z : ℝ => z ^ n * verticalMode freq z ^ 2) := by
  have h : Integrable (fun z : ℝ => z ^ n * Real.exp (-freq * z ^ 2)) := by
    simpa only [Real.rpow_natCast] using
      (integrable_rpow_mul_exp_neg_mul_sq hfreq (s := (n : ℝ))
        (lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (Nat.cast_nonneg n)))
  simp_rw [verticalMode_square hfreq, ← mul_div_assoc]
  exact h.div_const _

theorem verticalMode_square_integrable {freq : ℝ} (hfreq : 0 < freq) :
    Integrable (fun z : ℝ => verticalMode freq z ^ 2) := by
  simpa only [pow_zero, one_mul] using verticalMode_moment_integrable hfreq 0

theorem verticalMode_deriv_square_integrable {freq : ℝ} (hfreq : 0 < freq) :
    Integrable (fun z : ℝ => deriv (verticalMode freq) z ^ 2) := by
  have h := (verticalMode_moment_integrable hfreq 2).const_mul (freq ^ 2)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  rw [verticalMode_deriv]
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_SplitCoordinates
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Volume-preserving planar/transverse coordinates for the actual
three-dimensional Coulomb space. The intermediate product has its Euclidean
L² norm; the final ordinary product carries the same product volume. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem positionSplitCoordinates_measurePreserving :
    MeasurePreserving positionSplitCoordinates := by
  change MeasurePreserving (fun x => WithLp.ofLp (positionSplitIsometry x))
  exact (WithLp.volume_preserving_ofLp PlanarPosition ℝ).comp
    positionSplitIsometry.measurePreserving

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_Variational_CorrectionDensity
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

theorem coulombKernel_le_one {x : Position} (hx : 1 ≤ ‖x‖) : coulombKernel x ≤ 1 := by
  simpa only [coulombKernel, inv_one] using inv_anti₀ (by norm_num : (0:ℝ)<1) hx

theorem coulombKernel_sq_integrableOn_ball (r : ℝ) :
    IntegrableOn (fun x => (coulombKernel x)^2) (Metric.ball (0 : Position) r) := by
  apply integrableOn_ball_of_norm_le_rpow
    (by simp : 1 ≤ Module.finrank ℝ Position)
    (C := 1) (α := 2) (by norm_num : (2:ℝ) < Module.finrank ℝ Position)
    _ (measurable_coulombKernel.pow_const 2).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    simp [coulombKernel, Real.rpow_neg (norm_nonneg x)])

theorem coulombKernel_sub_le {x y : Position} (hx : x ≠ 0) (hy : y ≠ 0) :
    |coulombKernel x-coulombKernel y| ≤
      ‖x-y‖/2*((coulombKernel x)^2+(coulombKernel y)^2) := by
  have hxp : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hyp : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have he : |coulombKernel x-coulombKernel y| =
      |‖y‖-‖x‖| *(‖x‖⁻¹*‖y‖⁻¹) := by
    rw [coulombKernel, coulombKernel, inv_sub_inv hxp.ne' hyp.ne',
      abs_div, abs_mul, abs_of_pos hxp, abs_of_pos hyp]
    simp only [div_eq_mul_inv, mul_inv_rev, mul_comm ‖x‖⁻¹ ‖y‖⁻¹]
  rw [he]
  calc
    |‖y‖-‖x‖| *(‖x‖⁻¹*‖y‖⁻¹) ≤ ‖x-y‖*(‖x‖⁻¹*‖y‖⁻¹) := by
      apply mul_le_mul_of_nonneg_right
      · simpa only [norm_sub_rev] using abs_norm_sub_norm_le y x
      · positivity
    _ ≤ _ := by
      have hb : 2*(‖x‖⁻¹*‖y‖⁻¹) ≤ (‖x‖⁻¹)^2+(‖y‖⁻¹)^2 := by
        nlinarith [sq_nonneg (‖x‖⁻¹-‖y‖⁻¹)]
      have hm := mul_le_mul_of_nonneg_left hb (norm_nonneg (x-y))
      dsimp [coulombKernel]
      nlinarith

end NeutralAtom
end
end
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

theorem localizedDensity_nonnegative (freq : ℝ) (u : PlanarPosition) (x : Position) :
    0 ≤ localizedDensity freq u x := sq_nonneg _

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarOverlap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual normalized planar orbitals have overlap bounded at rate 0.9,
uniformly over every pair of centers. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def normalizedPlanarExponentialConstant (a : ℝ) : ℝ :=
  planarExponentialConstant a / Real.sqrt (∫ r, planarResolventMode r ^ 2)

def planarModeOverlap (u v : PlanarPosition) : ℝ :=
  ∫ r, normalizedPlanarMode (r - u) * normalizedPlanarMode (r - v)

def planarOverlapConstant : ℝ := normalizedPlanarExponentialConstant (19 / 20) ^ 2 *
  (∫ r : PlanarPosition, Real.exp (-(1 / 20 : ℝ) * ‖r‖))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedTransition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual transition densities of localized three-dimensional modes
have normalized mass bounds and exponentially small off-site L1 mass. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def localizedTransition (freq : ℝ) (u v : PlanarPosition) (x : Position) : ℝ :=
  continuumLocalizedMode freq u x * continuumLocalizedMode freq v x

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarLowerTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A matching lower exponential tail for the actual planar mode. Only the
positive forcing mass and the heat-time interval `[|r|/2,|r|/2+1]` are used. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def planarLowerTailConstant : ℝ :=
  Real.exp (-2) * (∫ a, planarForcing a) / (2 * Real.pi)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarRadial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rotation/reflection invariance of the actual manufactured planar data.
The hopping between arbitrary translated centers depends only on distance. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def planarHoppingAt (u : PlanarPosition) : ℝ :=
  (∫ r, planarForcing r * planarResolventMode (r - u)) /
    (2 * ∫ r, planarResolventMode r ^ 2)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedCoulombRadial
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual direct Coulomb interaction depends only on planar separation. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def liftPlanarIsometry (L : PlanarPosition ≃ₗᵢ[ℝ] PlanarPosition) : Position ≃ₗᵢ[ℝ] Position :=
  positionSplitIsometry.trans
    ((LinearIsometryEquiv.withLpProdCongr 2 L (LinearIsometryEquiv.refl ℝ ℝ)).trans
      positionSplitIsometry.symm)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedLeakage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exponential off-site density leakage for the actual localized modes. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def localizedTailConstant (freq : ℝ) : ℝ :=
  (4 * localizedAmplitudeBound freq) ^ 2 * Real.exp 1

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

def localLeakageBound (freq D : ℝ) : ℝ :=
  (localizedTailConstant freq * Real.exp (2 - D)) * (∫ x : Position, |localDualBump x|)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedGramSpacing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed logarithmic spacing controls the total leakage for every
polynomial number of sites. The exponent is chosen once for the reduction. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def localLeakageConstant (freq : ℝ) : ℝ :=
  localizedTailConstant freq * Real.exp 2 * (∫ x : Position, |localDualBump x|)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarHoppingBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Matching exponential brackets for the actual contact hopping integral. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def planarHoppingUpperConstant : ℝ :=
  Real.exp 3 * (∫ r, planarForcing r) / (2 * ∫ r, planarResolventMode r ^ 2)

def planarHoppingLowerConstant : ℝ :=
  planarLowerTailConstant * Real.exp (-1) * (∫ r, planarForcing r) /
    (2 * ∫ r, planarResolventMode r ^ 2)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A smooth square partition for finitely many disjoint planar cutoffs.
The exterior function is smooth even on the regions where all site cutoffs
vanish; no square root at a zero is used. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def planarTrigPartition {ι : Type*} [Fintype ι]
    (χ : ι → PlanarPosition → ℝ) : Option ι → PlanarPosition → ℝ
  | none => fun x => 1 + ∑ i, (Real.cos (χ i x) - 1)
  | some i => fun x => Real.sin (χ i x)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_VerticalCappedForm
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual capped transverse oscillator and its two-part IMS formula.
The cutoff is one on the inner half-slab and zero beyond the slab. -/

noncomputable section
open MeasureTheory
open scoped ContDiff
namespace ContinuumCoulomb

def verticalCutoffAngle (S z : ℝ) : ℝ :=
  (Real.pi/2) * verticalCutoffBump ((2/S)*z)

def verticalInnerCutoff (S z : ℝ) : ℝ := Real.sin (verticalCutoffAngle S z)
def verticalOuterCutoff (S z : ℝ) : ℝ := Real.cos (verticalCutoffAngle S z)

theorem verticalCutoffBump_deriv_bounded :
    ∃ C : ℝ, ∀ z, ‖deriv (verticalCutoffBump : ℝ → ℝ) z‖ ≤ C := by
  have hs : ContDiff ℝ 2 (verticalCutoffBump : ℝ → ℝ) := verticalCutoffBump.contDiff
  exact (hs.continuous_deriv (by norm_num)).bounded_above_of_compact_support
    verticalCutoffBump.hasCompactSupport.deriv

def verticalCutoffDerivativeConstant : ℝ := Classical.choose verticalCutoffBump_deriv_bounded

def verticalCutoffDerivativeBound (S : ℝ) : ℝ :=
  (Real.pi/2 * (2/S)) * verticalCutoffDerivativeConstant

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ManufacturedWellField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual compact three-dimensional well field in the unit-charge
construction. Its coefficients are Coulomb counterterms. The cutoff only weakens the attractive uncorrected wells. -/

noncomputable section
open scoped BigOperators ContDiff
namespace ContinuumCoulomb

def slabWellCutoff (S z : ℝ) : ℝ := verticalCutoffBump ((2/S)*z)

theorem slabWellCutoff_smooth (S : ℝ) : ContDiff ℝ ∞ (slabWellCutoff S) :=
  verticalCutoffBump.contDiff.comp (contDiff_const.mul contDiff_id)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarCutoffTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual site cutoff changes its normalized ground mode by an
exponentially small L2 vector. This controls the rank-one terms in IMS. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def planarSiteTailConstant : ℝ :=
  4 * normalizedPlanarExponentialConstant (19/20) ^ 2 *
    ∫ r : PlanarPosition, Real.exp (-(19/20 : ℝ) * ‖r‖)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedOrbitalGram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual localized L2 orbitals form a well-conditioned independent
family whenever the exponentially small pair overlaps have a small row sum.
In particular their finite span has an actual orthonormal basis. -/

noncomputable section
open MeasureTheory InnerProductSpace
open scoped BigOperators
namespace ContinuumCoulomb

def localizedOverlapBound (D : ℝ) : ℝ := planarOverlapConstant * Real.exp (-(9 / 10 : ℝ) * D)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_VerticalSliceProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual transverse Gaussian defines a contraction on the full L2
product space. No compact-support or smoothness hypothesis is imposed here. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def verticalCoefficient (freq : ℝ) (f : SplitPosition → ℝ) (r : PlanarPosition) : ℝ :=
  ∫ z, f (r,z)*verticalMode freq z

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_VerticalResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact L2 mass splitting into the Gaussian transverse mode and its
orthogonal residual, for arbitrary product-space wavefunctions. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def verticalLift (freq : ℝ) (a : PlanarPosition → ℝ) (p : SplitPosition) : ℝ :=
  a p.1*verticalMode freq p.2

def verticalResidual (freq : ℝ) (f : SplitPosition → ℝ) (p : SplitPosition) : ℝ :=
  f p-verticalLift freq (verticalCoefficient freq f) p

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarSliceProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Planar orbital coefficients on product L2, with exact contraction
and subtraction identities. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def planarCoefficient (u : PlanarPosition) (f : SplitPosition → ℝ) (z : ℝ) : ℝ :=
  ∫ r, f (r,z)*normalizedPlanarMode (r-u)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_VerticalCutoffTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gaussian control of the inner-slab projection error for the actual
transverse cutoff. The loss decays exponentially in the square of the slab
width, with the oscillator frequency fixed by the construction. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def verticalCutoffError (freq S z : ℝ) : ℝ :=
  (verticalInnerCutoff S z-1)*verticalMode freq z

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_SplitSpectralBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Combining the actual planar and transverse form estimates. The
projection budget removes the planar penalty from transverse excitations. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def splitVerticalForm (freq S : ℝ) (f : SplitPosition → ℝ) : ℝ :=
  ∫ r : PlanarPosition, verticalCappedForm freq S (fun z => f (r,z))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_SplitTestFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Classical test functions in split coordinates: compact slices and
their exact directional derivatives. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def splitVerticalPartial (f : SplitPosition → ℝ) (p : SplitPosition) : ℝ :=
  fderiv ℝ f p (0,1)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_SplitPullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact kinetic-energy pullback between physical Euclidean space and
planar/transverse product coordinates. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def splitPullback (f : Position → ℝ) (p : SplitPosition) : ℝ :=
  f (positionSplitCoordinates.symm p)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_ElectronSlotBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The one-electron finite-rank lower bound acts on every electron slot.
All coordinate changes preserve the full spinful weak-H1 domain. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def electronSlotOrbitalMass {n : ℕ} {ι : Type*} [Fintype ι]
    (u : Coulomb.H1Vector (n+1))
    (φ : ι → Lp ℂ 2 (volume : Measure (Configuration 1))) (i : Fin (n+1)) : ℝ :=
  coreOrbitalMass (u.permutation (Equiv.swap (Fin.last n) i)) φ

def totalOrbitalMass {n : ℕ} {ι : Type*} [Fintype ι]
    (u : Coulomb.H1Vector (n+1))
    (φ : ι → Lp ℂ 2 (volume : Measure (Configuration 1))) : ℝ :=
  ∑ i, electronSlotOrbitalMass u φ i

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

def globalBellMatrix (r : ℕ) : Matrix (MediatorBasis r) (MediatorBasis r) ℂ :=
  fun a b => ∏ e, bellMatrix (a e) (b e)

def mediatorExcitationNumber (r : ℕ) (a : MediatorBasis r) : ℕ :=
  (Finset.univ.filter (fun e => a e ≠ 0)).card

def mediatorPenaltyWeight (r : ℕ) (Delta : ℝ) (a : MediatorBasis r) : ℝ :=
  4 * Delta * mediatorExcitationNumber r a

end ContinuumCoulomb

end

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

/-- Complete finite Hamiltonian, with no magnetic or one-site terms. -/
def sourceHamiltonian (d : SquareLatticeHeisenberg)
    (u : SourceSpinVector d.vertices) : SourceSpinVector d.vertices :=
  fun s => ∑ e, (d.coefficient e : ℂ) *
    sourceHeisenbergAction (d.left e) (d.right e) u s

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

def SquareLatticeHeisenberg.withCoefficients (d : SquareLatticeHeisenberg)
    (coefficient : Fin d.edges → ℚ) : SquareLatticeHeisenberg :=
  { d with coefficient := coefficient }

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_FiniteAtomicOutputs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed YES and NO instances need only finiteness of the atomic energy.
No hydrogen spectral formula is needed for this branch of the reduction. -/

noncomputable section
namespace ContinuumCoulomb

/-- A fixed one-electron unit nucleus with adjacent integer thresholds. -/
def atomicThresholdOutput (z : ℤ) : UnitCoulomb where
  nuclei := [⟨BinaryRational.ofRat 0,BinaryRational.ofRat 0,BinaryRational.ofRat 0⟩]
  electrons := 1
  lower := BinaryRational.ofRat z
  upper := BinaryRational.ofRat (z+1)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ClassicalTensor
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.Coulomb.complexWindow_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! C1 tensor products and their actual weak-H1 partials. Fubini supplies
L2 membership for decaying orbitals; compact support is unnecessary. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem tensorOrbital_C1_fderiv {n : ℕ} {α : Type*} (v : α → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 1 (fun x => v a x s)) (p : Fin n → α)
    (s : SpinConfiguration n) (x : Configuration n) (i : Fin n) (b : Fin 3) :
    fderiv ℝ (Coulomb.tensorOrbital v p s) x (EuclideanSpace.single (i,b) 1) =
      (fderiv ℝ (fun y => v (p i) y (s i)) (Coulomb.position x i) (EuclideanSpace.single b 1)) *
        ∏ j ∈ Finset.univ.erase i, v (p j) (Coulomb.position x j) (s j) := by
  have hd (j : Fin n) : DifferentiableAt ℝ (fun y : Configuration n =>
      v (p j) (Coulomb.position y j) (s j)) x :=
    by
      change DifferentiableAt ℝ ((fun y => v (p j) y (s j)) ∘ Coulomb.positionCLM j) x
      exact ((hv (p j) (s j)).differentiable (by norm_num) (Coulomb.positionCLM j x)).comp x
        (Coulomb.positionCLM j).differentiableAt
  have he (j : Fin n) : fderiv ℝ (fun y : Configuration n => v (p j) (Coulomb.position y j) (s j)) x =
      (fderiv ℝ (fun y => v (p j) y (s j)) (Coulomb.position x j)).comp (Coulomb.positionCLM j) :=
    by
      change fderiv ℝ ((fun y => v (p j) y (s j)) ∘ Coulomb.positionCLM j) x = _
      exact (((hv (p j) (s j)).differentiable (by norm_num) (Coulomb.positionCLM j x)).hasFDerivAt.comp x
        (Coulomb.positionCLM j).hasFDerivAt).fderiv
  unfold Coulomb.tensorOrbital
  rw [fderiv_finsetProd (fun j _ => hd j), sum_apply]
  simp only [smul_apply, smul_eq_mul, he, ContinuousLinearMap.comp_apply, Coulomb.positionCLM_single]
  rw [Finset.sum_eq_single i]
  · simp only [ite_true, if_true]
    ring
  · intro j _ hji
    simp only [ite_eq_right hji, map_zero, mul_zero]
  · simp

theorem tensorOrbital_partial_memLp {n : ℕ} {α : Type*} (v : α → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 1 (fun x => v a x s))
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)
    (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x (EuclideanSpace.single b 1)) 2)
    (p : Fin n → α) (s : SpinConfiguration n) (i : Fin n) (b : Fin 3) :
    MemLp (fun x => fderiv ℝ (Coulomb.tensorOrbital v p s) x (EuclideanSpace.single (i,b) 1)) 2 := by
  let f : Fin n → Position → ℂ := fun j y => v (p j) y (s j)
  let d : Fin n → Position → ℂ := fun j x => fderiv ℝ (fun y => v (p j) y (s j)) x (EuclideanSpace.single b 1)
  have h := (Coulomb.slotTensor_memLp f d (fun j => hL2 (p j) (s j))
    (fun j => hpartial (p j) (s j) b) (Equiv.refl (Fin n)) i).comp_measurePreserving
    (Coulomb.configurationMeasurableEquiv_measurePreserving n)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  simp only [Function.comp_apply]
  rw [tensorOrbital_C1_fderiv v hv, Coulomb.slotTensor_factor]
  rfl

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_FiniteTensorState
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite products of the actual smooth orbitals lie in the full H1 domain.
Their synthesis agrees with the orthogonal L2 tensor synthesis. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

def classicalTensorState {n : ℕ} {α : Type*}
    (v : α → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 1 (fun x => v a x s))
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)
    (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x
      (EuclideanSpace.single b 1)) 2) (p : Fin n → α) : Coulomb.H1Vector n :=
  classicalH1State (Coulomb.tensorOrbital v p) (tensorOrbital_C1 v hv p)
    (Coulomb.tensorOrbital_memLp v hL2 p)
    (fun s a => tensorOrbital_partial_memLp v hv hL2 hpartial p s a.1 a.2)

def finiteTensorState {n : ℕ} {α : Type*} [Fintype α]
    (v : α → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 1 (fun x => v a x s))
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)
    (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x
      (EuclideanSpace.single b 1)) 2) (c : (Fin n → α) → ℂ) : Coulomb.H1Vector n :=
  Coulomb.H1Vector.finiteSum (fun p =>
    Coulomb.H1Vector.scale (c p) (classicalTensorState v hv hL2 hpartial p))

def finiteTensorProjection {n : ℕ} {α : Type*} [Fintype α]
    (v : α → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 1 (fun x => v a x s))
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)
    (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x
      (EuclideanSpace.single b 1)) 2) (u : Coulomb.H1Vector n) : Coulomb.H1Vector n :=
  finiteTensorState v hv hL2 hpartial (Coulomb.orbitalCoefficient u v)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_FiniteTensorProjection
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The all-orbital tensor projection and its genuine H1 remainder have
orthogonal L2 values. In particular their masses add exactly. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

def finiteTensorRemainder {n : ℕ} {α : Type*} [Fintype α]
    (v : α → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 1 (fun x => v a x s))
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)
    (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x
      (EuclideanSpace.single b 1)) 2) (u : Coulomb.H1Vector n) : Coulomb.H1Vector n :=
  u.add (Coulomb.H1Vector.scale (-1) (finiteTensorProjection v hv hL2 hpartial u))

end ContinuumCoulomb

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

def hubbardLowUnit (m : ℕ) : HubbardLowSpace m :=
  EuclideanSpace.single (fun _ => 0) 1

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_MediatorCompression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact simultaneous singlet-penalty diagonalization and inverse compression.
All tensor matrices here act on the complete mediator configuration basis. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators

/-- Tensor product over the actual four-state mediator pairs. -/
def mediatorTensor (r : ℕ) (M : Fin r → Matrix (Fin 4) (Fin 4) ℂ) :
    Matrix (MediatorBasis r) (MediatorBasis r) ℂ := fun a b => ∏ e, M e (a e) (b e)

/-- An operator acting on one actual fresh pair, with identity on all others. -/
def mediatorLocal (r : ℕ) (e : Fin r) (M : Matrix (Fin 4) (Fin 4) ℂ) :
    Matrix (MediatorBasis r) (MediatorBasis r) ℂ :=
  mediatorTensor r (fun f => if f = e then M else 1)

/-- The physical central-bond sum, with its singlet scalar shifts. -/
def physicalMediatorPenalty (r : ℕ) (Delta : ℝ) :
    Matrix (MediatorBasis r) (MediatorBasis r) ℂ :=
  (Delta : ℂ) • ∑ e, mediatorLocal r e (heisenberg + (3 : ℂ) • 1)

/-- Full inverse on the triplet complement and zero on the singlet kernel. -/
def mediatorInverseWeight (r : ℕ) (Delta : ℝ) (a : MediatorBasis r) : ℂ :=
  if a = mediatorVacuum r then 0 else ((mediatorPenaltyWeight r Delta a)⁻¹ : ℝ)

def mediatorInverseMatrix (r : ℕ) (Delta : ℝ) :
    Matrix (MediatorBasis r) (MediatorBasis r) ℂ :=
  Matrix.diagonal (mediatorInverseWeight r Delta)

end ContinuumCoulomb

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

/-- Restriction to original spins tensored with all mediator singlets. -/
def mediatorCompression (n r : ℕ) :
    Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ →ₗ[ℂ]
      Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ where
  toFun M s t := M (s, mediatorVacuum r) (t, mediatorVacuum r)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def liftedMediatorInverse (n r : ℕ) (Delta : ℝ) :
    Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ :=
  1 ⊗ₖ mediatorInverseMatrix r Delta

def elementaryMediatorSpoke (n r : ℕ) (e : Fin r) (member : Fin 2) (μ : Fin 3)
    (A : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) :
    Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ :=
  A ⊗ₖ mediatorLocal r e (bellMemberPauli member μ)

/-- The two physical spokes incident to one original edge. The left spoke
uses the first mediator member; the right can use either member. -/
def mediatorEdgeSpoke (n r : ℕ) (e : Fin r) (i j : Fin n) (member : Fin 2) :
    Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ :=
  ∑ μ : Fin 3,
    (elementaryMediatorSpoke n r e 0 μ (sourceLocalPauli n i μ) +
      elementaryMediatorSpoke n r e member μ (sourceLocalPauli n j μ))


def mediatorAxisSpoke (n r : ℕ) (e : Fin r) (i : Fin n) (member : Fin 2) :
    Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ :=
  ∑ μ : Fin 3, elementaryMediatorSpoke n r e member μ (sourceLocalPauli n i μ)

def totalMediatorSpokes (n r : ℕ) (left right : Fin r → Fin n)
    (member : Fin r → Fin 2) (amplitude : Fin r → ℝ) :
    Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ :=
  ∑ e, (amplitude e : ℂ) • mediatorEdgeSpoke n r e (left e) (right e) (member e)


def physicalMemberPauli (member : Fin 2) (μ : Fin 3) : Matrix (Fin 4) (Fin 4) ℂ :=
  if member = 0 then firstPauli μ else secondPauli μ

def fullMediatorBellMatrix (n r : ℕ) :
    Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ :=
  1 ⊗ₖ globalBellMatrix r

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

def mediatorLowIndex (n r : ℕ) (s : SourceSpinBasis n) : MediatedSpinBasis n r :=
  (s, mediatorVacuum r)

def mediatorHighIndex (n r : ℕ) (s : SourceSpinBasis n × MediatorHighBasis r) :
    MediatedSpinBasis n r := (s.1, s.2.val)

def mediatorLowInclusion (n r : ℕ) : MediatorLowSpace n →L[ℂ] MediatorFullSpace n r :=
  HubbardGlobal.coordinateInclusion (mediatorLowIndex n r)

def mediatorLowRestriction (n r : ℕ) : MediatorFullSpace n r →L[ℂ] MediatorLowSpace n :=
  HubbardGlobal.coordinateRestriction (mediatorLowIndex n r)

def mediatorHighInclusion (n r : ℕ) : MediatorHighSpace n r →L[ℂ] MediatorFullSpace n r :=
  HubbardGlobal.coordinateInclusion (mediatorHighIndex n r)

def mediatorHighRestriction (n r : ℕ) : MediatorFullSpace n r →L[ℂ] MediatorHighSpace n r :=
  HubbardGlobal.coordinateRestriction (mediatorHighIndex n r)

def actualMediatorWeight (n r : ℕ) (Delta : ℝ) (s : SourceSpinBasis n × MediatorHighBasis r) : ℝ :=
  mediatorPenaltyWeight r Delta s.2.val

def actualMediatorLowBlock (n r : ℕ)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) :
    MediatorLowSpace n →L[ℝ] MediatorLowSpace n :=
  ((mediatorLowRestriction n r).comp
    ((spinMatrixOperator (C ⊗ₖ 1)).comp (mediatorLowInclusion n r))).restrictScalars ℝ

def actualMediatorCoupling (n r : ℕ) (left right : Fin r → Fin n)
    (member : Fin r → Fin 2) (amplitude : Fin r → ℝ) :
    MediatorLowSpace n →L[ℝ] MediatorHighSpace n r :=
  ((mediatorHighRestriction n r).comp
    ((spinMatrixOperator (totalMediatorSpokes n r left right member amplitude)).comp
      (mediatorLowInclusion n r))).restrictScalars ℝ

def actualMediatorHighBlock (n r : ℕ)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ)
    (left right : Fin r → Fin n) (member : Fin r → Fin 2) (amplitude : Fin r → ℝ) :
    MediatorHighSpace n r →L[ℝ] MediatorHighSpace n r :=
  ((mediatorHighRestriction n r).comp
    ((spinMatrixOperator (C ⊗ₖ 1 + totalMediatorSpokes n r left right member amplitude)).comp
      (mediatorHighInclusion n r))).restrictScalars ℝ

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

def assembleMediator (n r : ℕ) (p : MediatorLowSpace n) (q : MediatorHighSpace n r) :
    MediatorFullSpace n r := mediatorLowInclusion n r p + mediatorHighInclusion n r q

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

def bellMediatorPenaltyMatrix (n r : ℕ) (Delta : ℝ) :
    Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ :=
  Matrix.diagonal (fun s => (mediatorPenaltyWeight r Delta s.2 : ℂ))

/-- The actual full matrix in the complete Bell-coordinate spin space. -/
def bellMediatorHamiltonian (n r : ℕ) (Delta : ℝ)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ)
    (left right : Fin r → Fin n) (member : Fin r → Fin 2) (amplitude : Fin r → ℝ) :
    Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ :=
  bellMediatorPenaltyMatrix n r Delta +
    (C ⊗ₖ 1 + totalMediatorSpokes n r left right member amplitude)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_MediatorSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual variational bottoms for the complete simultaneous-mediator spin
Hamiltonian and its effective source matrix. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker InnerProductSpace

def mediatorFullBottom (n r : ℕ)
    (H : Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ) : ℝ :=
  sInf {e | ∃ x : MediatorFullSpace n r, 0 < ‖x‖ ^ 2 ∧
    e = ⟪x, spinMatrixOperator H x⟫_ℝ / ‖x‖ ^ 2}

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_MediatorPhysical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical positive-spoke spin matrices and their full spectral comparison. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker InnerProductSpace

def physicalMediatorEdgeSpoke (n r : ℕ) (e : Fin r) (i j : Fin n) (member : Fin 2) :
    Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ :=
  ∑ μ : Fin 3,
    (sourceLocalPauli n i μ ⊗ₖ mediatorLocal r e (physicalMemberPauli 0 μ) +
      sourceLocalPauli n j μ ⊗ₖ mediatorLocal r e (physicalMemberPauli member μ))

def physicalTotalMediatorSpokes (n r : ℕ) (left right : Fin r → Fin n)
    (member : Fin r → Fin 2) (amplitude : Fin r → ℝ) :
    Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ :=
  ∑ e, (amplitude e : ℂ) • physicalMediatorEdgeSpoke n r e (left e) (right e) (member e)

/-- Central antiferromagnetic bonds with their explicit three-Delta
singlet shifts, plus the physical original-spin and spoke interactions. -/
def physicalMediatorHamiltonian (n r : ℕ) (Delta : ℝ)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ)
    (left right : Fin r → Fin n) (member : Fin r → Fin 2) (amplitude : Fin r → ℝ) :
    Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ :=
  1 ⊗ₖ physicalMediatorPenalty r Delta +
    (C ⊗ₖ 1 + physicalTotalMediatorSpokes n r left right member amplitude)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_MediatorOffsets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact scalar offsets relating the shifted mediator penalty to the
physical Hamiltonian containing only the specified Heisenberg bonds. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker InnerProductSpace

def physicalRawMediatorHamiltonian (n r : ℕ) (Delta : ℝ)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ)
    (left right : Fin r → Fin n) (member : Fin r → Fin 2) (amplitude : Fin r → ℝ) :
    Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ :=
  (1 : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) ⊗ₖ
      ((Delta : ℂ) • ∑ e, mediatorLocal r e heisenberg) +
    (C ⊗ₖ 1 + physicalTotalMediatorSpokes n r left right member amplitude)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_HeisenbergOffsets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact scalar offsets and positive homogeneity connecting the ordinary
finite-spin Hamiltonian with the Hubbard superexchange source form. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators InnerProductSpace

variable {Edge : Type*} [Fintype Edge]

def finiteHeisenbergMatrix (n : ℕ) (left right : Edge → Fin n) (J : Edge → ℝ) :
    Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ :=
  ∑ e, (J e : ℂ) • sourceHeisenbergMatrix n (left e) (right e)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedLinearOrbitals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite linear combinations of localized orbitals. Their
classical partials remain L2, and their integral Gram matrix is the
corresponding finite congruence of the actual overlap matrix. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def localizedLinearOrbital (freq : ℝ) {m : ℕ} (u : Fin m → PlanarPosition)
    (a : Fin m → ℝ) (x : Position) : ℝ :=
  ∑ j, a j * continuumLocalizedMode freq (u j) x

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_OrthonormalLocalizedModes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual spectral inverse-square-root correction applied to the
manufactured orbitals. These are C1 decaying orthonormal spatial functions;
injectively occupied spatial/spin modes give actual normalized fermions. -/

noncomputable section
open MeasureTheory Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace ContinuumCoulomb

def localizedModeGram {m : ℕ} (u : Fin m → PlanarPosition) : Matrix (Fin m) (Fin m) ℝ :=
  fun i j => planarModeOverlap (u i) (u j)

theorem localizedModeGram_isHermitian {m : ℕ} (u : Fin m → PlanarPosition) :
    (localizedModeGram u).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm]
  ext i j
  change planarModeOverlap (u j) (u i) = planarModeOverlap (u i) (u j)
  unfold planarModeOverlap
  apply integral_congr_ae
  filter_upwards [] with r
  exact mul_comm _ _

def correctedLocalizedCoefficients {m : ℕ} (u : Fin m → PlanarPosition) : Matrix (Fin m) (Fin m) ℝ :=
  GramCorrection.correction (localizedModeGram_isHermitian u)

def correctedLocalizedMode (freq : ℝ) {m : ℕ} (u : Fin m → PlanarPosition) (i : Fin m) : Position → ℝ :=
  localizedLinearOrbital freq u (correctedLocalizedCoefficients u i)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_RepulsionBound
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.Coulomb.complexWindow_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Coulomb repulsion as a form-domain to L² multiplier

Both continuum comparisons need control of the repulsion applied to a
localized many-electron vector, including its mixed block with the continuum
complement. Translated pair Hardy and finite Cauchy--Schwarz prove a bound on
the actual full repulsion, without summing over an exponentially large spin
operator matrix.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem pair_hardy_square {n : ℕ} (state : Coulomb.H1Vector n)
    (spin : Coulomb.Spins n) (i j : Fin n) (hne : i ≠ j) :
    Integrable (fun x => Coulomb.coulombKernel (Coulomb.position x i - Coulomb.position x j) ^ 2 *
      ‖state.value spin x‖ ^ 2) ∧
    (∫ x, Coulomb.coulombKernel (Coulomb.position x i - Coulomb.position x j) ^ 2 *
      ‖state.value spin x‖ ^ 2) ≤
      4 * ∑ k : Fin 3, ∫ x, ‖state.gradient spin (i, k) x‖ ^ 2 := by
  simpa only [← Coulomb.hardyCoulomb_sq, Coulomb.hardyCoulomb_pair] using
    state.hardy spin i (Coulomb.pairHardyCoordinates i j hne)

theorem repulsionPotential_measurable (n : ℕ) :
    Measurable (@repulsionPotential n) := by
  unfold repulsionPotential
  apply Finset.measurable_sum
  intro p _
  change Measurable (fun x => pairRepulsionTerm p x)
  by_cases hp : p.1 < p.2
  · have h := Coulomb.measurable_hardyCoulomb p.1
      (Coulomb.pairHardyCoordinates p.1 p.2 hp.ne)
    change Measurable (fun x =>
      Coulomb.hardyCoulomb p.1 (Coulomb.pairHardyCoordinates p.1 p.2 hp.ne) x) at h
    simpa only [pairRepulsionTerm, ite_eq_left hp, Coulomb.hardyCoulomb_pair] using h
  · simp only [pairRepulsionTerm, ite_eq_right hp]
    exact measurable_const

theorem repulsionPotential_spin_L2_bound {n : ℕ} (state : Coulomb.H1Vector n)
    (spin : Coulomb.Spins n) :
    Integrable (fun x => repulsionPotential x ^ 2 * ‖state.value spin x‖ ^ 2) ∧
    (∫ x, repulsionPotential x ^ 2 * ‖state.value spin x‖ ^ 2) ≤
      4 * (n : ℝ) ^ 3 * ∑ i, ∑ k : Fin 3, ∫ x, ‖state.gradient spin (i, k) x‖ ^ 2 := by
  let G : Fin n → ℝ := fun i => ∑ k : Fin 3, ∫ x, ‖state.gradient spin (i, k) x‖ ^ 2
  have hG (i : Fin n) : 0 ≤ G i :=
    Finset.sum_nonneg fun k _ => integral_nonneg fun x => sq_nonneg _
  have hterm (p : Fin n × Fin n) :
      Integrable (fun x => pairRepulsionTerm p x ^ 2 * ‖state.value spin x‖ ^ 2) ∧
      (∫ x, pairRepulsionTerm p x ^ 2 * ‖state.value spin x‖ ^ 2) ≤ 4 * G p.1 := by
    by_cases hp : p.1 < p.2
    · simpa only [pairRepulsionTerm, ite_eq_left hp, G] using
        pair_hardy_square state spin p.1 p.2 hp.ne
    · simp only [pairRepulsionTerm, ite_eq_right hp, zero_pow (by decide : 2 ≠ 0),
        zero_mul, integral_zero]
      exact ⟨integrable_zero _ _ _, by positivity⟩
  let majorant : Configuration n → ℝ := fun x =>
    (n : ℝ) ^ 2 * ∑ p : Fin n × Fin n, pairRepulsionTerm p x ^ 2 * ‖state.value spin x‖ ^ 2
  have hmajorant : Integrable majorant :=
    (integrable_finsetSum _ (fun p _ => (hterm p).1)).const_mul _
  have hdom (x : Configuration n) :
      repulsionPotential x ^ 2 * ‖state.value spin x‖ ^ 2 ≤ majorant x := by
    have h := mul_le_mul_of_nonneg_right (repulsionPotential_square_bound x)
      (sq_nonneg ‖state.value spin x‖)
    simpa only [majorant, Finset.sum_mul, mul_assoc] using h
  have hmeas : AEStronglyMeasurable
      (fun x => repulsionPotential x ^ 2 * ‖state.value spin x‖ ^ 2) volume :=
    ((repulsionPotential_measurable n).pow_const 2).aestronglyMeasurable.mul
      ((state.value_L2 spin).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).aestronglyMeasurable
  have hI : Integrable (fun x => repulsionPotential x ^ 2 * ‖state.value spin x‖ ^ 2) := by
    apply hmajorant.mono' hmeas
    exact Filter.Eventually.of_forall fun x => by
      change |repulsionPotential x ^ 2 * ‖state.value spin x‖ ^ 2| ≤ majorant x
      rw [abs_of_nonneg (by positivity)]
      exact hdom x
  refine ⟨hI, (integral_mono hI hmajorant hdom).trans ?_⟩
  change (∫ x, (n : ℝ) ^ 2 * ∑ p : Fin n × Fin n,
    pairRepulsionTerm p x ^ 2 * ‖state.value spin x‖ ^ 2) ≤ _
  rw [integral_const_mul, integral_finsetSum _ (fun p _ => (hterm p).1)]
  calc
    _ ≤ (n : ℝ) ^ 2 * ∑ p : Fin n × Fin n, 4 * G p.1 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun p _ => (hterm p).2) (sq_nonneg _)
    _ = _ := by
      simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
      unfold G
      ring

theorem repulsion_mul_memLp {n : ℕ} (state : Coulomb.H1Vector n)
    (spin : Coulomb.Spins n) :
    MemLp (fun x => (repulsionPotential x : ℂ) * state.value spin x) 2 := by
  have hm : AEStronglyMeasurable
      (fun x => (repulsionPotential x : ℂ) * state.value spin x) volume :=
    (repulsionPotential_measurable n).complex_ofReal.aestronglyMeasurable.mul
      (state.value_L2 spin).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hm).2
  simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs] using
    (repulsionPotential_spin_L2_bound state spin).1

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_BoundedFormCross
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polarization of the actual bounded-potential quadratic form on the
full weak-H1 graph. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def graphBoundedCross {n : ℕ}
    (A : Lp ℂ 2 (volume : Measure (Configuration n)) →L[ℝ]
      Lp ℂ 2 (volume : Measure (Configuration n))) (f g : H1Coordinates n) : ℝ :=
  (1/2:ℝ)*(∑ s, ∑ a, inner ℝ (f (Sum.inr (s,a))) (g (Sum.inr (s,a))))+
    ∑ s, inner ℝ (f (Sum.inl s)) (A (g (Sum.inl s)))

def graphComplexCross {n : ℕ}
    (A : Lp ℂ 2 (volume : Measure (Configuration n)) →L[ℝ]
      Lp ℂ 2 (volume : Measure (Configuration n))) (f g : H1Coordinates n) : ℂ :=
  (1/2:ℂ)*(∑ s, ∑ a, inner ℂ (f (Sum.inr (s,a))) (g (Sum.inr (s,a))))+
    ∑ s, inner ℂ (f (Sum.inl s)) (A (g (Sum.inl s)))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_RepulsionCross
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual Coulomb interaction has a polynomial mixed-form bound.
The multiplier acts on full spinful H1 states and takes values in L2. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def repulsionMultiplier {n : ℕ} (u : Coulomb.H1Vector n) (s : SpinConfiguration n) :
    Lp ℂ 2 (volume : Measure (Configuration n)) :=
  (repulsion_mul_memLp u s).toLp (fun x => (repulsionPotential x:ℂ)*u.value s x)

def repulsionCross {n : ℕ} (u v : Coulomb.H1Vector n) : ℝ :=
  ∑ s, inner ℝ (repulsionMultiplier u s) (h1Coordinates v (Sum.inl s))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_Cubature
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

def gaussTwoPoint (f : ℝ → ℝ) : ℝ := f (-gaussAbscissa) + f gaussAbscissa

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_FlowPathJets
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spatial derivatives as continuous paths. Taking derivatives in this
Banach space preserves the integral equation through order four without
requiring a fifth joint derivative of the vector field. -/

noncomputable section
open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
namespace ContinuumCoulomb
open WeakMTWTransport

abbrev SpatialPath := C(UnitTime, Position)

def modelPath (H : ℝ × Position → Position) (hH : Continuous H)
    (y : Position) : SpatialPath :=
  ⟨fun t => H (t,y), hH.comp (continuous_subtype_val.prodMk continuous_const)⟩

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_FlowUniform
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Discharge the finite C⁴ flow input by the four variational estimates. -/

noncomputable section
open Set
open scoped ContDiff
namespace ContinuumCoulomb

def UniformFlowDerivativeBound (B C : ℝ) (k : ℕ) : Prop :=
  ∀ (U : Set (ℝ × Position)), IsOpen U →
    Icc (0:ℝ) 1 ×ˢ (univ : Set Position) ⊆ U →
    ∀ v : ℝ → Position → Position,
    ContDiffOn ℝ 4 (fun p : ℝ × Position => v p.1 p.2) U →
    (∀ j ≤ 4, ∀ t ∈ Icc (0:ℝ) 1, ∀ x,
      ‖iteratedFDeriv ℝ j (fun p : ℝ × Position => v p.1 p.2) (t,x)‖ ≤ B) →
    ∀ G : Position → ℝ → Position, IsUnitTimeFlow v G →
    ∀ r : ℕ, 1 ≤ r → r ≤ k → ∀ t ∈ Icc (0:ℝ) 1, ∀ x,
      ‖iteratedFDeriv ℝ r (fun y => G y t) x‖ ≤ C

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_GaussPositionCell
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual eight equal masses on any translated cube, with a fourth-order
error bound from the ambient fourth Fréchet derivative. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def positionCellGauss (b : Position) (h : ℝ) (f : Position → ℝ) : ℝ :=
  (h/2)^3 * gaussTwoPoint (fun x => gaussTwoPoint (fun y => gaussTwoPoint
    (fun z => f (cubePoint b (h/2) x y z))))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabCoordinates
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact ordinary product coordinates for the slab Coulomb integral.
These allow the finite-box potential to be treated by one-coordinate
integrals without changing the Euclidean volume normalization. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def slabTripleEquiv : Position ≃ᵐ SlabTriple :=
  (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.trans
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).trans
      ((MeasurableEquiv.refl ℝ).prodCongr
        (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ))))

def slabTripleBox (H S : ℝ) : Set SlabTriple :=
  Set.Icc (-H) H ×ˢ (Set.Icc (-H) H ×ˢ Set.Icc (-S) S)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CubeIntegral
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalized tensor cell integral is the ordinary Euclidean volume
integral on the translated cube, with no change of volume convention. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def cubeTripleBox (b : Position) (h : ℝ) : Set SlabTriple :=
  Set.Icc (b 0-h/2) (b 0+h/2) ×ˢ
    (Set.Icc (b 1-h/2) (b 1+h/2) ×ˢ Set.Icc (b 2-h/2) (b 2+h/2))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_WellCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A cover of the actual well support by boxes whose total volume is
linear in the number of wells and the vertical cutoff radius. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def wellCoverBox (u : PlanarPosition) (r S : ℝ) : Set Position :=
  WithLp.ofLp ⁻¹' Set.Icc ![u 0-r,u 1-r,-S] ![u 0+r,u 1+r,S]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_NuclearGridPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual equal-mass grid potential and its error against the
manufactured continuous potential, at every evaluation point. -/

noncomputable section
open MeasureTheory
open scoped BigOperators NNReal
namespace ContinuumCoulomb

def gridGaussIndex {ι : Type*} (index : ι → Fin 3 → ℤ)
    (a : ι × (Fin 3 → Fin 2)) : GaussLatticeIndex := (index a.1,a.2)

theorem gridGaussIndex_injective {ι : Type*} (index : ι → Fin 3 → ℤ)
    (hi : Function.Injective index) : Function.Injective (gridGaussIndex index) := by
  intro a b hab
  exact Prod.ext (hi (congrArg (fun z : GaussLatticeIndex => z.1) hab))
    (congrArg (fun z : GaussLatticeIndex => z.2) hab)

def gridNuclearPotential {ι : Type*} [Fintype ι] (index : ι → Fin 3 → ℤ)
    (G : Position → Position) (rho h : ℝ) (y : Position) : ℝ :=
  -(rho*h^3/8)*∑ a : ι × (Fin 3 → Fin 2),
    Coulomb.coulombKernel (y-G (gaussLatticePoint h (gridGaussIndex index a)))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CorrectedOneElectronProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The corrected orbital span lies in the actual one-electron weak-H1
domain, with arbitrary complex coefficients in each spin component. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def correctedOneElectronValue (freq : ℝ) {m : ℕ} (u : Fin m → PlanarPosition)
    (c : SpinConfiguration 1 → Fin m → ℂ) (s : SpinConfiguration 1) (x : Configuration 1) : ℂ :=
  ∑ i, c s i*(correctedLocalizedMode freq u i (oneElectronCoordinates x) : ℂ)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabRegularization
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Regularization of the actual finite-slab potential. The singular
Coulomb limit is justified on the full volume integral; no continuity of
the slab indicator is assumed. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace ContinuumCoulomb

def regularizedSlabPotential (epsilon rho H S : ℝ) (y : Position) : ℝ :=
  -rho * ∫ x in slabDomain H S, NeutralAtom.regularizedKernel epsilon (y-x)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabPlanarTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The inverse-cube tail in two horizontal dimensions. Its exact mass is
`2π/H`, giving the finite-slab truncation error without divergent integrals. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def slabPlanarTail (H : ℝ) (p : PlanarPosition) : ℝ := slabRadialTail H ‖p‖

def slabPlanarBox (H : ℝ) : Set PlanarPosition :=
  {p | |p 0| ≤ H ∧ |p 1| ≤ H}

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabVerticalCoordinates
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertical-first coordinates for the actual three-dimensional slab. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def slabVerticalEquiv : Position ≃ᵐ ℝ × PlanarPosition :=
  (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.trans
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).trans
      ((MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabConfinement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative confinement by the actual finite rectangular Coulomb slab. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace ContinuumCoulomb

def slabPlanarSection (epsilon H z w : ℝ) : ℝ :=
  ∫ p in slabPlanarBox H, coulombLineKernel (epsilon^2+(z-w)^2) ‖p‖

def slabPlaneError (epsilon H z w : ℝ) : ℝ :=
  slabPlanarSection epsilon H z w-slabPlanarSection epsilon H 0 w+
    2*Real.pi*(Real.sqrt (epsilon^2+(z-w)^2)-Real.sqrt (epsilon^2+w^2))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabRegularity
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuity and global boundedness of the actual slab field, including
its discontinuous density at the slab boundary. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem slabDensity_nonnegative {rho : ℝ} (hrho : 0 ≤ rho) (H S : ℝ) (x : Position) :
    0 ≤ slabDensity rho H S x := by
  by_cases hx : x ∈ slabDomain H S
  · simpa [slabDensity, hx] using hrho
  · simp [slabDensity, hx]

theorem slabDensity_le {rho : ℝ} (hrho : 0 ≤ rho) (H S : ℝ) (x : Position) :
    slabDensity rho H S x ≤ rho := by
  by_cases hx : x ∈ slabDomain H S
  · simp [slabDensity, hx]
  · simpa [slabDensity, hx] using hrho

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedMomentTail
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Translated fourth/eighth moments and the weighted tails used in the
finite-slab operator estimate. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def localizedDensityMoment (freq : ℝ) (u : PlanarPosition) (k : ℕ) : ℝ :=
  ∫ x : Position, ‖x‖^k*localizedDensity freq u x

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabOrbitalResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite slab's actual harmonic-oscillator residual on a localized
orbital. Interior accuracy and weighted tails are kept separately. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def slabResidualMultiplier (rho H S : ℝ) (x : Position) : ℝ :=
  slabPotential rho H S x-slabPotential rho H S 0-2*Real.pi*rho*(x 2)^2

def slabOrbitalResidual (rho H S freq : ℝ) (u : PlanarPosition) (x : Position) : ℝ :=
  slabResidualMultiplier rho H S x*continuumLocalizedMode freq u x

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ManufacturedWeakResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The differential residual is an actual weak-H1 kinetic/potential
pairing identity. This is the bridge used for the off-diagonal form bound. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def oneElectronLocalizedMode (freq : ℝ) (u : PlanarPosition) (x : Configuration 1) : ℝ :=
  continuumLocalizedMode freq u (oneElectronCoordinates x)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CorrectedResidualPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual corrected-orbital mixed forms inherit the manufactured residual
bound on every state in the full one-electron weak-H1 domain. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def oneElectronCorrectedMode (freq : ℝ) {m : ℕ} (u : Fin m → PlanarPosition)
    (i : Fin m) (x : Configuration 1) : ℝ :=
  correctedLocalizedMode freq u i (oneElectronCoordinates x)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_NuclearPerturbedComplement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complement elimination with the actual singular nuclear error form.
The general form error enters quadratically through its mixed term. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def nuclearPerturbedForm {n : ℕ} (V : Configuration n → ℝ) (F : Position → ℝ)
    (u : Coulomb.H1Vector n) : ℝ := boundedPotentialForm V u+nuclearErrorEnergy F u

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabOriginQuadrature
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar slab shift is computed by cubature of a capped kernel on
the fixed cube. Its singular truncation error is independent of the box. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb.SlabOriginQuadrature

def capped (ε rho H S : ℝ) : ℝ := -rho * ∫ x in slabDomain H S, cappedCoulombKernel ε x

end ContinuumCoulomb.SlabOriginQuadrature

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_RealMollification
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth approximation of real L² functions on the actual configuration
space. Fatou and the contraction estimate suffice; no Sobolev density input
is used. This is the scalar approximation needed for the H=W discharge. -/

noncomputable section
open MeasureTheory Filter ContinuousLinearMap
open scoped Topology Convolution
namespace ContinuumCoulomb

def realMollification {n : ℕ} (u : Configuration n → ℝ) (k : ℕ) :
    Configuration n → ℝ := (Coulomb.hardyMollifier k).normed volume ⋆ u

theorem realMollification_smooth {n : ℕ} {u : Configuration n → ℝ}
    (hu : MemLp u 2) (k : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (realMollification u k) :=
  (Coulomb.hardyMollifier k).hasCompactSupport_normed.contDiff_convolution_left
    (lsmul ℝ ℝ) (Coulomb.hardyMollifier k).contDiff_normed
    (hu.locallyIntegrable (by norm_num))

theorem realMollification_contraction {n : ℕ} {u : Configuration n → ℝ}
    (hu : MemLp u 2) (k : ℕ) :
    MemLp (realMollification u k) 2 ∧
      (∫ x, realMollification u k x ^ 2) ≤ ∫ x, u x ^ 2 := by
  have h := Coulomb.convolution_sq_integral_le
    ((Coulomb.hardyMollifier k).normed volume) u
    ((Coulomb.hardyMollifier k).contDiff_normed (n := (⊤ : ℕ∞))).continuous
    (Coulomb.hardyMollifier k).hasCompactSupport_normed
    (Coulomb.hardyMollifier k).nonneg_normed
    (Coulomb.hardyMollifier k).integral_normed
    (hu.locallyIntegrable (by norm_num)) hu.integrable_sq
  exact ⟨(memLp_two_iff_integrable_sq
    (realMollification_smooth hu k).continuous.aestronglyMeasurable).mpr h.1,h.2⟩

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ComplexMollification
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Componentwise mollification preserves the actual complex weak derivatives.
All estimates here are unconditional. -/

noncomputable section
open MeasureTheory Filter ContinuousLinearMap
open scoped Topology Convolution
namespace ContinuumCoulomb

def complexMollification {n : ℕ} (u : Configuration n → ℂ) (k : ℕ) :
    Configuration n → ℂ := fun x =>
  (realMollification (fun y => (u y).re) k x : ℂ)+
    Complex.I*(realMollification (fun y => (u y).im) k x : ℂ)

@[simp] theorem complexMollification_re {n : ℕ} (u : Configuration n → ℂ) (k : ℕ)
    (x : Configuration n) :
    (complexMollification u k x).re = realMollification (fun y => (u y).re) k x := by
  simp [complexMollification]

@[simp] theorem complexMollification_im {n : ℕ} (u : Configuration n → ℂ) (k : ℕ)
    (x : Configuration n) :
    (complexMollification u k x).im = realMollification (fun y => (u y).im) k x := by
  simp [complexMollification]

theorem complexMollification_smooth {n : ℕ} {u : Configuration n → ℂ}
    (hu : MemLp u 2) (k : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (complexMollification u k) :=
  (Complex.ofRealCLM.contDiff.comp (realMollification_smooth (re_memLp hu) k)).add
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (realMollification_smooth (im_memLp hu) k)))

theorem complexMollification_memLp {n : ℕ} {u : Configuration n → ℂ}
    (hu : MemLp u 2) (k : ℕ) : MemLp (complexMollification u k) 2 := by
  apply (memLp_two_iff_integrable_sq_norm
    (complexMollification_smooth hu k).continuous.aestronglyMeasurable).mpr
  simp_rw [Coulomb.complex_norm_sq_components,complexMollification_re,complexMollification_im]
  exact ((realMollification_contraction (re_memLp hu) k).1.integrable_sq).add
    ((realMollification_contraction (im_memLp hu) k).1.integrable_sq)

theorem complexMollification_partial {n : ℕ} {u g : Configuration n → ℂ}
    (hu : MemLp u 2) (hg : MemLp g 2) (v : Configuration n)
    (hw : ∀ (φ : Configuration n → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, u x*(fderiv ℝ φ x v:ℂ)) = -(∫ x, g x*(φ x:ℂ)))
    (k : ℕ) (x : Configuration n) :
    fderiv ℝ (complexMollification u k) x v = complexMollification g k x := by
  have hd (L : ℂ →L[ℝ] ℝ) :
      fderiv ℝ (realMollification (fun y => L (u y)) k) x v =
        realMollification (fun y => L (g y)) k x :=
    Coulomb.weak_convolution_partial _ _ _ v
      ((L.comp_memLp' hu).locallyIntegrable (by norm_num))
      (Coulomb.hardyMollifier k).contDiff_normed
      (Coulomb.hardyMollifier k).hasCompactSupport_normed
      (Coulomb.weak_complex_component u g hu hg v hw L) x
  have hc := (complexMollification_smooth hu k).differentiable (by simp)
  have hp (L : ℂ →L[ℝ] ℝ) :
      fderiv ℝ (fun y => L (complexMollification u k y)) x v =
        L (fderiv ℝ (complexMollification u k) x v) :=
    congrArg (fun A : Configuration n →L[ℝ] ℝ => A v)
      (L.hasFDerivAt.comp x (hc x).hasFDerivAt).fderiv
  apply Complex.ext
  · have h := hp Complex.reCLM
    simp only [Complex.reCLM_apply,complexMollification_re] at h
    have hderiv := hd Complex.reCLM
    simp only [Complex.reCLM_apply] at hderiv
    change fderiv ℝ (realMollification (fun y => (u y).re) k) x v = _ at h
    rw [hderiv] at h
    simpa only [Complex.reCLM_apply,complexMollification_re] using h.symm
  · have h := hp Complex.imCLM
    simp only [Complex.imCLM_apply,complexMollification_im] at h
    have hderiv := hd Complex.imCLM
    simp only [Complex.imCLM_apply] at hderiv
    change fderiv ℝ (realMollification (fun y => (u y).im) k) x v = _ at h
    rw [hderiv] at h
    simpa only [Complex.imCLM_apply,complexMollification_im] using h.symm

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

def adjustedContactVertex (lengths : ℕ → ℝ) (h : ℝ) (k : ℕ) : ContactPoint :=
  contactPoint (∑ j ∈ Finset.range k, adjustedContactStepX lengths h j)
    (∑ j ∈ Finset.range k, adjustedContactStepY h j)

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

def contactGadgetRightNode (negative : Bool) (k : Fin 10) : ContactGadgetSite :=
  if hk : k = 0 then
    if negative then Sum.inl 9 else contactGadgetSide
  else Sum.inr (Sum.inl ⟨k.val - 1, by have := k.isLt; omega⟩)

def contactGadgetPosition (negative : Bool) (central : ℝ)
    (leftLengths rightLengths : ℕ → ℝ) (leftHeight rightHeight : ℝ) :
    ContactGadgetSite → ContactPoint :=
  Sum.elim (fun k => adjustedContactVertex leftLengths leftHeight k.val)
    (Sum.elim (fun k => contactPoint (contactGadgetRightOrigin negative central) 0 +
      adjustedContactVertex rightLengths rightHeight (k.val + 1))
      (fun _ => if negative then contactPoint (17 / 2) central
        else contactPoint (contactGadgetRightOrigin negative central) 0))

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

def horizontalContact (a b : ℤ) (p : ContactStripSite) : ContactPoint :=
  contactPoint (17 * a + p.axial) (17 * b + p.transverse)

def verticalContact (a b : ℤ) (p : ContactStripSite) : ContactPoint :=
  contactPoint (17 * a - p.transverse) (17 * b + p.axial)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactPathBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate bounds for the two explicit paths. These imply the fixed strip
conditions used to separate gadgets throughout an arbitrarily large lattice. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators

theorem contactSlopeHeight_bounds {c : ℝ} (hc : 3 / 4 ≤ c) (hc' : c ≤ 7 / 8) :
    0 ≤ contactSlopeHeight c ∧ contactSlopeHeight c ≤ 2 / 3 := by
  have hs := contactSlopeHeight_sq (by linarith : -1 ≤ c) (by linarith : c ≤ 1)
  have hn : 0 ≤ contactSlopeHeight c := Real.sqrt_nonneg _
  exact ⟨hn, by nlinarith⟩

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactBaseSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact nineteen-link base gadget and all of its nonlink separations. -/

noncomputable section
namespace ContinuumCoulomb

def contactGadgetLinked (negative : Bool) : ContactGadgetSite → ContactGadgetSite → Prop
  | Sum.inl i, Sum.inl j => Nat.dist i.val j.val = 1
  | Sum.inl i, Sum.inr (Sum.inl j) => negative = true ∧ i = 9 ∧ j = 0
  | Sum.inr (Sum.inl j), Sum.inl i => negative = true ∧ i = 9 ∧ j = 0
  | Sum.inl i, Sum.inr (Sum.inr _) => i = 9
  | Sum.inr (Sum.inr _), Sum.inl i => i = 9
  | Sum.inr (Sum.inl i), Sum.inr (Sum.inl j) => Nat.dist i.val j.val = 1
  | Sum.inr (Sum.inl i), Sum.inr (Sum.inr _) => negative = false ∧ i = 0
  | Sum.inr (Sum.inr _), Sum.inr (Sum.inl i) => negative = false ∧ i = 0
  | Sum.inr (Sum.inr _), Sum.inr (Sum.inr _) => False

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactExtent
attribute [-simp] _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The contact realization preserves polynomial coordinate extent. -/

noncomputable section
namespace ContinuumCoulomb

@[simp] theorem contactGridPoint_apply (a : ℤ × ℤ) (i : Fin 2) :
    contactGridPoint a i = 17 * (contactGridAxis a i : ℝ) := by
  fin_cases i <;> rfl

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedCoulombNumerics
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual six-coordinate bounded integrand for Coulomb quadrature,
with an explicit error to the original full singular coefficient. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def localizedCappedIntegrand (freq ε : ℝ) (u v : PlanarPosition) (p : Position × Position) : ℝ :=
  localizedDensity freq u p.1 *
    (cappedCoulombKernel ε (p.1 - p.2) * localizedDensity freq v p.2)

def localizedCappedCoulombCoeff (freq ε : ℝ) (u v : PlanarPosition) : ℝ :=
  ∫ p, localizedCappedIntegrand freq ε u v p

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedRawDensity
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unnormalized packets used by the literal Coulomb quadrature. Squaring
the normalization cancels the Gaussian square root, so the final quotient
uses only the already certified planar mass, frequency and pi evaluators. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def localizedRawDensity (freq : ℝ) (x : Position) : ℝ :=
  planarResolventMode (positionSplitCoordinates x).1 ^ 2 *
    Real.exp (-freq * (positionSplitCoordinates x).2 ^ 2)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_RawDensityModulus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative continuity needed by the six-coordinate finite-box
quadrature. Only the box radius enters the Gaussian modulus. -/

noncomputable section
namespace ContinuumCoulomb

def splitRawDensity (freq : ℝ) (p : SplitPosition) : ℝ :=
  planarResolventMode p.1 ^ 2 * Real.exp (-freq * p.2 ^ 2)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CoulombCubeModulus
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinatewise Lipschitz control of the actual Coulomb box integrand. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb
open UniformQuadrature

def rawCoulombSix (freq ε : ℝ) (shift : Position) (v : Fin 6 → ℝ) : ℝ :=
  cappedPairIntegrand ε shift (localizedRawDensity freq) (localizedRawDensity freq)
    (twoParticleCoordinates v)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarHeatBoxCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact two-coordinate box formula for the actual heat average.
The forcing vanishes outside this fixed square, so spatial truncation
introduces no error. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def planarPairEquiv : PlanarPosition ≃ᵐ ℝ × ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans
    (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarHeatBoxBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit coordinate bounds on the fixed forcing square. They turn
the kernel estimates into concrete quadrature constants for every input
point, with polynomial dependence on its magnitude. -/

noncomputable section
namespace ContinuumCoulomb

def planarBoxSpatialConstant (r : PlanarPosition) (η : ℝ) : ℝ :=
  2 * (‖r‖ + 2) / η ^ 2 + 32 * η⁻¹

def planarBoxTimeConstant (r : PlanarPosition) (η : ℝ) : ℝ :=
  η⁻¹ ^ 2 + η⁻¹ * (1 + (‖r‖ + 2) ^ 2 / (4 * η ^ 2))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarHeatTruncation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit time truncation for the actual resolvent representation.
The omitted short-time interval costs at most its length; the long-time
tail is at most the elementary exponential tail. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def planarTruncatedHeat (r : PlanarPosition) (η T : ℝ) : ℝ :=
  ∫ t in η..T, Real.exp (-t) * planarHeatAverage t r

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_RationalHeatPlaneError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Error of the actual rational two-coordinate heat quadrature.
The sample evaluator is the concrete Taylor/π/forcing program. -/

namespace ContinuumCoulomb.RationalHeatBox

def spatialNode (N i : ℕ) : ℚ := RationalQuadratureProgram.node (-1) (spatialStep N) i

end ContinuumCoulomb.RationalHeatBox

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_RationalResolventError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual computed three-dimensional heat quadrature approximates
the constructed planar resolvent. The bound includes both numerical
quadrature and the explicitly proved short/long-time tails. -/

noncomputable section
namespace ContinuumCoulomb.RationalHeatBox

def timeEndpoint (x : Input) : ℚ :=
  RationalQuadratureProgram.node x.2.2.1 x.2.2.2 x.1

end ContinuumCoulomb.RationalHeatBox

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_RawCoulombSample
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal rational sample of the six-coordinate Coulomb integrand.
Both density factors and the capped kernel use the certified programs. -/

noncomputable section
namespace ContinuumCoulomb.RawCoulombSample
open CappedKernelProgram

def inBox (R : ℕ) (x : Triple) : Prop :=
  |(x.1 : ℝ)| ≤ R ∧ |(x.2.1 : ℝ)| ≤ R ∧ |(x.2.2 : ℝ)| ≤ R

end ContinuumCoulomb.RawCoulombSample

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CoulombQuadrature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual six-coordinate cubature of the finite Coulomb integral. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb.RawCoulombSample
open UniformQuadrature

def sampled (rho R P b : ℕ) (ε : ℚ) (s : CappedKernelProgram.Triple)
    (a h : ℚ) (w : Fin 6 → ℕ) : ℝ :=
  value rho R P b ε s
    (RationalQuadratureProgram.node a h (w 0),
      RationalQuadratureProgram.node a h (w 1),
      RationalQuadratureProgram.node a h (w 2))
    (RationalQuadratureProgram.node a h (w 3),
      RationalQuadratureProgram.node a h (w 4),
      RationalQuadratureProgram.node a h (w 5))

end ContinuumCoulomb.RawCoulombSample

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

def Antisymmetric {N Q : ℕ} (ψ : State N Q) : Prop :=
  ∀ (i j : Fin N), i ≠ j → ∀ a, ψ (a ∘ Equiv.swap i j) = -ψ a

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ092_CC.Laughlin_Exterior_Scaling
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_apply _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_add _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_coordinates _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_mul _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_smul _root_.OAI.ContinuumCoulomb.OccupationFock.sectorEquiv_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock

noncomputable def orbitalScaling (Q : ℕ) (d : Fin (Q+1) → ℂ) : Orbital Q →ₗ[ℂ] Orbital Q where
  toFun v i := d i*v i
  map_add' v w := by ext i; simp [mul_add]
  map_smul' c v := by ext i; simp [mul_left_comm]

noncomputable def exteriorScaling (Q : ℕ) (d : Fin (Q+1) → ℂ) : Space Q →ₐ[ℂ] Space Q :=
  ExteriorAlgebra.map (orbitalScaling Q d)

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ092_CC.Laughlin_Exterior_OccupationMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Topology

noncomputable def occupationNormSq (Q : ℕ) (x : Space Q) : ℝ :=
  ∑ A : Finset (Fin (Q+1)), ‖(occupationBasis Q).repr x A‖^2

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ092_CC.Laughlin_Fock_Creation
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_apply _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_add _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_coordinates _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_mul _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_smul _root_.OAI.ContinuumCoulomb.OccupationFock.sectorEquiv_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem occupation_singleton (Q : ℕ) (i : Fin (Q+1)) :
    occupationBasis Q {i} = ExteriorAlgebra.ι ℂ (mode i) := by
  let A : Set.powersetCard (Fin (Q+1)) 1 := ⟨{i},Finset.card_singleton i⟩
  have hi : Set.powersetCard.ofFinEmbEquiv.symm A 0 = i := by
    have hm := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem A
      (Set.powersetCard.ofFinEmbEquiv.symm A 0)).mp ⟨0,rfl⟩
    exact Finset.mem_singleton.mp hm
  change (Pi.basisFun ℂ (Fin (Q+1))).ExteriorAlgebra A.val = _
  rw [ExteriorAlgebra.basis_apply_powersetCard]
  simp only [ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_succ_apply,
    ExteriorAlgebra.ιMulti_zero_apply, mul_one, Function.comp_apply, hi]
  simp [Pi.basisFun_apply, mode]

theorem create_unoccupied_sign (Q : ℕ) (i : Fin (Q+1))
    (A : Finset (Fin (Q+1))) (hi : i ∉ A) :
    ∃ ε : ℂ, (ε = 1 ∨ ε = -1) ∧
      create i (occupationBasis Q A) = ε • occupationBasis Q (insert i A) := by
  let S : Set.powersetCard (Fin (Q+1)) 1 := ⟨{i},Finset.card_singleton i⟩
  let T : Set.powersetCard (Fin (Q+1)) A.card := ⟨A,rfl⟩
  have hd : Disjoint S.val T.val := by simpa [S,T] using hi
  have h := ExteriorAlgebra.basis_mul_of_disjoint (Pi.basisFun ℂ (Fin (Q+1))) S T hd
  rcases Int.units_eq_one_or (Set.powersetCard.permOfDisjoint hd).sign with hs | hs
  · refine ⟨1,Or.inl rfl,?_⟩
    simpa [hs,S,T,occupationBasis,Set.powersetCard.disjUnion,
      ← occupation_singleton Q i, create] using h
  · refine ⟨-1,Or.inr rfl,?_⟩
    simpa [hs,S,T,occupationBasis,Set.powersetCard.disjUnion,
      ← occupation_singleton Q i, create] using h

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ092_CC.Laughlin_Fock_Annihilation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock

noncomputable def insertionSign (Q : ℕ) (i : Fin (Q+1)) (A : Finset (Fin (Q+1))) : ℂ :=
  if h : i ∉ A then (create_unoccupied_sign Q i A h).choose else 1

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ092_CC.Laughlin_Fock_Adjoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

noncomputable def occupationInner (Q : ℕ) (x y : Space Q) : ℂ :=
  ∑ A : Finset (Fin (Q+1)), star ((occupationBasis Q).repr x A) * (occupationBasis Q).repr y A

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ092_CC.Laughlin_Tensor_ExteriorRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Matrix

noncomputable def tensorExterior (N Q : ℕ) (ψ : State N Q) : Space Q :=
  ∑ a, ψ a • ExteriorAlgebra.ιMulti ℂ N (fun k => mode (a k))

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ092_CC.Laughlin_Tensor_ExteriorContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

noncomputable def orderedWedge {n Q : ℕ} (a : Configuration n Q) : Space Q :=
  ExteriorAlgebra.ιMulti ℂ n (fun k => mode (a k))

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ092_CC.Laughlin_Tensor_ExteriorIsometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

noncomputable def normalizedTensorExterior (n Q : ℕ) (ψ : State n Q) : Space Q :=
  ((Real.sqrt (n.factorial : ℝ))⁻¹ : ℂ) • tensorExterior n Q ψ

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_GridNuclei
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The transported Gauss cloud is an actual collection of distinct unit
nuclei. Its physical form has exactly the slab-origin energy offset. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem gaussLatticePoint_injective {h : ℝ} (hh : 0 < h) :
    Function.Injective (gaussLatticePoint h) := by
  intro a b hab
  by_contra hne
  have hs := gaussLatticePoint_separation hh a b hne
  rw [hab,sub_self,norm_zero] at hs
  linarith

def gridNuclei {ι : Type*} [Fintype ι] [Nonempty ι] (index : ι → Fin 3 → ℤ)
    (hi : Function.Injective index) (G : Position → Position) (hG : Function.Injective G)
    {h : ℝ} (hh : 0 < h) : Coulomb.Nuclei (Fintype.card (ι × (Fin 3 → Fin 2))) where
  nonempty := Fintype.card_pos
  position a := G (gaussLatticePoint h
    (gridGaussIndex index ((Fintype.equivFin (ι × (Fin 3 → Fin 2))).symm a)))
  distinct := (hG.comp ((gaussLatticePoint_injective hh).comp
    (gridGaussIndex_injective index hi))).comp (Fintype.equivFin _).symm.injective
  charge _ := 1
  charge_ge_one _ := le_rfl

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedFockStates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every state of the actual full half-filled Fock space is realized by
an antisymmetric weak-H1 continuum state in the corrected localized modes.
The continuum mass is exactly the finite occupation norm. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb
open HubbardGlobal

def localizedSpinMode (freq : ℝ) {m : ℕ} (u : Fin (m+1) → PlanarPosition)
    (j : Fin ((2*m+1)+1)) : Position → Fin 2 → ℂ :=
  realSpinOrbital (correctedLocalizedMode freq u ((siteModes m).symm j).1) ((siteModes m).symm j).2

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarWeakConstant
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.planarHeatResolventPrimitive_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A locally integrable planar function with zero distributional gradient
is constant almost everywhere. This is the uniqueness step needed after the
ground-state transform; it uses actual compact mollifiers. -/

noncomputable section
open MeasureTheory Filter ContinuousLinearMap
open scoped Topology Convolution ContDiff
namespace ContinuumCoulomb

local instance instPlanarWeakConstantMeasurable : MeasurableSpace PlanarPosition := borel PlanarPosition
local instance instPlanarWeakConstantBorel : BorelSpace PlanarPosition := ⟨rfl⟩
local instance instPlanarWeakConstantMeasure : MeasureSpace PlanarPosition := measureSpaceOfInnerProductSpace

def planarMollifier (k : ℕ) : ContDiffBump (0 : PlanarPosition) where
  rIn := 1/((k:ℝ)+1)
  rOut := 2/((k:ℝ)+1)
  rIn_pos := one_div_pos.mpr (by positivity)
  rIn_lt_rOut := div_lt_div_of_pos_right (by norm_num) (by positivity)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarDistributionAxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two coordinate distributional derivatives determine the full planar
weak gradient. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace ContinuumCoulomb

local instance instPlanarDistributionAxesMeasurable : MeasurableSpace PlanarPosition := borel PlanarPosition
local instance instPlanarDistributionAxesBorel : BorelSpace PlanarPosition := ⟨rfl⟩
local instance instPlanarDistributionAxesMeasure : MeasureSpace PlanarPosition := measureSpaceOfInnerProductSpace

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarGroundIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact ground-state transform for the actual manufactured planar well. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def planarGroundQuotient (u : PlanarPosition → ℝ) (x : PlanarPosition) : ℝ :=
  u x/planarResolventMode x

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarNormalizationTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative truncation of the actual planar normalization integral.
All constants below depend only on the fixed manufactured forcing. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def planarNormalizationTailConstant : ℝ :=
  planarExponentialConstant (1 / 2) ^ 2 *
    ∫ r : PlanarPosition, Real.exp (-(1 / 2 : ℝ) * ‖r‖)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarNormalizationBox
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite square approximates the actual normalization integral with
an explicit exponential error; no compact-support surrogate is used. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def planarNormalizationBox (L : ℝ) : ℝ :=
  ∫ x in (-L)..L, ∫ y in (-L)..L,
    planarResolventMode (planarPairEquiv.symm (x, y)) ^ 2

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

def value (D B : ℕ) (q : ℚ) : ℚ := (numerator D B q:ℚ)/(D:ℚ)

end ContinuumCoulomb.RationalBoxRound

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_RealOneElectronState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real spatial functions embedded into the full spinful one-electron
weak-H1 space. This transfers nuclear form estimates to orbital products. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def realOneElectronState (f : Position → ℝ) (hf : ContDiff ℝ 1 f) (hL2 : MemLp f 2)
    (hd : ∀ e : Position, MemLp (fun x => fderiv ℝ f x e) 2) : Coulomb.H1Vector 1 :=
  classicalH1State (fun _ x => (f (oneElectronCoordinates x) : ℂ))
    (fun _ => Complex.ofRealCLM.contDiff.comp (hf.comp oneElectronCoordinates.contDiff))
    (fun _ => (hL2.comp_measurePreserving oneElectronCoordinates.measurePreserving).ofReal)
    (fun _ a => by
      have hm : MemLp (fun x : Configuration 1 =>
          (fderiv ℝ f (oneElectronCoordinates x) (EuclideanSpace.single a.2 1) : ℂ)) 2 :=
        ((hd (EuclideanSpace.single a.2 1)).comp_measurePreserving
        oneElectronCoordinates.measurePreserving).ofReal
      simpa only [real_one_electron_partial hf] using hm)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_SobolevDensity
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The whole-space H=W specialization required by the two continuum
reductions. The approximation is constructed by normalized smooth convolution,
with no published density hypothesis remaining. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace ContinuumCoulomb

def mollifiedH1 {n : ℕ} (u : Coulomb.H1Vector n) (k : ℕ) : Coulomb.H1Vector n :=
  classicalH1State (fun s => complexMollification (u.value s) k)
    (fun s => (complexMollification_smooth (u.value_L2 s) k).of_le (by first | simp | exact_mod_cast le_top))
    (fun s => complexMollification_memLp (u.value_L2 s) k)
    (fun s a => by
      have he := complexMollification_partial (u.value_L2 s) (u.partial_L2 s a)
        (EuclideanSpace.single a 1) (u.weak_partial s a) k
      simp_rw [he]
      exact complexMollification_memLp (u.partial_L2 s a) k)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_UnitBinaryInclusion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The unit-charge target is a special case of the binary-charge target.
The inclusion preserves the actual full fermionic continuum energy and
both promise thresholds. -/

namespace ContinuumCoulomb

noncomputable section

theorem unitBinary_yes {d : UnitCoulomb} (h : d ∈ unitCoulombPromise.yes) :
    d.toBinary ∈ binaryCoulombPromise.yes := by
  obtain ⟨hv, he⟩ := h
  refine ⟨d.toBinary_valid hv, ?_⟩
  rw [d.toBinary_energy hv]
  exact he

theorem unitBinary_no {d : UnitCoulomb} (h : d ∈ unitCoulombPromise.no) :
    d.toBinary ∈ binaryCoulombPromise.no := by
  obtain ⟨hv, he⟩ := h
  refine ⟨d.toBinary_valid hv, ?_⟩
  rw [d.toBinary_energy hv]
  exact he

end
end ContinuumCoulomb

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

theorem position_length_pos (p : BinaryPosition) : 0 < (binaryPositionCodec.encode p).length := by
  have hx := SourcePrograms.integer_length_pos p.x.numerator
  change 0 < ((BinaryEncoding.integer.encode p.x.numerator ++
    BinaryEncoding.natural.encode p.x.denominator) ++ _).length
  simp only [List.length_append]
  omega

end ContinuumCoulomb.UnitBinaryProgram

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

theorem rounded_eq (k : ℕ) (d : BinaryHeisenberg) (h : d.Valid) :
    SourceNormalizationProgram.rounded (input k d) =
      SourceNormalizedSpectrum.rounded (d.toSource h) (roundingDenominator k d) := by
  simp only [SourceNormalizationProgram.rounded, input, List.length_map, List.map_map]
  change d.edges.map (fun e => (e.left, e.right,
      SourceCoefficientRounding.coefficient (roundingDenominator k d) e.coefficient.value)) =
    List.ofFn (fun e : Fin d.edges.length => ((d.edges.get e).left, (d.edges.get e).right,
      SourceCoefficientRounding.coefficient (roundingDenominator k d) (d.edges.get e).coefficient.value))
  simpa only [List.get_eq_getElem] using (List.ofFn_getElem_eq_map d.edges
    (fun e => (e.left, e.right,
      SourceCoefficientRounding.coefficient (roundingDenominator k d) e.coefficient.value))).symm

theorem retained_eq (k : ℕ) (d : BinaryHeisenberg) (h : d.Valid) :
    SourceNormalizationProgram.retained (input k d) =
      SourceNormalizedSpectrum.retained (d.toSource h) (roundingDenominator k d) := by
  unfold SourceNormalizationProgram.retained SourceNormalizedSpectrum.retained
  rw [rounded_eq k d h]

theorem normalized_eq (k : ℕ) (d : BinaryHeisenberg) (h : d.Valid) :
    SourceNormalizationProgram.normalized (input k d) =
      (((SourceNormalizedSpectrum.retained (d.toSource h) (roundingDenominator k d)).length,
        roundingDenominator k d + size d ^ k + 1, size d ^ k, d.coordinate.length),
        SourceNormalizedSpectrum.retained (d.toSource h) (roundingDenominator k d)) := by
  unfold SourceNormalizationProgram.normalized
  rw [retained_eq k d h]
  simp only [input, List.length_map, roundingDenominator]

end ContinuumCoulomb.SourceMetadataProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourcePositiveBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual source normalization and metadata programs give one fixed
polynomial coefficient exponent for the final positive-spin graph. -/

noncomputable section
namespace ContinuumCoulomb.SourceMetadataProgram
open ExactQuantumFactoring.BitStackProgram MediatorListProgram

attribute [local irreducible] MediatorParameters.finalWeight

abbrev finalBound (k : ℕ) (d : BinaryHeisenberg) : ℕ :=
  MediatorParameters.finalWeight
    (SourceNormalizationProgram.normalized (input k d)).1.1
    (SourceNormalizationProgram.normalized (input k d)).1.2.1
    (SourceNormalizationProgram.normalized (input k d)).1.2.2.1

end ContinuumCoulomb.SourceMetadataProgram

end

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

abbrev sourceFamily (k : ℕ) (d : BinaryHeisenberg) (h : d.Valid) :=
  SourceNormalizedSpectrum.family (d.toSource h) (roundingDenominator k d)

end ContinuumCoulomb.SourcePositiveProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourcePhysicalThreshold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal raw-source assembly of the complete physical threshold pair.
The same fixed powers determine the calibration amplification, the centered
nuclear mesh, and the rational slab dimensions. -/

namespace ContinuumCoulomb.SourcePhysicalThreshold
open ExactQuantumFactoring.BitStackProgram

def mesh (k : ℕ) (d : BinaryHeisenberg) : ℕ := SourceContactProgram.size d^(10*k)
def horizontalRadius (k : ℕ) (d : BinaryHeisenberg) : ℕ := SourceContactProgram.size d^(60*k)
def verticalRadius (k : ℕ) (d : BinaryHeisenberg) : ℕ := SourceContactProgram.size d^(15*k)
def slabHorizontal (k : ℕ) (d : BinaryHeisenberg) : ℚ :=
  SlabBoxSchedule.centeredWidth (horizontalRadius k d) (mesh k d)
def slabVertical (k : ℕ) (d : BinaryHeisenberg) : ℚ :=
  SlabBoxSchedule.centeredWidth (verticalRadius k d) (mesh k d)

end ContinuumCoulomb.SourcePhysicalThreshold

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_SourceNuclearProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Raw-source assembly of the actual transported unit nuclei. The well
scale is exactly lambda, the cutoff width is the exact centered slab width,
and all three lattice radii come from the same powers as the thresholds. -/

namespace ContinuumCoulomb.SourceNuclearProgram
open ExactQuantumFactoring.BitStackProgram

def amplification (rho k : ℕ) (d : BinaryHeisenberg) : ℚ :=
  CenteredPhysicalThreshold.amplification rho (SourcePhysicalThreshold.mesh k d)

end ContinuumCoulomb.SourceNuclearProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumAncilla
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.ContinuumCoulomb.qmaApplyMatrix_one _root_.OAI.ContinuumCoulomb.qmaClockIndex_fin _root_.OAI.ContinuumCoulomb.qmaHistoryFromVector_fin _root_.OAI.ContinuumCoulomb.qmaMask_apply _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_length _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact witness embedding into the zero-ancilla subspace. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators

theorem qmaWitnessExtend_ancilla (c : QMACircuit) (s : SourceSpinBasis c.witness) :
    QMAAncillaZero c (qmaWitnessExtend c s) := by
  intro i hi
  simp [qmaWitnessExtend,not_lt.mpr hi]

theorem qmaWitnessExtend_restrict (c : QMACircuit) (hc : c.WellFormed)
    (s : SourceSpinBasis (c.work+1)) (hs : QMAAncillaZero c s) :
    qmaWitnessExtend c (qmaWitnessRestrict c hc s) = s := by
  funext i
  by_cases hi : i.val < c.witness
  · simp [qmaWitnessExtend,qmaWitnessRestrict,hi]
  · simp [qmaWitnessExtend,hi,hs i (Nat.le_of_not_gt hi)]

def qmaZeroAncillaEquiv (c : QMACircuit) (hc : c.WellFormed) :
    {s : SourceSpinBasis (c.work+1) // QMAAncillaZero c s} ≃ SourceSpinBasis c.witness where
  toFun s := qmaWitnessRestrict c hc s.val
  invFun s := ⟨qmaWitnessExtend c s,qmaWitnessExtend_ancilla c s⟩
  left_inv s := Subtype.ext (qmaWitnessExtend_restrict c hc s.val s.property)
  right_inv := qmaWitnessRestrict_extend c hc

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative propagation for the actual H,T,CNOT circuit history. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb
open Matrix

def qmaHistoryGauge (c : QMACircuit)
    (u : ℕ → EuclideanSpace ℂ (SourceSpinBasis (c.work+1))) (t : ℕ) :
    EuclideanSpace ℂ (SourceSpinBasis (c.work+1)) :=
  qmaApplyMatrix (qmaPrefixMatrix c t).conjTranspose (u t)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumEndpoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The verifier acceptance probability is the exact endpoint projection
energy of its normalized zero-ancilla evolution. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators

def qmaInputVector (c : QMACircuit) (hc : c.WellFormed)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) :
    EuclideanSpace ℂ (SourceSpinBasis (c.work+1)) :=
  WithLp.toLp 2 (qmaInitialState c hc psi)

def qmaOutputVector (c : QMACircuit) (hc : c.WellFormed)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) :
    EuclideanSpace ℂ (SourceSpinBasis (c.work+1)) :=
  qmaApplyMatrix (qmaCircuitMatrix c) (qmaInputVector c hc psi)

def qmaRejectVector (c : QMACircuit) (hc : c.WellFormed)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) :
    EuclideanSpace ℂ (SourceSpinBasis (c.work+1)) :=
  qmaMask (fun s => s (Fin.last c.work) ≠ 1) (qmaOutputVector c hc psi)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumInputProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The legal initial subspace is exactly the zero-ancilla witness embedding. -/

noncomputable section
namespace ContinuumCoulomb

def qmaExtractWitness (c : QMACircuit)
    (u : EuclideanSpace ℂ (SourceSpinBasis (c.work+1))) :
    EuclideanSpace ℂ (SourceSpinBasis c.witness) :=
  WithLp.toLp 2 (fun s => u (qmaWitnessExtend c s))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A quantitative circuit-history promise gap, for all history vectors. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators

def qmaHistoryMass (c : QMACircuit)
    (u : ℕ → EuclideanSpace ℂ (SourceSpinBasis (c.work+1))) : ℝ :=
  ∑ t ∈ Finset.range (c.gates.length+1), ‖u t‖^2

def qmaInputPenalty (c : QMACircuit)
    (u : ℕ → EuclideanSpace ℂ (SourceSpinBasis (c.work+1))) : ℝ :=
  ‖qmaMask (fun s => ¬QMAAncillaZero c s) (u 0)‖^2

def qmaOutputPenalty (c : QMACircuit)
    (u : ℕ → EuclideanSpace ℂ (SourceSpinBasis (c.work+1))) : ℝ :=
  ‖qmaMask (fun s => s (Fin.last c.work) ≠ 1) (u c.gates.length)‖^2

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryWitness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit accepting histories and their exact mass and energy. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators

def qmaIdealHistory (c : QMACircuit) (hc : c.WellFormed)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness))
    (t : ℕ) : EuclideanSpace ℂ (SourceSpinBasis (c.work+1)) :=
  qmaApplyMatrix (qmaPrefixMatrix c t) (qmaInputVector c hc psi)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistorySpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalized finite-dimensional spectral bounds for the history matrix. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators

def qmaHistoryVector (c : QMACircuit)
    (u : ℕ → EuclideanSpace ℂ (SourceSpinBasis (c.work+1))) :
    EuclideanSpace ℂ (QMAHistoryBasis c) :=
  WithLp.toLp 2 (fun p => u p.1.val p.2)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumAncillaCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Replace the joint ancilla penalty by a sum of individual qubit penalties. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

def qmaAncillaCount (c : QMACircuit) (s : SourceSpinBasis (c.work+1)) : ℝ :=
  ∑ i : Fin (c.work+1), if c.witness ≤ i.val ∧ s i ≠ 0 then 1 else 0

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumUnaryClock
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unary clock states and the adjacent-pair characterization of validity. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

def qmaUnaryClock (N : ℕ) (t : Fin (N+1)) : SourceSpinBasis N :=
  fun i => if i.val < t.val then 1 else 0

theorem qmaUnaryClock_injective (N : ℕ) : Function.Injective (qmaUnaryClock N) := by
  intro s t h
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hst | hts
  · let i : Fin N := ⟨s.val,lt_of_lt_of_le hst (Nat.le_of_lt_succ t.isLt)⟩
    have hi := congrFun h i
    have hs : ¬i.val < s.val := by simp [i]
    have ht : i.val < t.val := hst
    simp [qmaUnaryClock,hs,ht] at hi
  · let i : Fin N := ⟨t.val,lt_of_lt_of_le hts (Nat.le_of_lt_succ s.isLt)⟩
    have hi := congrFun h i
    have hs : i.val < s.val := hts
    have ht : ¬i.val < t.val := by simp [i]
    simp [qmaUnaryClock,hs,ht] at hi

theorem qmaUnaryClock_antitone (N : ℕ) (t : Fin (N+1)) : Antitone (qmaUnaryClock N t) := by
  intro i j hij
  by_cases hi : i.val < t.val
  · by_cases hj : j.val < t.val <;> simp [qmaUnaryClock,hi,hj]
  · have hj : ¬j.val < t.val := by omega
    simp [qmaUnaryClock,hi,hj]

theorem qmaUnaryClock_of_antitone (N : ℕ) (s : SourceSpinBasis N) (hs : Antitone s) :
    ∃ t : Fin (N+1), qmaUnaryClock N t = s := by
  have hlow : IsLowerSet {i : Fin N | s i = 1} := by
    intro j i hij hj
    have h := hs hij
    change s j = 1 at hj
    rw [hj] at h
    have hb := (s i).isLt
    apply Fin.ext
    change (s i).val = 1
    change (1 : Fin 2).val ≤ (s i).val at h
    norm_num at h
    omega
  rcases hlow.eq_univ_or_Iio with hall | ⟨t,ht⟩
  · refine ⟨Fin.last N,?_⟩
    funext i
    have hi : s i = 1 := by
      have hm : i ∈ ({j : Fin N | s j = 1} : Set (Fin N)) := by rw [hall]; trivial
      exact hm
    simp [qmaUnaryClock,i.isLt,hi]
  · refine ⟨⟨t.val,Nat.lt_succ_of_lt t.isLt⟩,?_⟩
    funext i
    have hi : s i = 1 ↔ i < t := Set.ext_iff.mp ht i
    by_cases hit : i.val < t.val
    · have hsi : s i = 1 := hi.mpr hit
      simp [qmaUnaryClock,hit,hsi]
    · have hsi : s i ≠ 1 := fun h => hit (hi.mp h)
      have hz : s i = 0 := by
        apply Fin.ext
        have hb := (s i).isLt
        have hn : (s i).val ≠ 1 := fun h => hsi (Fin.ext h)
        change (s i).val = 0
        omega
      simp [qmaUnaryClock,hit,hz]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumUnaryPenalty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The adjacent 01 penalties separate all invalid unary clock states. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

def qmaClockFaultCount : (N : ℕ) → SourceSpinBasis N → ℝ
  | 0, _ => 0
  | n+1, s => ∑ i : Fin n, if s i.castSucc = 0 ∧ s i.succ = 1 then 1 else 0

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPinnedClock
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
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

def qmaHistoryClock (T : ℕ) (t : Fin (T+1)) : SourceSpinBasis (T+2) :=
  qmaUnaryClock (T+2) ⟨t.val+1,by omega⟩

theorem qmaHistoryClock_injective (T : ℕ) : Function.Injective (qmaHistoryClock T) := by
  intro s t h
  have he := qmaUnaryClock_injective (T+2) h
  apply Fin.ext
  have hv := congrArg Fin.val he
  simpa using hv

theorem qmaHistoryClock_legal (T : ℕ) (t : Fin (T+1)) :
    QMALegalClock T (qmaHistoryClock T t) := by
  refine ⟨qmaUnaryClock_antitone _ _,?_,?_⟩
  · simp [qmaHistoryClock,qmaUnaryClock]
  · have ht : ¬T+1 < t.val+1 := by omega
    simpa [qmaHistoryClock,qmaUnaryClock] using ht

theorem qmaHistoryClock_of_legal (T : ℕ) (s : SourceSpinBasis (T+2))
    (hs : QMALegalClock T s) : ∃ t : Fin (T+1), qmaHistoryClock T t = s := by
  obtain ⟨k,hk⟩ := qmaUnaryClock_of_antitone (T+2) s hs.1
  have hl := hs.2.1
  have hr := hs.2.2
  rw [←hk] at hl hr
  have hk0 : 0 < k.val := by
    by_contra hn
    have hz : k.val = 0 := by omega
    simp [qmaUnaryClock,hz] at hl
  have hk1 : k.val ≤ T+1 := by
    by_contra hn
    have ht : T+1 < k.val := by omega
    simp [qmaUnaryClock,ht] at hr
  refine ⟨⟨k.val-1,by omega⟩,?_⟩
  unfold qmaHistoryClock
  have he : (⟨k.val-1+1,by omega⟩ : Fin (T+2+1)) = k := by
    apply Fin.ext
    change k.val-1+1 = k.val
    omega
  rw [he]
  exact hk

def qmaPinnedClockPenalty (T : ℕ) (s : SourceSpinBasis (T+2)) : ℝ :=
  qmaClockFaultCount (T+2) s+
    (if s 0 = 1 then 0 else 1)+(if s (Fin.last (T+1)) = 0 then 0 else 1)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumClockSector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The valid clock sector is exactly the finite circuit clock, with its
full complement retained in the norm decomposition. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

def qmaHistoryClockEquiv (T : ℕ) :
    Fin (T+1) ≃ {s : SourceSpinBasis (T+2) // QMALegalClock T s} :=
  Equiv.ofBijective (fun t => ⟨qmaHistoryClock T t,qmaHistoryClock_legal T t⟩) (by
    constructor
    · intro s t h
      exact qmaHistoryClock_injective T (congrArg Subtype.val h)
    · intro s
      obtain ⟨t,ht⟩ := qmaHistoryClock_of_legal T s.val s.property
      exact ⟨t,Subtype.ext ht⟩)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumLocalCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The small support matrix is recovered canonically by fixing every
spectator qubit to zero, preserving real entries and Hermiticity. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def qmaLocalCore (S : Finset ι) (A : Matrix (ι → Fin 2) (ι → Fin 2) ℂ) :
    Matrix (QMASupportBasis S) (QMASupportBasis S) ℂ :=
  A.submatrix (qmaSupportExtend S) (qmaSupportExtend S)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QubitMediatorMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

attribute [default_instance 200] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

namespace OAI

/-! The literal parallel mediator Hamiltonian and its exact first three
vacuum-compressed terms. Single flips have zero third-order compression. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical
variable {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ]

def qmaMediatorFlips (V : κ → Matrix σ σ ℂ) :
    Matrix (σ × (κ → Fin 2)) (σ × (κ → Fin 2)) ℂ :=
  ∑ e, V e ⊗ₖ qmaBitFlipMatrix e

def qmaMediatorPerturbation (C : Matrix σ σ ℂ) (D V : κ → Matrix σ σ ℂ) :
    Matrix (σ × (κ → Fin 2)) (σ × (κ → Fin 2)) ℂ :=
  C ⊗ₖ 1 + qmaMediatorOccupations D + qmaMediatorFlips V

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed four-spin coordinates for the exchange-only encoding. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaFourExchangeRational (i j : Fin 4) : Matrix (Fin 16) (Fin 16) ℚ :=
  fun s t => 2*(if qmaFourIndex (sourceSpinSwap i j (qmaFourBits s)) = t then 1 else 0)-
    (if s = t then 1 else 0)

def qmaFourExchange (i j : Fin 4) : Matrix (Fin 16) (Fin 16) ℂ :=
  fun s t => qmaFourExchangeRational i j s t

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourGapCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A rational positive factorization of the four-spin penalty above the
singlet projection. Each fixed row is checked separately at default limits. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaFourPenaltyRational : Matrix (Fin 16) (Fin 16) ℚ :=
  qmaFourExchangeRational 0 1+qmaFourExchangeRational 0 2+qmaFourExchangeRational 0 3+
    qmaFourExchangeRational 1 2+qmaFourExchangeRational 1 3+qmaFourExchangeRational 2 3+(6:ℚ) • (1 : Matrix (Fin 16) (Fin 16) ℚ)

def qmaFourGapRational : Matrix (Fin 16) (Fin 16) ℚ :=
  qmaFourPenaltyRational-(4:ℚ) • (1-qmaFourProjectionRational)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourPositive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The checked rational certificate is nonnegative on all complex states. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaFourPenalty : Matrix (Fin 16) (Fin 16) ℂ := qmaFourPenaltyRational.map (Rat.castHom ℂ)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourSpin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical single-spin actions on the four-spin encoding. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaFourSpinIndex (i : Fin 4) (μ : Fin 3) (s : Fin 16) : Fin 16 :=
  qmaFourIndex (Function.update (qmaFourBits s) i (qmaPauliBit μ (qmaFourBits s i)))

def qmaFourSpinRational (i : Fin 4) (μ : Fin 3) : Matrix (Fin 16) (Fin 16) ℚ :=
  fun s t => qmaPhysicalPauliSign μ (qmaFourBits s i)*
    (if qmaFourSpinIndex i μ s = t then 1 else 0)

def qmaFourSpin (i : Fin 4) (μ : Fin 3) : Matrix (Fin 16) (Fin 16) ℂ :=
  qmaPauliPhase μ • (qmaFourSpinRational i μ).map (Rat.castHom ℂ)

def qmaFourSpinRawAction (i : Fin 4) (μ : Fin 3) : Matrix (Fin 16) (Fin 2) ℚ :=
  fun s b => qmaPhysicalPauliSign μ (qmaFourBits s i)*qmaFourRawEncoding (qmaFourSpinIndex i μ s) b

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumTensorSucc
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Splitting off the first physical block in a finite tensor Hamiltonian. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical ComplexOrder
variable {σ τ : Type*} {n : ℕ}

variable [Fintype σ] [DecidableEq σ]

def qmaTensorPenalty (n : ℕ) (H : Matrix σ σ ℂ) :
    Matrix (Fin n → σ) (Fin n → σ) ℂ := ∑ i : Fin n, qmaSiteMatrix i H

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourTensorGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual many-block four-spin penalty has a uniform full-complement gap. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical ComplexOrder

def qmaFourTensorEncoding (n : ℕ) : Matrix (Fin n → Fin 16) (Fin n → Fin 2) ℂ :=
  qmaTensorMatrix (fun _ => qmaFourEncoding)

def qmaFourTensorProjection (n : ℕ) : Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ :=
  qmaTensorMatrix (fun _ => qmaFourProjection)

def qmaFourTensorPenalty (n : ℕ) : Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ :=
  qmaTensorPenalty n qmaFourPenalty

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourTensorCross
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual inter-block Heisenberg columns in the many-block four-spin code. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {n : ℕ}

def qmaFourTensorPairColumn (i j : Fin n) (p q : Fin 4) (μ : Fin 3) :
    Matrix (Fin n → Fin 16) (Fin n → Fin 2) ℂ :=
  qmaTensorMatrix (fun k => if k = i then qmaFourSpin p μ*qmaFourEncoding
    else if k = j then qmaFourSpin q μ*qmaFourEncoding else qmaFourEncoding)

def qmaFourTensorCross (i j : Fin n) (p q : Fin 4) :
    Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ :=
  ∑ μ : Fin 3, qmaSiteMatrix i (qmaFourSpin p μ)*qmaSiteMatrix j (qmaFourSpin q μ)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourFields
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Logical X and Z fields are realized by internal physical exchanges. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaFourField (x z : ℝ) : Matrix (Fin 16) (Fin 16) ℂ :=
  ((x/(2*Real.sqrt 3):ℝ):ℂ) • (qmaFourExchange 0 3-qmaFourExchange 0 2)-
    ((z/2:ℝ):ℂ) • qmaFourExchange 0 1

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourAxis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A common interface for the fixed X and Z exchange encodings. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaFourAxisField (a : Fin 2) (t : ℝ) : Matrix (Fin 16) (Fin 16) ℂ :=
  if a = 0 then qmaFourField t 0 else qmaFourField 0 t

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourTensorWeighted
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Factorized Heisenberg couplings in the full many-block tensor code. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {n : ℕ}

def qmaFourTensorWeighted (i j : Fin n) (a b : Fin 4 → ℝ) :
    Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ :=
  ∑ p, ∑ q, ((a p*b q:ℝ):ℂ) • qmaFourTensorCross i j p q

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourTensorEffective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical counterterms calibrate each edge of the full tensor simulator. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {n : ℕ}

def qmaFourTensorCoupling (i j : Fin n) (a b : Fin 2) (t : ℝ) :
    Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ :=
  (qmaFourCouplingSize a b t:ℂ) • qmaFourTensorWeighted i j
    (qmaFourAxisWeights a true) (qmaFourAxisWeights b (qmaFourCouplingSign t))

def qmaFourTensorEffective (i j : Fin n) (a b : Fin 2) (t : ℝ) :
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  (-1/8:ℂ) • ((qmaFourTensorCoupling i j a b t*qmaFourTensorEncoding n).conjTranspose*
    (qmaFourTensorCoupling i j a b t*qmaFourTensorEncoding n))

def qmaFourTensorCounterterm (i j : Fin n) (a b : Fin 2) (t : ℝ) :
    Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ :=
  qmaSiteMatrix i (qmaFourAxisField a (qmaFourCounterA a b t))+
    qmaSiteMatrix j (qmaFourAxisField b (qmaFourCounterB a b t))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourTensorFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact effective Hamiltonian of a family of distinct logical edges. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

variable {σ τ κ : Type*} [Fintype σ] [Fintype τ] [Fintype κ] [DecidableEq κ]

variable {n : ℕ}

def qmaFourTensorFamilyCoupling (left right : κ → Fin n) (a b : κ → Fin 2) (t : κ → ℝ) :
    Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ :=
  ∑ e, qmaFourTensorCoupling (left e) (right e) (a e) (b e) (t e)

def qmaFourTensorFamilyCounterterm (left right : κ → Fin n) (a b : κ → Fin 2) (t : κ → ℝ) :
    Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ :=
  ∑ e, qmaFourTensorCounterterm (left e) (right e) (a e) (b e) (t e)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QubitMediatorPenalty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An invertible diagonal extension of the physical excitation penalty.
The extension agrees with the physical penalty on the actual complement. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators InnerProductSpace Classical
variable {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ]

def qmaPaddedPenalty (g : ℝ) : EuclideanSpace ℂ (σ × (κ → Fin 2)) →L[ℝ]
    EuclideanSpace ℂ (σ × (κ → Fin 2)) := diagonalPenalty (qmaPaddedWeight g)

def qmaPaddedInverse (g : ℝ) : EuclideanSpace ℂ (σ × (κ → Fin 2)) →L[ℝ]
    EuclideanSpace ℂ (σ × (κ → Fin 2)) := diagonalPenalty (fun p => (qmaPaddedWeight g p)⁻¹)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QubitMediatorHilbert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual Hilbert-space low and complementary coordinates for qubit mediators. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators InnerProductSpace Classical
variable {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ]

def qmaMediatorHighProjection : EuclideanSpace ℂ (σ × (κ → Fin 2)) →L[ℝ]
    EuclideanSpace ℂ (σ × (κ → Fin 2)) :=
  (spinMatrixOperator qmaMediatorHighMatrix).restrictScalars ℝ

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QubitMediatorPhysical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The physical parallel-qubit Hamiltonian has the calculated vacuum column. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical
variable {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ]

def qmaPhysicalMediatorMatrix (g : ℝ) (C : Matrix σ σ ℂ) (D V : κ → Matrix σ σ ℂ) :
    Matrix (σ × (κ → Fin 2)) (σ × (κ → Fin 2)) ℂ :=
  qmaPhysicalPenaltyMatrix g+qmaMediatorPerturbation C D V

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QubitMediatorForms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full physical energy equals the block energy on its genuine
vacuum/complement decomposition. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators InnerProductSpace Classical
variable {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ]

def qmaPhysicalOperator (g : ℝ) (C : Matrix σ σ ℂ) (D V : κ → Matrix σ σ ℂ) :
    EuclideanSpace ℂ (σ × (κ → Fin 2)) →L[ℝ] EuclideanSpace ℂ (σ × (κ → Fin 2)) :=
  (qmaMatrixOperator (qmaPhysicalMediatorMatrix g C D V)).restrictScalars ℝ

def qmaPerturbationOperator (C : Matrix σ σ ℂ) (D V : κ → Matrix σ σ ℂ) :
    EuclideanSpace ℂ (σ × (κ → Fin 2)) →L[ℝ] EuclideanSpace ℂ (σ × (κ → Fin 2)) :=
  (qmaMatrixOperator (qmaMediatorPerturbation C D V)).restrictScalars ℝ

def qmaComplementOperator (C : Matrix σ σ ℂ) (D V : κ → Matrix σ σ ℂ) :
    EuclideanSpace ℂ (σ × (κ → Fin 2)) →L[ℝ] EuclideanSpace ℂ (σ × (κ → Fin 2)) :=
  qmaMediatorHighProjection.comp ((qmaPerturbationOperator C D V).comp qmaMediatorHighProjection)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourTensorHilbert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual low/high coordinates and the bounded padded inverse for the four-spin code. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators InnerProductSpace Classical ComplexOrder

def qmaFourTensorInclusion (n : ℕ) :
    EuclideanSpace ℂ (Fin n → Fin 2) →L[ℝ] EuclideanSpace ℂ (Fin n → Fin 16) :=
  (qmaMatrixOperator (qmaFourTensorEncoding n)).restrictScalars ℝ

def qmaFourTensorRestriction (n : ℕ) :
    EuclideanSpace ℂ (Fin n → Fin 16) →L[ℝ] EuclideanSpace ℂ (Fin n → Fin 2) :=
  (qmaMatrixOperator (qmaFourTensorEncoding n).conjTranspose).restrictScalars ℝ

def qmaFourTensorHigh (n : ℕ) :
    EuclideanSpace ℂ (Fin n → Fin 16) →L[ℝ] EuclideanSpace ℂ (Fin n → Fin 16) :=
  (qmaMatrixOperator (1-qmaFourTensorProjection n)).restrictScalars ℝ

def qmaFourTensorPaddedMatrix (n : ℕ) : Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ :=
  qmaFourTensorPenalty n+(4:ℂ) • qmaFourTensorProjection n

def qmaFourTensorPadded (n : ℕ) (r : ℝ) :
    EuclideanSpace ℂ (Fin n → Fin 16) →L[ℝ] EuclideanSpace ℂ (Fin n → Fin 16) :=
  r^2 • (qmaMatrixOperator (qmaFourTensorPaddedMatrix n)).restrictScalars ℝ

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourTensorForms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full physical quadratic form in its actual encoded and orthogonal coordinates. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators InnerProductSpace Classical
variable {n : ℕ}

def qmaFourTensorPhysical (r : ℝ)
    (K : EuclideanSpace ℂ (Fin n → Fin 16) →L[ℝ] EuclideanSpace ℂ (Fin n → Fin 16)) :=
  r^2 • (qmaMatrixOperator (qmaFourTensorPenalty n)).restrictScalars ℝ+K

def qmaFourTensorLow
    (K : EuclideanSpace ℂ (Fin n → Fin 16) →L[ℝ] EuclideanSpace ℂ (Fin n → Fin 16)) :=
  (qmaFourTensorRestriction n).comp (K.comp (qmaFourTensorInclusion n))

def qmaFourTensorOff
    (K : EuclideanSpace ℂ (Fin n → Fin 16) →L[ℝ] EuclideanSpace ℂ (Fin n → Fin 16)) :=
  (qmaFourTensorHigh n).comp (K.comp (qmaFourTensorInclusion n))

def qmaFourTensorHighPerturbation
    (K : EuclideanSpace ℂ (Fin n → Fin 16) →L[ℝ] EuclideanSpace ℂ (Fin n → Fin 16)) :=
  (qmaFourTensorHigh n).comp (K.comp (qmaFourTensorHigh n))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourTensorEffectiveError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual effective form approximates the calibrated tensor matrix. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators InnerProductSpace Classical
variable {n : ℕ}

def qmaFourTensorEffectiveMatrix (V C : Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ) :=
  (qmaFourTensorEncoding n).conjTranspose*C*qmaFourTensorEncoding n-
    (1/8:ℂ) • ((V*qmaFourTensorEncoding n).conjTranspose*(V*qmaFourTensorEncoding n))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourTensorGround
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full physical ground-energy comparison for the four-spin tensor simulator. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators InnerProductSpace Classical
variable {n : ℕ}

def qmaFourTensorPhysicalMatrix (r : ℝ) (U : Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ) :=
  (r^2:ℂ) • qmaFourTensorPenalty n+U

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourTensorOperatorBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial norm budget for the exact calibrated effective matrix. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped InnerProductSpace Classical
variable {n : ℕ}

def qmaFourTensorNormBudget (V C : Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ) : ℝ :=
  1+‖spinMatrixOperator V‖+‖spinMatrixOperator C‖+‖spinMatrixOperator V‖^2

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourTensorFamilyAccuracy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A polynomial-precision simulator for an arbitrary family of distinct X/Z pairs. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators InnerProductSpace Classical
variable {n : ℕ} {κ : Type*} [Fintype κ]

def qmaFourTensorFamilyTarget (left right : κ → Fin n) (a b : κ → Fin 2) (t : κ → ℝ) :=
  (∑ e, (t e:ℂ) • qmaPairMatrix (left e) (right e) (qmaFourAxis (a e)) (qmaFourAxis (b e)))+
    ((∑ e, qmaFourEnergyOffset (a e) (b e) (t e):ℝ):ℂ) •
      (1 : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourTensorOnsite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Internal physical exchanges encode the one-site and scalar X/Z terms. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {n : ℕ} {τ : Type*} [Fintype τ]

def qmaFourTensorFields (site : τ → Fin n) (axis : τ → Fin 2) (weight : τ → ℝ) :
    Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ :=
  ∑ e, qmaSiteMatrix (site e) (qmaFourAxisField (axis e) (weight e))

def qmaFourTensorOnsite (site : τ → Fin n) (axis : τ → Fin 2) (weight : τ → ℝ) (constant : ℝ) :
    Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ :=
  qmaFourTensorFields site axis weight+((constant-qmaFourTensorFieldShift axis weight:ℝ):ℂ) • 1

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourTensorFullFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full X/Z families, including scalar and one-site terms, have polynomial simulators. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {n : ℕ} {κ τ : Type*} [Fintype κ] [Fintype τ]

def qmaFourTensorFullCounterterm (left right : κ → Fin n) (a b : κ → Fin 2) (t : κ → ℝ)
    (site : τ → Fin n) (axis : τ → Fin 2) (weight : τ → ℝ) (constant : ℝ) :=
  qmaFourTensorFamilyCounterterm left right a b t+qmaFourTensorOnsite site axis weight constant

def qmaFourTensorFullTarget (left right : κ → Fin n) (a b : κ → Fin 2) (t : κ → ℝ)
    (site : τ → Fin n) (axis : τ → Fin 2) (weight : τ → ℝ) (constant : ℝ) :=
  qmaFourTensorFamilyTarget left right a b t+
    ((∑ e, (weight e:ℂ) • qmaSiteMatrix (site e) (qmaFourAxis (axis e)))+(constant:ℂ) • 1)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumBlockBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The tensor code's physical coordinates are exactly ordinary groups of four qubits. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaBlockBasisEquiv (n : ℕ) : SourceSpinBasis (n*4) ≃ (Fin n → Fin 16) where
  toFun s i := qmaFourBasisEquiv (fun p => s (finProdFinEquiv (i,p)))
  invFun x k := qmaFourBasisEquiv.symm (x (finProdFinEquiv.symm k).1) (finProdFinEquiv.symm k).2
  left_inv s := by
    funext k
    obtain ⟨⟨i,p⟩,rfl⟩ := finProdFinEquiv.surjective k
    simp only [Equiv.symm_apply_apply]
  right_inv x := by
    funext i
    simp only [Equiv.symm_apply_apply,Equiv.apply_symm_apply]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumBlockHamiltonian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal exchange sums for the real-coefficient four-spin Hamiltonian. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {n : ℕ}

def qmaBlockSourcePenalty (n : ℕ) : Matrix (SourceSpinBasis (n*4)) (SourceSpinBasis (n*4)) ℂ :=
  (∑ i : Fin n, ∑ e : Fin 6, sourceHeisenbergMatrix (n*4)
    (finProdFinEquiv (i,qmaFourEdgeLeft e)) (finProdFinEquiv (i,qmaFourEdgeRight e)))+
      ((n:ℂ)*6) • 1

def qmaBlockSourceField (i : Fin n) (x z : ℝ) :
    Matrix (SourceSpinBasis (n*4)) (SourceSpinBasis (n*4)) ℂ :=
  ((x/(2*Real.sqrt 3):ℝ):ℂ) •
    (sourceHeisenbergMatrix (n*4) (finProdFinEquiv (i,0)) (finProdFinEquiv (i,3))-
      sourceHeisenbergMatrix (n*4) (finProdFinEquiv (i,0)) (finProdFinEquiv (i,2)))-
    ((z/2:ℝ):ℂ) • sourceHeisenbergMatrix (n*4) (finProdFinEquiv (i,0)) (finProdFinEquiv (i,1))

def qmaBlockSourceAxisField (i : Fin n) (a : Fin 2) (t : ℝ) :
    Matrix (SourceSpinBasis (n*4)) (SourceSpinBasis (n*4)) ℂ :=
  if a = 0 then qmaBlockSourceField i t 0 else qmaBlockSourceField i 0 t

def qmaBlockSourceCoupling (i j : Fin n) (a b : Fin 2) (t : ℝ) :
    Matrix (SourceSpinBasis (n*4)) (SourceSpinBasis (n*4)) ℂ :=
  (qmaFourCouplingSize a b t:ℂ) •
    ∑ p : Fin 4, ∑ q : Fin 4,
      ((qmaFourAxisWeights a true p*qmaFourAxisWeights b (qmaFourCouplingSign t) q:ℝ):ℂ) •
        sourceHeisenbergMatrix (n*4) (finProdFinEquiv (i,p)) (finProdFinEquiv (j,q))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumBlockFull
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full physical simulator as a sum of ordinary Heisenberg exchanges. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {n : ℕ} {κ τ : Type*} [Fintype κ] [Fintype τ]

def qmaBlockSourceCounterterm (i j : Fin n) (a b : Fin 2) (t : ℝ) :
    Matrix (SourceSpinBasis (n*4)) (SourceSpinBasis (n*4)) ℂ :=
  qmaBlockSourceAxisField i a (qmaFourCounterA a b t)+
    qmaBlockSourceAxisField j b (qmaFourCounterB a b t)

def qmaBlockSourceOnsite (site : τ → Fin n) (axis : τ → Fin 2) (weight : τ → ℝ) (constant : ℝ) :
    Matrix (SourceSpinBasis (n*4)) (SourceSpinBasis (n*4)) ℂ :=
  (∑ e, qmaBlockSourceAxisField (site e) (axis e) (weight e))+
    ((constant-qmaFourTensorFieldShift axis weight:ℝ):ℂ) • 1

def qmaBlockSourceFull (r : ℝ) (left right : κ → Fin n) (a b : κ → Fin 2) (t : κ → ℝ)
    (site : τ → Fin n) (axis : τ → Fin 2) (weight : τ → ℝ) (constant : ℝ) :
    Matrix (SourceSpinBasis (n*4)) (SourceSpinBasis (n*4)) ℂ :=
  ((r^2:ℝ):ℂ) • qmaBlockSourcePenalty n+
    (r:ℂ) • (∑ e, qmaBlockSourceCoupling (left e) (right e) (a e) (b e) (t e))+
    (∑ e, qmaBlockSourceCounterterm (left e) (right e) (a e) (b e) (t e))+
    qmaBlockSourceOnsite site axis weight constant

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

def qmaFourExchangeWeight (r : ℝ) (a b : κ → Fin 2) (t : κ → ℝ)
    (axis : τ → Fin 2) (weight : τ → ℝ) : QMAFourExchangeIndex n κ τ → ℝ
  | .inl _ => r^2
  | .inr (.inl (e,p,q)) => r*qmaFourCouplingSize (a e) (b e) (t e)*
      (qmaFourAxisWeights (a e) true p*qmaFourAxisWeights (b e) (qmaFourCouplingSign (t e)) q)
  | .inr (.inr (.inl (e,s,k))) => if s = 0 then
      qmaFieldEdgeWeight (a e) (qmaFourCounterA (a e) (b e) (t e)) k else
      qmaFieldEdgeWeight (b e) (qmaFourCounterB (a e) (b e) (t e)) k
  | .inr (.inr (.inr (e,k))) => qmaFieldEdgeWeight (axis e) (weight e) k

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QubitPhase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A diagonal unitary rotates any chosen mediator X couplings to Y. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

def qmaPolarizedFlip (m : κ → Bool) (e : κ) : Matrix (κ → Fin 2) (κ → Fin 2) ℂ :=
  fun a b => if a = qmaBitFlip e b then
    (if m e = true then (if b e = 1 then -Complex.I else Complex.I) else 1) else 0

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QubitPhasePhysical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Independent mediator phase rotations preserve the full physical spectrum. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical
variable {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ]

def qmaPolarizedPhysical (g : ℝ) (L : Matrix σ σ ℂ) (D V : κ → Matrix σ σ ℂ)
    (m : κ → Bool) : Matrix (σ × (κ → Fin 2)) (σ × (κ → Fin 2)) ℂ :=
  qmaPhysicalPenaltyMatrix g+(L ⊗ₖ (1 : Matrix (κ → Fin 2) (κ → Fin 2) ℂ)+
    qmaMediatorOccupations D+∑ e, V e ⊗ₖ qmaPolarizedFlip m e)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QubitMediatorTrial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The third-order trial vector lies in the genuine physical spin space. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators InnerProductSpace Classical
variable {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ]

def qmaThirdTrial (g : ℝ) (V : κ → Matrix σ σ ℂ) (p : EuclideanSpace ℂ σ) :
    EuclideanSpace ℂ (σ × (κ → Fin 2)) :=
  qmaMediatorInclusion p+(-(qmaPaddedInverse g (qmaCouplingOperator V p)))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QubitThirdGadget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit parallel third-order gadget with a polynomial accuracy scale. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators InnerProductSpace Classical
variable {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ]

def qmaThirdGadget (H : Matrix σ σ ℂ) (A B C : κ → Matrix σ σ ℂ)
    (R : ℝ) (J : κ → ℝ) : Matrix (σ × (κ → Fin 2)) (σ × (κ → Fin 2)) ℂ :=
  qmaPhysicalMediatorMatrix (R^3) (qmaThirdSeriesLow H A B C R (fun e => J e))
    (fun e => (R^2:ℝ) • C e)
    (fun e => (R^2:ℝ) • qmaThirdSeriesPair (A e) (B e) (J e))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QubitSubdivisionMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The simultaneous subdivision gadget has only a scalar counterterm.
Its exact third-order compression retains the common low-block residual. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ]

def qmaSubdivisionGadget (H : Matrix σ σ ℂ) (A B : κ → Matrix σ σ ℂ)
    (R : ℝ) (J : κ → ℝ) : Matrix (σ × (κ → Fin 2)) (σ × (κ → Fin 2)) ℂ :=
  qmaPhysicalMediatorMatrix (R^2) (qmaSubdivisionLow H (fun e => J e)) (fun _ => 0)
    (fun e => (R:ℝ) • qmaThirdSeriesPair (A e) (B e) (-J e))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QubitSubdivisionDecomposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An exact four-term output family for a phase-rotated subdivision gadget. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical
variable {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ]

def qmaSubdivisionPolarized (H : Matrix σ σ ℂ) (A B : κ → Matrix σ σ ℂ)
    (R : ℝ) (J : κ → ℝ) (m : κ → Bool) :
    Matrix (σ × (κ → Fin 2)) (σ × (κ → Fin 2)) ℂ :=
  qmaPolarizedPhysical (R^2) (qmaSubdivisionLow H (fun e => J e)) (fun _ => 0)
    (fun e => (R:ℝ) • qmaThirdSeriesPair (A e) (B e) (-J e)) m

def qmaSubdivisionPiece (A B : Matrix σ σ ℂ) (e : κ) (R j : ℝ) (m : κ → Bool) :
    Fin 4 → Matrix (σ × (κ → Fin 2)) (σ × (κ → Fin 2)) ℂ :=
  ![(R^2:ℝ) • ((1 : Matrix σ σ ℂ) ⊗ₖ qmaAncillaOccupation e),
    (1+(j/2)^2:ℝ) • (1 : Matrix (σ × (κ → Fin 2)) (σ × (κ → Fin 2)) ℂ),
    (R:ℝ) • (A ⊗ₖ qmaPolarizedFlip m e),
    (-R*j/2:ℝ) • (B ⊗ₖ qmaPolarizedFlip m e)]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QubitSubdivisionLocalFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Subdivision increases each factor's support by at most its one fresh mediator. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical
variable {ι κ α : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [Fintype α]

def qmaSubdivisionLocalPiece (A B : Matrix (ι → Fin 2) (ι → Fin 2) ℂ)
    (e : κ) (R j : ℝ) (m : κ → Bool) :
    Fin 4 → Matrix (ι ⊕ κ → Fin 2) (ι ⊕ κ → Fin 2) ℂ :=
  ![(R^2:ℝ) • qmaJoinMatrix (1 : Matrix (ι → Fin 2) (ι → Fin 2) ℂ) (qmaAncillaOccupation e),
    (1+(j/2)^2:ℝ) • (1 : Matrix (ι ⊕ κ → Fin 2) (ι ⊕ κ → Fin 2) ℂ),
    (R:ℝ) • qmaJoinMatrix A (qmaPolarizedFlip m e),
    (-R*j/2:ℝ) • qmaJoinMatrix B (qmaPolarizedFlip m e)]

def qmaSubdivisionOnQubits (H : Matrix (ι → Fin 2) (ι → Fin 2) ℂ)
    (A B : κ → Matrix (ι → Fin 2) (ι → Fin 2) ℂ) (R : ℝ) (J : κ → ℝ) (m : κ → Bool) :
    Matrix (ι ⊕ κ → Fin 2) (ι ⊕ κ → Fin 2) ℂ :=
  (qmaSubdivisionPolarized H A B R J m).submatrix (Equiv.sumArrowEquivProdArrow ι κ (Fin 2))
    (Equiv.sumArrowEquivProdArrow ι κ (Fin 2))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QubitThirdPhased
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The third-order family with the real-preserving mediator phases. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical
variable {σ ι κ : Type*} [Fintype σ] [DecidableEq σ]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def qmaThirdPhasedPiece (A B C : Matrix σ σ ℂ) (e : κ) (R j : ℝ) (m : κ → Bool) :
    Fin 7 → Matrix (σ × (κ → Fin 2)) (σ × (κ → Fin 2)) ℂ :=
  ![(R^3:ℝ) • ((1 : Matrix σ σ ℂ) ⊗ₖ qmaAncillaOccupation e),
    (R*(1+(j/2)^2):ℝ) • (1 : Matrix (σ × (κ → Fin 2)) (σ × (κ → Fin 2)) ℂ),
    (R*j:ℝ) • ((A*B) ⊗ₖ (1 : Matrix (κ → Fin 2) (κ → Fin 2) ℂ)),
    (-(1+(j/2)^2):ℝ) • (C ⊗ₖ (1 : Matrix (κ → Fin 2) (κ → Fin 2) ℂ)),
    (R^2:ℝ) • (C ⊗ₖ qmaAncillaOccupation e),
    (R^2:ℝ) • (A ⊗ₖ qmaPolarizedFlip m e),
    (R^2*j/2:ℝ) • (B ⊗ₖ qmaPolarizedFlip m e)]

def qmaThirdPhased (H : Matrix σ σ ℂ) (A B C : κ → Matrix σ σ ℂ)
    (R : ℝ) (J : κ → ℝ) (m : κ → Bool) :
    Matrix (σ × (κ → Fin 2)) (σ × (κ → Fin 2)) ℂ :=
  qmaPolarizedPhysical (R^3) (qmaThirdSeriesLow H A B C R (fun e => J e))
    (fun e => (R^2:ℝ) • C e) (fun e => (R^2:ℝ) • qmaThirdSeriesPair (A e) (B e) (J e)) m

def qmaThirdPhasedLocalPiece (A B C : Matrix (ι → Fin 2) (ι → Fin 2) ℂ)
    (e : κ) (R j : ℝ) (m : κ → Bool) (k : Fin 7) :
    Matrix (ι ⊕ κ → Fin 2) (ι ⊕ κ → Fin 2) ℂ :=
  (qmaThirdPhasedPiece A B C e R j m k).submatrix
    (Equiv.sumArrowEquivProdArrow ι κ (Fin 2)) (Equiv.sumArrowEquivProdArrow ι κ (Fin 2))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumXZFamilySplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual word family splits into the three kinds of physical simulator terms. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

variable {n : ℕ} {κ : Type*} [Fintype κ]

def qmaXZFamilyConstant (t : κ → QMAXZTerm n) (J : κ → ℝ) : ℝ :=
  (∑ e : QMAXZScalarIndex t, J e.val)-
    ∑ e : QMAXZPairIndex t, qmaFourEnergyOffset
      (qmaXZPairData t e).axisLeft (qmaXZPairData t e).axisRight (J e.val)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumXZHeisenberg
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full X/Z family is simulated in the ordinary physical qubit space. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {n : ℕ} {κ : Type*} [Fintype κ]

def qmaXZBlockBudget (t : κ → QMAXZTerm n) (J : κ → ℝ) : ℝ :=
  qmaFourTensorFullBudget (fun e : QMAXZPairIndex t => J e.val)
    (fun e : QMAXZFieldIndex t => J e.val) (qmaXZFamilyConstant t J)

def qmaXZBlockSource (r : ℝ) (t : κ → QMAXZTerm n) (J : κ → ℝ) :
    Matrix (SourceSpinBasis (n*4)) (SourceSpinBasis (n*4)) ℂ :=
  qmaBlockSourceFull r
    (fun e => (qmaXZPairData t e).left) (fun e => (qmaXZPairData t e).right)
    (fun e => (qmaXZPairData t e).axisLeft) (fun e => (qmaXZPairData t e).axisRight)
    (fun e => J e.val)
    (fun e => (qmaXZFieldData t e).site) (fun e => (qmaXZFieldData t e).axis)
    (fun e => J e.val) (qmaXZFamilyConstant t J)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumBlockBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A rationally evaluable budget suffices for every physical simulator coefficient. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {n : ℕ} {κ : Type*} [Fintype κ]

def qmaXZPolynomialBudget (J : κ → ℝ) : ℝ :=
  1+2000000*qmaXZInputSize J+(7056*qmaXZInputSize J)^2

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSingletStar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted multi-terminal singlet stars for the lattice routing gadgets. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaPauliKernel (n : ℕ) (i j : Fin n) : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ :=
  ∑ μ : Fin 3, sourceLocalPauli n i μ*sourceLocalPauli n j μ

variable {κ : Type*} [Fintype κ]

def qmaSingletStar (n r : ℕ) (e : Fin r) (site : κ → Fin n)
    (member : κ → Fin 2) (amplitude : κ → ℝ) :
    Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ :=
  ∑ a, (amplitude a:ℂ) • mediatorAxisSpoke n r e (site a) (member a)

/-- All routing stars are applied simultaneously, one per distinct singlet pair. -/
def qmaRoutingStars (n r : ℕ) (site : Fin r → κ → Fin n)
    (member : Fin r → κ → Fin 2) (amplitude : Fin r → κ → ℝ) :
    Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ :=
  ∑ e, qmaSingletStar n r e (site e) (member e) (amplitude e)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCrossingEffective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact four-terminal crossing gadget and its perimeter counterterms. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaCrossingCorrection {n : ℕ} (site : Fin 4 → Fin n) (J K : ℝ) :
    Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ :=
  ((3/2+3*J^2+3*K^2:ℝ):ℂ) • 1 +
    (1/2:ℂ) • sourceHeisenbergMatrix n (site 0) (site 1) -
    (K:ℂ) • sourceHeisenbergMatrix n (site 0) (site 3) -
    (J:ℂ) • sourceHeisenbergMatrix n (site 1) (site 2) +
    ((2*J*K:ℝ):ℂ) • sourceHeisenbergMatrix n (site 2) (site 3)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumWireSwap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact three-CNOT transfers for a circuit whose active wires move through a grid. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaWirePermutation {n : ℕ} (f : SourceSpinBasis n → SourceSpinBasis n) :
    Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ := fun s t => if s = f t then 1 else 0

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumGateProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact sequential products for the circuit transformations used by the sparse history. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix

abbrev qmaGateProduct (work : ℕ) (gs : List QMAGate) :
    Matrix (SourceSpinBasis (work+1)) (SourceSpinBasis (work+1)) ℂ :=
  qmaCircuitMatrix ⟨work,0,gs⟩

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumWireRelabel
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact coordinate changes for gates and circuit products. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaWireBasis {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    SourceSpinBasis n ≃ SourceSpinBasis n where
  toFun s := s ∘ σ
  invFun s := s ∘ σ.symm
  left_inv s := by funext i; simp
  right_inv s := by funext i; simp

def qmaWireRelabelMatrix {n : ℕ} (σ : Equiv.Perm (Fin n))
    (M : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) :=
  M.submatrix (qmaWireBasis σ) (qmaWireBasis σ)

def qmaRelabelGate (work : ℕ) (σ : Equiv.Perm (Fin (work+1))) : QMAGate → QMAGate
  | .hadamard i => .hadamard (σ (qmaQubit work i)).val
  | .phaseT i => .phaseT (σ (qmaQubit work i)).val
  | .controlledNot i j =>
      .controlledNot (σ (qmaQubit work i)).val (σ (qmaQubit work j)).val

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRowTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Moving a complete register between two disjoint rows. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaRowPairs_distinct {n work : ℕ} (l r : Fin n → Fin (work+1))
    (hlr : ∀ i j, l i ≠ r j) : ∀ p ∈ qmaRowPairs l r, p.1 ≠ p.2 := by
  intro p hp
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
  exact hlr i i

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumWireGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete row-major physical qubits for the space-time wire construction. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaGridRow_injective (rows width : ℕ) (r : Fin (rows+1)) :
    Function.Injective (qmaGridQubit rows width r) := by
  intro i j h
  exact congrArg Prod.snd (qmaGridQubit_injective rows width (a₁ := (r,i)) (a₂ := (r,j)) h)

theorem qmaGridRows_disjoint (rows width : ℕ) (r s : Fin (rows+1)) (hrs : r ≠ s)
    (i j : Fin (width+1)) : qmaGridQubit rows width r i ≠ qmaGridQubit rows width s j := by
  intro h
  exact hrs (congrArg Prod.fst (qmaGridQubit_injective rows width (a₁ := (r,i)) (a₂ := (s,j)) h))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumGridFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cumulative row-transfer frame locates the active register exactly. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

def qmaGridFrame (rows width : ℕ) : (t : ℕ) → t ≤ rows →
    Equiv.Perm (Fin (qmaGridWork rows width+1))
  | 0,_ => Equiv.refl _
  | t+1,ht =>
      (qmaTransferPermutation (qmaRowPairs (qmaGridQubit rows width (⟨t,by omega⟩ : Fin (rows+1)))
        (qmaGridQubit rows width (⟨t+1,by omega⟩ : Fin (rows+1))))).trans
          (qmaGridFrame rows width t (by omega))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPaddedBasis
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Splitting the original register from fresh grid wires. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical

def qmaAppendBasis (n m : ℕ) : SourceSpinBasis (n+m) ≃ SourceSpinBasis n × SourceSpinBasis m where
  toFun s := (fun i => s (Fin.castAdd m i),fun j => s (Fin.natAdd n j))
  invFun p := Fin.addCases p.1 p.2
  left_inv s := by
    funext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · simp only [Fin.addCases_left]
    · simp only [Fin.addCases_right]
  right_inv p := by simp

def qmaPaddedBasis (work extra : ℕ) :
    SourceSpinBasis (work+extra+1) ≃ SourceSpinBasis (work+1) × SourceSpinBasis extra :=
  (Equiv.arrowCongr (qmaPaddedIndex work extra).symm (Equiv.refl (Fin 2))).trans
    (qmaAppendBasis (work+1) extra)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumReferenceWalls
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The nearest-neighbor reference chain has only two zero-wall sectors. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaReferenceWalls (n : ℕ) (s : SourceSpinBasis (n+1)) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => s i.castSucc ≠ s i.succ)).card

def qmaReferenceWallMatrix (n : ℕ) :
    Matrix (SourceSpinBasis (n+1)) (SourceSpinBasis (n+1)) ℂ :=
  Matrix.diagonal (fun s => (qmaReferenceWalls n s : ℂ))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumDiagonalTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact diagonal tensors and the computational-basis reference-chain penalty. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaReferenceZPenalty (n : ℕ) :
    Matrix (SourceSpinBasis (n+1)) (SourceSpinBasis (n+1)) ℂ :=
  ∑ i : Fin n, (1/2 : ℂ) • (1-sourceLocalPauli (n+1) i.castSucc 2*
    sourceLocalPauli (n+1) i.succ 2)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRoutingBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Low and high blocks for the finite singlet stars used in lattice routing. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker InnerProductSpace

def routingCoupling (n r : ℕ)
    (W : Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ) :
    MediatorLowSpace n →L[ℝ] MediatorHighSpace n r :=
  ((mediatorHighRestriction n r).comp
    ((spinMatrixOperator W).comp (mediatorLowInclusion n r))).restrictScalars ℝ

def routingHighBlock (n r : ℕ)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ)
    (W : Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ) :
    MediatorHighSpace n r →L[ℝ] MediatorHighSpace n r :=
  ((mediatorHighRestriction n r).comp
    ((spinMatrixOperator (C ⊗ₖ 1 + W)).comp
      (mediatorHighInclusion n r))).restrictScalars ℝ

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRoutingForms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact quadratic forms for the finite singlet routing gadgets. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker InnerProductSpace

/-- The actual full matrix in the complete Bell-coordinate spin space. -/
def routingHamiltonian (n r : ℕ) (Delta : ℝ)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ)
    (W : Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ) :
    Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ :=
  bellMediatorPenaltyMatrix n r Delta +
    (C ⊗ₖ 1 + W)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkEffective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational asymmetric fork gadget for reducing the degree of an old spin. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaForkCorrection {n : ℕ} (site : Fin 3 → Fin n) (J K : ℝ) :
    Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ :=
  ((3/4+3*J^2+3*K^2:ℝ):ℂ) • 1 +
    ((2*J*K:ℝ):ℂ) • sourceHeisenbergMatrix n (site 1) (site 2)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRoutingPhysical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual physical spin interactions for the singlet routing construction. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker InnerProductSpace
variable {κ : Type*} [Fintype κ]

def qmaPhysicalSingletStar (n r : ℕ) (e : Fin r) (site : κ → Fin n)
    (member : κ → Fin 2) (amplitude : κ → ℝ) :
    Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ :=
  ∑ a, (amplitude a:ℂ) • ∑ μ : Fin 3,
    sourceLocalPauli n (site a) μ ⊗ₖ mediatorLocal r e (physicalMemberPauli (member a) μ)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumParallelGraph
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

def qmaParallelGraphWeight {r : ℕ} (base : ν → ℝ) (Delta : ℝ) (amplitude : Fin r → κ → ℝ) :
    ν ⊕ (Fin r ⊕ (Fin r × κ)) → ℝ
  | .inl a => base a
  | .inr (.inl _) => Delta
  | .inr (.inr p) => amplitude p.1 p.2

def qmaPhysicalParallelHamiltonian (n r : ℕ) (Delta : ℝ)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ)
    (site : Fin r → κ → Fin n) (member : Fin r → κ → Fin 2) (amplitude : Fin r → κ → ℝ) :
    Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ :=
  1 ⊗ₖ physicalMediatorPenalty r Delta +
    (C ⊗ₖ 1 + ∑ e, qmaPhysicalSingletStar n r e (site e) (member e) (amplitude e))

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

def qmaPathCorrection (_R J : ℝ) {n : ℕ} : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ :=
  ((3/4+3*J^2:ℝ):ℂ) • 1

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

def qmaPartialPathsScale (w : ν → ℝ) (t : ℝ) (s : Finset ν) (N : ℝ) : ℝ :=
  let B := 3*(∑ e : {e // e ∉ s}, |w e.val|)+|t|
  let A := 3*∑ i : Fin s.card, (1+2*|w (qmaSelectedIndex s i)|)
  let D := B+4*∑ i : Fin s.card, (1+|w (qmaSelectedIndex s i)|)^2
  qmaRoutingScale A D N

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumReferencePenalty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual nearest-neighbor real YY penalty has a unit complement gap. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaReferenceYPenalty (n : ℕ) :
    Matrix (SourceSpinBasis (n+1)) (SourceSpinBasis (n+1)) ℂ :=
  ∑ i : Fin n, (1/2 : ℂ) • (1-sourceLocalPauli (n+1) i.castSucc 1*
    sourceLocalPauli (n+1) i.succ 1)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListScheduleGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact emitted edge order realizes the abstract scheduled subdivision.
This transfers the disjoint-route invariant to the literal list compiler. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListSchedule
open MediatorGraph
open scoped Classical

theorem freshValue (n r : ℕ) (i : Fin r) (a : Fin 2) :
    (fresh n r i a).val=n+2*i.val+a.val := by
  change n+(a.val+2*i.val)=_
  omega

end ContinuumCoulomb.QuantumListSchedule

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedXZEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full-space error of the literal six-to-four-to-three-to-two-to-XZ compiler. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedXZ
open scoped Classical
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def energy (xs : κ → List ι) (w : κ → ι → Fin 4) (J : κ → ℚ) (N : ℕ) : ℝ :=
  MediatorGraph.normalizedBottom (qmaPauliFamily (word xs w)
    (fun p => (coefficient J N p:ℝ)))

def threeEnergy (xs : κ → List ι) (w : κ → ι → Fin 4) (J : κ → ℚ) (N : ℕ) : ℝ :=
  MediatorGraph.normalizedBottom (qmaPauliFamily (threeWord xs w)
    (fun p => (threeCoefficient J N p:ℝ)))

def twoEnergy (xs : κ → List ι) (w : κ → ι → Fin 4) (J : κ → ℚ) (N : ℕ) : ℝ :=
  MediatorGraph.normalizedBottom (qmaPauliFamily (twoWord xs w)
    (fun p => (twoCoefficient J N p:ℝ)))

def xzThreeEnergy (xs : κ → List ι) (w : κ → ι → Fin 4) (J : κ → ℚ) (N : ℕ) : ℝ := by
  letI : Fintype (XZThreeQubit ι κ) := inferInstance
  letI : DecidableEq (XZThreeQubit ι κ) := inferInstance
  exact MediatorGraph.normalizedBottom (qmaPauliFamily (xzThreeWord xs w)
    (fun p => (xzThreeCoefficient J N p:ℝ)))

end ContinuumCoulomb.QuantumOrderedXZ

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedLabelEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full-space energy guarantee for the emitted raw exchange list, with
the five early reductions, private-pair subdivision, and four-spin error
all accounted for. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedLabelCompile
open QuantumOrderedLabelTable
open scoped Classical

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable {m n : ℕ}

def finalEnergy (xs : κ → List ι) (w : κ → ι → Fin 4) (J : κ → ℚ) (N : ℕ) : ℝ :=
  MediatorGraph.normalizedBottom (qmaPauliFamily (finalWord xs w)
    (fun p => (finalCoefficient J N p:ℝ)))

end ContinuumCoulomb.QuantumOrderedLabelCompile

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPaddedLocal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact full-space meaning of a fixed-width local coefficient table.
The coordinate map is the order of the literal support list; padding only
duplicates local words and never introduces spectator configurations. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPaddedLocal
open scoped BigOperators Classical

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def reindex {n : ℕ} (S : Finset ι) (e : Fin n ≃ {i // i ∈ S})
    (A : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) :
    Matrix (QMASupportBasis S) (QMASupportBasis S) ℂ :=
  fun s t => A (fun i => s (e i)) (fun i => t (e i))

end ContinuumCoulomb.QuantumPaddedLocal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPropagationOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual ordered support has its reference bit first, followed by
the duplicate-free propagation support in its literal source order. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPropagationOrder
open scoped Classical

def term (c : QMACircuit) (t : Fin c.gates.length) : QMACircuitTerm c :=
  .inr (.inr (.inr (.inr t)))

end ContinuumCoulomb.QuantumPropagationOrder

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_PhysicalOneElectronLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
A finite-rank lower bound for the manufactured one-electron Coulomb
field, obtained from the planar and vertical spectral estimates.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def verticalSpectralLevel (freq S η : ℝ) : ℝ :=
  3*freq/2-verticalCutoffDerivativeBound S^2/2-
    freq*(1+η⁻¹)*verticalCutoffTailConstant freq*Real.exp (-freq*S^2/8)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceFinalGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact final graph indexed by the literal output vertex count.
Changing only the proof of that count preserves every bond and weight. -/

noncomputable section

namespace ContinuumCoulomb.SourcePositiveProgram
open MediatorIteration SourceMetadataProgram ContactMediator

abbrev graphEdgeCount (s : ℕ) (d : BinaryHeisenberg) (hd : d.Valid) : ℕ :=
  (geometricSource s d hd).edges +
    (((geometricSource s d hd).edges * 2 + (geometricSource s d hd).edges * 2 * 2) +
      ((geometricSource s d hd).edges * 2 + (geometricSource s d hd).edges * 2 * 2) * 2)

end ContinuumCoulomb.SourcePositiveProgram

end

end OAI
end


