-- Prove2me | Definitions.Def_OAIQ092A010
-- name    : OAIQ092A010
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T20:04:38.604106+00:00
-- url     : https://prove2.me/theorems/dd8bdc5f-c70a-406f-9448-d8f29ef38363
-- title:
--   Definitions bundle OAIQ092A010 of the split of OpenAI, QMA-hardness of continuum Coulomb energy (result family 275)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ContinuumCoulomb.binary_coulomb_qmaHard` and `OAI.ContinuumCoulomb.unit_coulomb_qmaHard`, carved from OpenAI's openai/math development (OpenAI, *QMA-hardness of continuum Coulomb energy (result family 275)*, OpenAI Math Release, September 24, 2026, result family 275, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 647 declarations of OpenAI's Lean: 519 definitions and 128 theorems. The definitions and types are `OAI.ContinuumCoulomb.QuantumCrossingSelectProgram.crossingProgram`, `OAI.ContinuumCoulomb.QuantumCrossingSelectProgram.crossingsProgram`, `OAI.ContinuumCoulomb.QuantumCrossingSelectProgram.keepProgram`, `OAI.ContinuumCoulomb.QuantumCrossingSelectProgram.pairsProgram`, `OAI.ContinuumCoulomb.QuantumCrossingSelectProgram.program`, `OAI.ContinuumCoulomb.QuantumCrossingSelectProgram.retainedProgram`, `OAI.ContinuumCoulomb.QuantumCrossingSelectProgram.sitesProgram`, `OAI.ContinuumCoulomb.QuantumCrossingSelectProgram.weightProgram`, `OAI.ContinuumCoulomb.QuantumCrossingSiteProgram.allSites`, `OAI.ContinuumCoulomb.QuantumCrossingSiteProgram.allSitesProgram`, `OAI.ContinuumCoulomb.QuantumCrossingSiteProgram.flagsProgram`, `OAI.ContinuumCoulomb.QuantumCrossingSiteProgram.index`, `OAI.ContinuumCoulomb.QuantumCrossingSiteProgram.indexProgram`, `OAI.ContinuumCoulomb.QuantumCrossingSiteProgram.inputCode`, `OAI.ContinuumCoulomb.QuantumCrossingSiteProgram.sites`, `OAI.ContinuumCoulomb.QuantumCrossingSiteProgram.sitesProgram`, `OAI.ContinuumCoulomb.QuantumCrossingSiteProgram.target`, `OAI.ContinuumCoulomb.QuantumCrossingSiteProgram.targetProgram`, `OAI.ContinuumCoulomb.QuantumCrossingSiteProgram.terminal`, `OAI.ContinuumCoulomb.QuantumCrossingSiteProgram.terminalProgram`, `OAI.ContinuumCoulomb.QuantumDistinctCrossings.cell`, `OAI.ContinuumCoulomb.QuantumDistinctCrossings.cellsEquiv`, `OAI.ContinuumCoulomb.QuantumDistinctCrossings.program`, `OAI.ContinuumCoulomb.QuantumEvenListPieces.freshProgram`, `OAI.ContinuumCoulomb.QuantumEvenListPieces.pathsProgram`, `OAI.ContinuumCoulomb.QuantumEvenListPieces.pointProgram`, `OAI.ContinuumCoulomb.QuantumEvenRouteLabels.originalPath`, `OAI.ContinuumCoulomb.QuantumEvenTapeGeometry.edge`, `OAI.ContinuumCoulomb.QuantumEvenTapeGeometry.embedding`, `OAI.ContinuumCoulomb.QuantumEvenTapeGeometry.input`, `OAI.ContinuumCoulomb.QuantumEvenTapeGeometry.relabel`, `OAI.ContinuumCoulomb.QuantumEvenTapeGeometry.tripleEquiv`, `OAI.ContinuumCoulomb.QuantumEvenTapeGeometry.vertex`, `OAI.ContinuumCoulomb.QuantumEvenTapeProgram.Input`, `OAI.ContinuumCoulomb.QuantumEvenTapeProgram.Tags`, `OAI.ContinuumCoulomb.QuantumEvenTapeProgram.blockInput`, `OAI.ContinuumCoulomb.QuantumEvenTapeProgram.blockInputProgram`, `OAI.ContinuumCoulomb.QuantumEvenTapeProgram.blockProgram`, `OAI.ContinuumCoulomb.QuantumEvenTapeProgram.bondCountProgram`, `OAI.ContinuumCoulomb.QuantumEvenTapeProgram.bondsProgram` and 479 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, lean/OAI/Computability, lean/OAI/MathematicalPhysics, in whole or in part: `ContinuumCoulomb_ManyBody_FiniteBoxMatrix`, `ContinuumCoulomb_ManyBody_OrthonormalLocalizedModes`, `ContinuumCoulomb_OneParticle_CorrectedOneElectronProjection`, `ContinuumCoulomb_OneParticle_CorrectedResidualPairing`, `ContinuumCoulomb_OneParticle_CorrectedStateCoordinates`, `ContinuumCoulomb_OneParticle_LocalizedFockStates`, `ContinuumCoulomb_OneParticle_LocalizedLinearOrbitals`, `ContinuumCoulomb_OneParticle_LocalizedModeDerivatives`, `ContinuumCoulomb_OneParticle_ManufacturedComplement`, `ContinuumCoulomb_OneParticle_ManufacturedComplementBudget`, `ContinuumCoulomb_OneParticle_ManufacturedOneElectronGap`, `ContinuumCoulomb_OneParticle_ManufacturedOrbitalResidual`, `ContinuumCoulomb_OneParticle_ManufacturedWeakResidual`, `ContinuumCoulomb_Programs_SourceNuclearProgram`, `ContinuumCoulomb_Programs_SourcePositiveProgram`, `ContinuumCoulomb_Programs_UnitBinaryProgram`, `ContinuumCoulomb_Quantum_QuantumCircuitPadding`, `ContinuumCoulomb_Quantum_QuantumClockCells`, `ContinuumCoulomb_Quantum_QuantumClockPath`, `ContinuumCoulomb_Quantum_QuantumComputedRoutingTable`, `ContinuumCoulomb_Quantum_QuantumCrossingSelectProgram`, `ContinuumCoulomb_Quantum_QuantumCrossingSiteProgram`, `ContinuumCoulomb_Quantum_QuantumDescriptorSiteProgram`, `ContinuumCoulomb_Quantum_QuantumDiagonalTableProgram`, `ContinuumCoulomb_Quantum_QuantumDistinctCrossings`, `ContinuumCoulomb_Quantum_QuantumDistributedFamily`, `ContinuumCoulomb_Quantum_QuantumDistributedMatrix`, `ContinuumCoulomb_Quantum_QuantumEvenListPieces`, `ContinuumCoulomb_Quantum_QuantumEvenRouteLabels`, `ContinuumCoulomb_Quantum_QuantumEvenTapeGeometry`, `ContinuumCoulomb_Quantum_QuantumEvenTapeOrder`, `ContinuumCoulomb_Quantum_QuantumEvenTapeProgram`, `ContinuumCoulomb_Quantum_QuantumFinalRoutingProgram`, `ContinuumCoulomb_Quantum_QuantumFirstUseProgram`, `ContinuumCoulomb_Quantum_QuantumFirstUseSites`, `ContinuumCoulomb_Quantum_QuantumFixedMatrixProgram`, `ContinuumCoulomb_Quantum_QuantumFixedPauliProgram`, `ContinuumCoulomb_Quantum_QuantumForkGridInitial`, `ContinuumCoulomb_Quantum_QuantumForkGridProgram`, `ContinuumCoulomb_Quantum_QuantumForkListInitialProgram`, `ContinuumCoulomb_Quantum_QuantumForkListInitialSpatial`, `ContinuumCoulomb_Quantum_QuantumForkListInitialStateProgram`, `ContinuumCoulomb_Quantum_QuantumForkListNext`, `ContinuumCoulomb_Quantum_QuantumForkListPoints`, `ContinuumCoulomb_Quantum_QuantumForkListProgram`, `ContinuumCoulomb_Quantum_QuantumForkListScale`, `ContinuumCoulomb_Quantum_QuantumForkListSpatialPackage`, `ContinuumCoulomb_Quantum_QuantumForkRoutingData`, `ContinuumCoulomb_Quantum_QuantumGateArrival`, `ContinuumCoulomb_Quantum_QuantumGridCoordinates`, `ContinuumCoulomb_Quantum_QuantumGridLocality`, `ContinuumCoulomb_Quantum_QuantumHistoryCellProgram`, `ContinuumCoulomb_Quantum_QuantumHistoryCells`, `ContinuumCoulomb_Quantum_QuantumHistoryDeltaProgram`, `ContinuumCoulomb_Quantum_QuantumHistoryDiagonal`, `ContinuumCoulomb_Quantum_QuantumHistoryFork`, `ContinuumCoulomb_Quantum_QuantumHistoryIncidence`, `ContinuumCoulomb_Quantum_QuantumHistoryLattice`, `ContinuumCoulomb_Quantum_QuantumHistoryPrecisionProgram`, `ContinuumCoulomb_Quantum_QuantumHistoryPreparedProgram`, `ContinuumCoulomb_Quantum_QuantumHistoryRawCells`, `ContinuumCoulomb_Quantum_QuantumHistoryRoutedEnergy`, `ContinuumCoulomb_Quantum_QuantumHistorySamplerProgram`, `ContinuumCoulomb_Quantum_QuantumHistorySourceProgram`, `ContinuumCoulomb_Quantum_QuantumHistorySpatial`, `ContinuumCoulomb_Quantum_QuantumHistorySpatialProgram`, `ContinuumCoulomb_Quantum_QuantumHistoryTableProgram`, `ContinuumCoulomb_Quantum_QuantumInflatedListProgram`, `ContinuumCoulomb_Quantum_QuantumListLatticeProgram`, `ContinuumCoulomb_Quantum_QuantumListMergeProgram`, `ContinuumCoulomb_Quantum_QuantumListPathProgram`, `ContinuumCoulomb_Quantum_QuantumListPathStep`, `ContinuumCoulomb_Quantum_QuantumListRouteLattice`, `ContinuumCoulomb_Quantum_QuantumListRouteProgram`, `ContinuumCoulomb_Quantum_QuantumListScheduleProgram`, `ContinuumCoulomb_Quantum_QuantumOrderedCellProgram`, `ContinuumCoulomb_Quantum_QuantumOrderedCellTable`, `ContinuumCoulomb_Quantum_QuantumOrderedDescriptorProgram`, `ContinuumCoulomb_Quantum_QuantumOrderedDescriptors`, `ContinuumCoulomb_Quantum_QuantumOrderedLabelCompile`, `ContinuumCoulomb_Quantum_QuantumOrderedLabelFamily`, `ContinuumCoulomb_Quantum_QuantumOrderedLabelPipeline`, `ContinuumCoulomb_Quantum_QuantumOrderedRawCells`, `ContinuumCoulomb_Quantum_QuantumOrderedReference`, `ContinuumCoulomb_Quantum_QuantumOrderedSupport`, `ContinuumCoulomb_Quantum_QuantumOrderedWeightProgram`, `ContinuumCoulomb_Quantum_QuantumPackedSchedule`, `ContinuumCoulomb_Quantum_QuantumPaddedHistory`, `ContinuumCoulomb_Quantum_QuantumPaddedLabelEnergy`, `ContinuumCoulomb_Quantum_QuantumPaddedLabelProgram`, `ContinuumCoulomb_Quantum_QuantumPaddedLabelTable`, `ContinuumCoulomb_Quantum_QuantumPaddedSampling`, `ContinuumCoulomb_Quantum_QuantumPaddedTableProgram`, `ContinuumCoulomb_Quantum_QuantumPairDedup`, `ContinuumCoulomb_Quantum_QuantumPathProgram`, `ContinuumCoulomb_Quantum_QuantumPathScaleProgram`, `ContinuumCoulomb_Quantum_QuantumPathTable`, `ContinuumCoulomb_Quantum_QuantumPathVisitProgram`, `ContinuumCoulomb_Quantum_QuantumPlanarTapeGeometry`, `ContinuumCoulomb_Quantum_QuantumPlanarTapeProgram`, `ContinuumCoulomb_Quantum_QuantumPlanarTapeSupport`, `ContinuumCoulomb_Quantum_QuantumPortChainActual`, `ContinuumCoulomb_Quantum_QuantumPortChainProgram`, `ContinuumCoulomb_Quantum_QuantumPortScheduleTape`, `ContinuumCoulomb_Quantum_QuantumPreparedCircuit`, `ContinuumCoulomb_Quantum_QuantumPreparedVerifier`, `ContinuumCoulomb_Quantum_QuantumPropagationAction`, `ContinuumCoulomb_Quantum_QuantumPropagationOrder`, `ContinuumCoulomb_Quantum_QuantumPropagationSampler`, `ContinuumCoulomb_Quantum_QuantumPropagationSupport`, `ContinuumCoulomb_Quantum_QuantumPropagationTable`, `ContinuumCoulomb_Quantum_QuantumRawFamilyProgram`, `ContinuumCoulomb_Quantum_QuantumRawProgram`, `ContinuumCoulomb_Quantum_QuantumRawSchedule`, `ContinuumCoulomb_Quantum_QuantumRawTermProgram`, `ContinuumCoulomb_Quantum_QuantumRebitDiagonal`, `ContinuumCoulomb_Quantum_QuantumReferenceCongestion`, `ContinuumCoulomb_Quantum_QuantumReferenceEdgeTable`, `ContinuumCoulomb_Quantum_QuantumRouteSelectorProgram`, `ContinuumCoulomb_Quantum_QuantumRoutingCrossingTest`, `ContinuumCoulomb_Quantum_QuantumRoutingFamily`, `ContinuumCoulomb_Quantum_QuantumRoutingInputActual`, `ContinuumCoulomb_Quantum_QuantumRoutingInputProgram`, `ContinuumCoulomb_Quantum_QuantumRoutingTable`, `ContinuumCoulomb_Quantum_QuantumRowInsertion`, `ContinuumCoulomb_Quantum_QuantumRowStageBounds`, `ContinuumCoulomb_Quantum_QuantumScheduleCrossingGeometry`, `ContinuumCoulomb_Quantum_QuantumSparseEndpoint`, `ContinuumCoulomb_Quantum_QuantumSparseFirstUse`, `ContinuumCoulomb_Quantum_QuantumSpatialClockTerms`, `ContinuumCoulomb_Quantum_QuantumSpatialCrossingGeometry`, `ContinuumCoulomb_Quantum_QuantumSpatialCrossingProgram`, `ContinuumCoulomb_Quantum_QuantumSpatialInput`, `ContinuumCoulomb_Quantum_QuantumSpatialOccupancy`, `ContinuumCoulomb_Quantum_QuantumSpatialPortProgram`, `ContinuumCoulomb_Quantum_QuantumSpatialPropagation`, `ContinuumCoulomb_Quantum_QuantumSpatialReference`, `ContinuumCoulomb_Quantum_QuantumSpatialRoutingTape`, `ContinuumCoulomb_Quantum_QuantumSpatialTerms`, `ContinuumCoulomb_Quantum_QuantumStageIndex`, `ContinuumCoulomb_Quantum_QuantumStagePath`, `ContinuumCoulomb_Quantum_QuantumStageStep`, `ContinuumCoulomb_Quantum_QuantumSupportDedup`, `ContinuumCoulomb_Quantum_QuantumSupportLookup`, `ContinuumCoulomb_Quantum_QuantumSweepCellProgram`, `ContinuumCoulomb_Quantum_QuantumSweepCircuit`, `ContinuumCoulomb_Quantum_QuantumSweepCongestion`, `ContinuumCoulomb_Quantum_QuantumSweepCoverage`, `ContinuumCoulomb_Quantum_QuantumSweepCursor`, `ContinuumCoulomb_Quantum_QuantumSweepEndpoint`, `ContinuumCoulomb_Quantum_QuantumTaggedRouteProgram`, `ContinuumCoulomb_Quantum_QuantumTaggedStage`, `ContinuumCoulomb_Quantum_QuantumTaggedSupport`, `ContinuumCoulomb_Quantum_QuantumTaggedSweep`, `ContinuumCoulomb_Quantum_QuantumTimeCongestion`, `ContinuumCoulomb_Quantum_QuantumTransferIndex`, `ContinuumCoulomb_Quantum_QuantumUnaryMatrix`, `ContinuumCoulomb_Reduction_SourceFinalGraph`, `ContinuumCoulomb_Reduction_SourceGraphIndex`, `ContinuumCoulomb_Reduction_SourceHubbardEnergy`, `ContinuumCoulomb_Reduction_SourceIndexedSites`, `ContinuumCoulomb_Reduction_SourceNormalizedPromise`, `ContinuumCoulomb_Reduction_SourcePhysicalPromise`, `ContinuumCoulomb_Reduction_SourcePhysicalThreshold`, `ContinuumCoulomb_Reduction_SourcePositiveBounds`, `ContinuumCoulomb_Reduction_SourcePositiveCorrectness`, `ContinuumCoulomb_Reduction_SourceUnitCoulomb`.
--
--   **Imports.** It imports the published bundle `Def_ContinuumCoulombHardness`; the bundles `OAIQ092A008` and `OAIQ092A009` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ092A015`, `OAIQ092A016` and `OAIQ092A017`; the statements `OAI.ContinuumCoulomb.QuantumEvenTapeGeometry.output_polynomialPromise`, `OAI.ContinuumCoulomb.QuantumFinalRoutingProgram.spatial_energy_error`, `OAI.ContinuumCoulomb.QuantumFinalRoutingProgram.spatial_planar_energy`, `OAI.ContinuumCoulomb.QuantumFinalRoutingProgram.spatial_planar_noLoops`, `OAI.ContinuumCoulomb.QuantumFinalRoutingProgram.spatial_polynomialPromise`, `OAI.ContinuumCoulomb.QuantumHistorySourceProgram.history_error`, `OAI.ContinuumCoulomb.QuantumHistorySourceProgram.routed_realization`, `OAI.ContinuumCoulomb.QuantumHistorySpatial.source_data_power`, `OAI.ContinuumCoulomb.QuantumPaddedLabelProgram.history_accuracy`, `OAI.ContinuumCoulomb.QuantumPlanarTapeGeometry.final_realization`, `OAI.ContinuumCoulomb.QuantumSpatialCrossingProgram.planar_bounds`, `OAI.ContinuumCoulomb.QuantumSpatialPortProgram.realizes`, `OAI_ContinuumCoulomb_RawCoulombSample_value_error`, `OAI.ContinuumCoulomb.SourceNuclearProgram.exists_indexed_matrix_offsets`, `OAI.ContinuumCoulomb.SourceUnitCoulomb.actual_threshold_error`, `OAI.ContinuumCoulomb.SourceUnitCoulomb.promise_of_hubbard_interval`, `OAI.ContinuumCoulomb.exists_source_target_parameters`, `OAI.ContinuumCoulomb.localizedSpinResidual_sum_bound`, `OAI.ContinuumCoulomb.localizedTensorState_kinetic_bound`, `OAI.ContinuumCoulomb.localizedTensor_hubbard_lower`, `OAI.ContinuumCoulomb.manufacturedSlab_residual_finite_rank_lower`, `OAI.ContinuumCoulomb.manufacturedSlab_uniform_tensorComplement_gap`, `OAI.ContinuumCoulomb.manufacturedTensor_nuclear_interacting_lower`, `OAI.ContinuumCoulomb.manufactured_grid_ground_bounds` and `OAI.ContinuumCoulomb.source_cloud_comparison`; the proofs of `OAI.ContinuumCoulomb.PrefactorSourceContactProgram.exists_source_calibration`, `OAI.ContinuumCoulomb.QuantumEvenTapeGeometry.output_polynomialPromise`, `OAI.ContinuumCoulomb.QuantumFinalRoutingProgram.spatial_energy_error`, `OAI.ContinuumCoulomb.QuantumFinalRoutingProgram.spatial_planar_energy`, `OAI.ContinuumCoulomb.QuantumFinalRoutingProgram.spatial_planar_noLoops`, `OAI.ContinuumCoulomb.QuantumFinalRoutingProgram.spatial_polynomialPromise`, `OAI.ContinuumCoulomb.QuantumHistorySourceProgram.history_error`, `OAI.ContinuumCoulomb.QuantumHistorySourceProgram.routed_realization`, `OAI.ContinuumCoulomb.QuantumHistorySpatial.source_data_power`, `OAI.ContinuumCoulomb.QuantumPaddedLabelProgram.history_accuracy`, `OAI.ContinuumCoulomb.QuantumPlanarTapeGeometry.final_realization`, `OAI.ContinuumCoulomb.QuantumSpatialCrossingProgram.planar_bounds`, `OAI.ContinuumCoulomb.QuantumSpatialPortProgram.realizes`, `OAI.ContinuumCoulomb.SourceNuclearProgram.exists_indexed_matrix_offsets`, `OAI.ContinuumCoulomb.SourceUnitCoulomb.actual_threshold_error`, `OAI.ContinuumCoulomb.SourceUnitCoulomb.promise_of_hubbard_interval`, `OAI.ContinuumCoulomb.binary_coulomb_qmaHard_of_two_inputs`, `OAI.ContinuumCoulomb.exists_actual_oneBody_parameters`, `OAI.ContinuumCoulomb.exists_source_target_parameters`, `OAI.ContinuumCoulomb.exists_source_unit_reduction_with_planar_gap`, `OAI.ContinuumCoulomb.localizedSpinResidual_sum_bound`, `OAI.ContinuumCoulomb.localizedTensorState_kinetic_bound`, `OAI.ContinuumCoulomb.localizedTensor_hubbard_lower`, `OAI.ContinuumCoulomb.localized_hubbard_near_trial`, `OAI.ContinuumCoulomb.manufacturedSlab_residual_finite_rank_lower`, `OAI.ContinuumCoulomb.manufacturedSlab_uniform_tensorComplement_gap`, `OAI.ContinuumCoulomb.manufacturedTensor_nuclear_interacting_lower`, `OAI.ContinuumCoulomb.manufactured_grid_ground_bounds`, `OAI.ContinuumCoulomb.manufactured_grid_witness`, `OAI.ContinuumCoulomb.manufactured_polynomial_comparison`, `OAI.ContinuumCoulomb.publishedCMPHardness`, `OAI.ContinuumCoulomb.source_cloud_comparison` and `OAI.ContinuumCoulomb.unit_coulomb_qmaHard_of_two_inputs`.
-- source:
--   OpenAI, QMA-hardness of continuum Coulomb energy (result family 275), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 275; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Continuum-Coulomb-hardness-with-binary-nuclear-charges-September-24-2026/Continuum-Coulomb-hardness-with-binary-nuclear-charges-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis, lean/OAI/Computability, lean/OAI/MathematicalPhysics at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Round
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
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.Analysis.ODE.ExistUnique
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
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.EReal.Basic
import Mathlib.Data.Fin.Rev
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
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Set
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.UniformIntegrable
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
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
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
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.Antilipschitz
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_ContinuumCoulombHardness
import Definitions.Def_OAIQ092A008
import Definitions.Def_OAIQ092A009

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedModeDerivatives
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual classical first derivatives of the localized modes are L2.
The planar/transverse product formula and the volume-preserving chart give
membership without a smooth-compact-support assumption on the orbitals. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem normalizedPlanarMode_partial_square_integrable (e : PlanarPosition) :
    Integrable (fun r => planarPartial normalizedPlanarMode e r ^ 2) := by
  simp_rw [normalizedPlanarMode_partial, mul_pow]
  exact (planarResolventMode_partial_square_integrable e).const_mul _

theorem localizedMode_planarDerivative_memLp {freq : ℝ} (hfreq : 0 < freq)
    (u e : PlanarPosition) :
    MemLp (fun p : SplitPosition => planarPartial normalizedPlanarMode e (p.1 - u) * verticalMode freq p.2) 2 := by
  apply (memLp_two_iff_integrable_sq (by
    exact (((planarPartial_continuous (normalizedPlanarMode_C7.of_le (by norm_num)) e).comp
      (continuous_fst.sub continuous_const)).mul
      ((verticalMode_smooth freq).continuous.comp continuous_snd)).aestronglyMeasurable)).mpr
  simp_rw [mul_pow]
  rw [Measure.volume_eq_prod]
  exact ((normalizedPlanarMode_partial_square_integrable e).comp_sub_right u).mul_prod
    (verticalMode_square_integrable hfreq)

theorem localizedMode_fderiv_memLp {freq : ℝ} (hfreq : 0 < freq) (u : PlanarPosition) (e : SplitPosition) :
    MemLp (fun p => fderiv ℝ (localizedMode freq u) p e) 2 := by
  simp_rw [localizedMode_fderiv]
  exact (localizedMode_planarDerivative_memLp hfreq u e.1).add
    ((localizedMode_verticalDerivative_memLp hfreq u).mul_const e.2)

theorem continuumLocalizedMode_fderiv_memLp {freq : ℝ} (hfreq : 0 < freq) (u : PlanarPosition) (e : Position) :
    MemLp (fun x => fderiv ℝ (continuumLocalizedMode freq u) x e) 2 := by
  simp_rw [continuumLocalizedMode_fderiv]
  exact (localizedMode_fderiv_memLp hfreq u (positionSplitCoordinates e)).comp_measurePreserving
    positionSplitCoordinates_measurePreserving

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ManufacturedOrbitalResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The residual for the actual manufactured one-body operator is the sum
of the checked off-site, finite-slab, and cutoff/counterterm residuals. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

/-- The seventy-second-moment tail keeps the residual compatible with the
physical mesh scale even for high-aspect slabs. -/
def manufacturedOrbitalSquaredError (rho H S freq δ D R : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (j : Fin m) : ℝ :=
  3*((m : ℝ)^2*(PlanarSobolev.wellBound*planarWellMatrixConstant)*Real.exp (-(19/10 : ℝ)*D)+
    (2*(6*Real.pi*rho*S^3/H)^2+2*(64*rho*S/H)^2*localizedDensityMoment freq (u j) 4+
      2*(2*slabUniformBound rho H S)^2*(localizedDensityMoment freq (u j) 72/R^72)+
      2*(2*Real.pi*rho)^2*(localizedDensityMoment freq (u j) 72/R^68))+
    (((m : ℝ)*δ*PlanarSobolev.wellBound)^2+
      ((m : ℝ)*(δ+1)*PlanarSobolev.wellBound)^2*
        (localizedDensityMoment freq (u j) 8/(S/2)^8)))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_FiniteBoxMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-box correction to the intended one-body matrix. The well-depth
counterterm remains part of the target matrix; only its vertical truncation
and the finite slab approximation contribute to this error. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def finiteBoxOrbitalSquaredError (rho H S freq δ r : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (j : Fin m) : ℝ :=
  2*((2*(6*Real.pi*rho*S^3/H)^2+2*(64*rho*S/H)^2*localizedDensityMoment freq (u j) 4+
      2*(2*slabUniformBound rho H S)^2*(localizedDensityMoment freq (u j) 72/r^72)+
      2*(2*Real.pi*rho)^2*(localizedDensityMoment freq (u j) 72/r^68))+
    ((m:ℝ)*(δ+1)*PlanarSobolev.wellBound)^2/(S/2)^24*
      (∫ x, ‖x‖^24*continuumLocalizedMode freq 0 x^2))

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

theorem localizedLinearOrbital_fderiv_memLp {freq : ℝ} (hfreq : 0 < freq) {m : ℕ}
    (u : Fin m → PlanarPosition) (a : Fin m → ℝ) (e : Position) :
    MemLp (fun x => fderiv ℝ (localizedLinearOrbital freq u a) x e) 2 := by
  have ht (j : Fin m) : MemLp (fun x => a j *
      fderiv ℝ (continuumLocalizedMode freq (u j)) x e) 2 volume :=
    (continuumLocalizedMode_fderiv_memLp hfreq (u j) e).const_mul (a j)
  have hs : MemLp (fun x => ∑ j, a j *
      fderiv ℝ (continuumLocalizedMode freq (u j)) x e) 2 volume :=
    memLp_finsetSum Finset.univ (fun j _ => ht j)
  simpa only [localizedLinearOrbital_fderiv] using hs

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

theorem correctedLocalizedMode_partial_memLp {freq : ℝ} (hfreq : 0 < freq) {m : ℕ}
    (u : Fin m → PlanarPosition) (i : Fin m) (b : Fin 3) :
    MemLp (fun x => fderiv ℝ (correctedLocalizedMode freq u i) x (EuclideanSpace.single b 1)) 2 :=
  localizedLinearOrbital_fderiv_memLp hfreq u _ _

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

theorem correctedOneElectronValue_partial_memLp {freq : ℝ} (hfreq : 0 < freq) {m : ℕ}
    (u : Fin m → PlanarPosition) (c : SpinConfiguration 1 → Fin m → ℂ)
    (s : SpinConfiguration 1) (a : Fin 1 × Fin 3) :
    MemLp (fun x => fderiv ℝ (correctedOneElectronValue freq u c s) x
      (EuclideanSpace.single a 1)) 2 := by
  obtain ⟨a,b⟩ := a
  have ha : a = 0 := Subsingleton.elim _ _
  subst a
  simp_rw [correctedOneElectronValue_partial]
  exact memLp_finsetSum Finset.univ (fun i _ =>
    ((correctedLocalizedMode_partial_memLp hfreq u i b).ofReal.comp_measurePreserving
      oneElectronCoordinates.measurePreserving).const_mul (c s i))

def correctedOneElectronState {freq : ℝ} (hfreq : 0 < freq) {m : ℕ}
    (u : Fin m → PlanarPosition) (c : SpinConfiguration 1 → Fin m → ℂ) : Coulomb.H1Vector 1 :=
  classicalH1State (correctedOneElectronValue freq u c) (correctedOneElectronValue_C1 freq u c)
    (correctedOneElectronValue_memLp hfreq u c) (correctedOneElectronValue_partial_memLp hfreq u c)

def correctedOneElectronProjection {freq : ℝ} (hfreq : 0 < freq)
    {m : ℕ} (u : Fin m → PlanarPosition) (v : Coulomb.H1Vector 1) : Coulomb.H1Vector 1 :=
  correctedOneElectronState hfreq u (correctedOneElectronCoefficients hfreq u v)

def correctedOneElectronRemainder {freq : ℝ} (hfreq : 0 < freq)
    {m : ℕ} (u : Fin m → PlanarPosition) (v : Coulomb.H1Vector 1) : Coulomb.H1Vector 1 :=
  v.add ((correctedOneElectronProjection hfreq u v).rsmul (-1))

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

theorem oneElectronLocalizedMode_partial_memLp {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) (a : Fin 1 × Fin 3) :
    MemLp (configurationRealPartial (oneElectronLocalizedMode freq u) a) 2 := by
  have he : configurationRealPartial (oneElectronLocalizedMode freq u) a =
      (fun x => fderiv ℝ (continuumLocalizedMode freq u) (oneElectronCoordinates x)
        (oneElectronCoordinates (EuclideanSpace.single a 1))) :=
    funext (oneElectronLocalizedMode_partial freq u a)
  rw [he]
  exact (continuumLocalizedMode_fderiv_memLp hfreq u _).comp_measurePreserving
    oneElectronCoordinates.measurePreserving

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CorrectedResidualPairing
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.complexMollification_im _root_.OAI.ContinuumCoulomb.complexMollification_re _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
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

theorem oneElectronCorrectedMode_partial_memLp {freq : ℝ} (hfreq : 0 < freq)
    {m : ℕ} (u : Fin m → PlanarPosition) (i : Fin m) (a : Fin 1 × Fin 3) :
    MemLp (configurationRealPartial (oneElectronCorrectedMode freq u i) a) 2 := by
  have he : configurationRealPartial (oneElectronCorrectedMode freq u i) a =
      (fun x => ∑ j, correctedLocalizedCoefficients u i j*
        configurationRealPartial (oneElectronLocalizedMode freq (u j)) a x) :=
    funext (configurationRealPartial_sum _ _
      (fun j => (oneElectronLocalizedMode_C2 freq (u j)).of_le (by norm_num)) a)
  rw [he]
  exact memLp_finsetSum Finset.univ (fun j _ =>
    (oneElectronLocalizedMode_partial_memLp hfreq (u j) a).const_mul _)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CorrectedStateCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Derivative coordinates of an actual corrected-orbital H1 state. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def correctedPartialLp {freq : ℝ} (hfreq : 0 < freq) {m : ℕ}
    (u : Fin m → PlanarPosition) (i : Fin m) (a : Fin 1 × Fin 3) :
    Lp ℂ 2 (volume : Measure (Configuration 1)) :=
  (oneElectronCorrectedMode_partial_memLp hfreq u i a).ofReal.toLp
    (fun x => (configurationRealPartial (oneElectronCorrectedMode freq u i) a x : ℂ))

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

theorem localizedSpinMode_partial_memLp {freq : ℝ} (hfreq : 0 < freq) {m : ℕ}
    (u : Fin (m+1) → PlanarPosition) (j : Fin ((2*m+1)+1)) (s : Fin 2) (b : Fin 3) :
    MemLp (fun x => fderiv ℝ (fun y => localizedSpinMode freq u j y s) x (EuclideanSpace.single b 1)) 2 :=
  realSpinOrbital_partial_memLp _ (correctedLocalizedMode_C1 freq u _)
    (correctedLocalizedMode_partial_memLp hfreq u _) _ s b

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ManufacturedOneElectronGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The manufactured field's finite-rank lower estimate holds on the entire
spinful weak-H1 domain. No smoothness, compact support, or reality condition is
imposed on the state in this theorem. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def manufacturedSpectralLevel (γ : ℝ) (m : ℕ) (D η freq S rho H δ : ℝ) : ℝ :=
  planarSpectralLevel γ m D η+verticalSpectralLevel freq S η-freq*(1+η)-
    (δ*PlanarSobolev.wellBound+6*Real.pi*rho*S^3/H)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ManufacturedComplement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The manufactured field has a positive gap above its one-orbital energy
on the complement of the actual orthonormalized modes. All localization losses
are retained explicitly; they are not charged to the final energy precision. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def manufacturedSpectralLoss (γ : ℝ) (m : ℕ) (D η freq S rho H δ : ℝ) : ℝ :=
  planarSiteDerivativeBound D^2+
    γ*(1+η⁻¹)*m*planarSiteTailConstant*Real.exp (-(19/20:ℝ)*(D/8))+
    verticalCutoffDerivativeBound S^2/2+
    freq*(1+η⁻¹)*verticalCutoffTailConstant freq*Real.exp (-freq*S^2/8)+
    freq*η+δ*PlanarSobolev.wellBound+6*Real.pi*rho*S^3/H

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ManufacturedComplementBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit polynomial bounds for the actual kinetic budget and the
coercive complement allowance in the manufactured Hubbard comparison. -/

noncomputable section
namespace ContinuumCoulomb

def manufacturedKineticBudgetConstant (freq rho : ℝ) : ℝ :=
  2*PlanarSobolev.wellBound+6*Real.pi*rho+((-1/2:ℝ)+freq/2)+2

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

noncomputable def certificate : Turing.TM2ComputableInPolyTime
    unitCoulombCodec.encode binaryCoulombCodec.encode UnitCoulomb.toBinary := program.toTM2

noncomputable def reduction : PolynomialManyOne
    unitCoulombCodec.encode binaryCoulombCodec.encode unitCoulombPromise binaryCoulombPromise where
  map := UnitCoulomb.toBinary
  polynomialTime := certificate
  maps_yes _ := unitBinary_yes
  maps_no _ := unitBinary_no

end ContinuumCoulomb.UnitBinaryProgram

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

def lowerThreshold (d : SquareLatticeHeisenberg) (W G : ℕ) (a : ℚ) : ℚ :=
  a - MediatorIteration.offset (family d (denominator d.edges G))
    (denominator d.edges G + W + 1) G + 1 / (128 * (G : ℚ))

def upperThreshold (d : SquareLatticeHeisenberg) (W G : ℕ) (b : ℚ) : ℚ :=
  b - MediatorIteration.offset (family d (denominator d.edges G))
    (denominator d.edges G + W + 1) G - 1 / (128 * (G : ℚ))

end ContinuumCoulomb.SourceNormalizedSpectrum

end

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

noncomputable opaque verticesProgram (k : ℕ) : Procedure binaryHeisenbergCodec.encode unaryCode
    (fun d => (output k d).vertices) :=
  MediatorThreeStageProgram.verticesProgram.comp (normalizedProgram k)
noncomputable opaque offsetProgram (k : ℕ) : Procedure binaryHeisenbergCodec.encode ratCode
    (offset k) := MediatorOffsetProgram.offsetProgram.comp (normalizedProgram k)

noncomputable opaque gRationalProgram (k : ℕ) : Procedure binaryHeisenbergCodec.encode ratCode
    (fun d => ((SourceMetadataProgram.size d ^ k : ℕ) : ℚ)) :=
  Procedure.natToRat.comp (Procedure.unaryToBits.comp (SourceMetadataProgram.boundProgram k))
noncomputable opaque denominatorProgram (k : ℕ) : Procedure binaryHeisenbergCodec.encode ratCode
    (fun d => 128 * ((SourceMetadataProgram.size d ^ k : ℕ) : ℚ)) :=
  Procedure.ratMul.comp ((Procedure.constant binaryHeisenbergCodec.encode ratCode 128).pair
    (gRationalProgram k))
noncomputable opaque errorProgram (k : ℕ) : Procedure binaryHeisenbergCodec.encode ratCode (error k) :=
  Procedure.ratDiv.comp ((Procedure.constant binaryHeisenbergCodec.encode ratCode 1).pair
    (denominatorProgram k))
noncomputable opaque lowerShiftProgram (k : ℕ) : Procedure binaryHeisenbergCodec.encode ratCode
    (fun d => d.lower.value - offset k d) :=
  Procedure.ratSub.comp (SourcePrograms.lower.pair (offsetProgram k))
noncomputable opaque upperShiftProgram (k : ℕ) : Procedure binaryHeisenbergCodec.encode ratCode
    (fun d => d.upper.value - offset k d) :=
  Procedure.ratSub.comp (SourcePrograms.upper.pair (offsetProgram k))
noncomputable opaque lowerProgram (k : ℕ) : Procedure binaryHeisenbergCodec.encode ratCode
    (fun d => (output k d).lower) :=
  Procedure.ratAdd.comp ((lowerShiftProgram k).pair (errorProgram k))
noncomputable opaque upperProgram (k : ℕ) : Procedure binaryHeisenbergCodec.encode ratCode
    (fun d => (output k d).upper) :=
  Procedure.ratSub.comp ((upperShiftProgram k).pair (errorProgram k))

end ContinuumCoulomb.SourcePositiveProgram

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

noncomputable opaque normalizedEnvironmentProgram (k : ℕ) : Procedure binaryHeisenbergCodec.encode
    envCode (fun d => (SourceNormalizationProgram.normalized (input k d)).1) :=
  (Procedure.first envCode (listCode bondCode)).comp (normalizedProgram k)

noncomputable opaque finalBoundProgram (k : ℕ) : Procedure binaryHeisenbergCodec.encode
    unaryCode ((fun x : Env => MediatorParameters.finalWeight x.1 x.2.1 x.2.2.1) ∘
      (fun d => (SourceNormalizationProgram.normalized (input k d)).1)) :=
  MediatorUnaryProgram.finalWeight.comp (normalizedEnvironmentProgram k)

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

theorem vertices_eq (k : ℕ) (d : BinaryHeisenberg) (h : d.Valid) :
    (output k d).vertices = d.coordinate.length +
      (SourceNormalizedSpectrum.retained (d.toSource h) (roundingDenominator k d)).length * 2 +
      (SourceNormalizedSpectrum.retained (d.toSource h) (roundingDenominator k d)).length * 2 * 2 +
      ((SourceNormalizedSpectrum.retained (d.toSource h) (roundingDenominator k d)).length * 2 +
        (SourceNormalizedSpectrum.retained (d.toSource h) (roundingDenominator k d)).length * 2 * 2) * 2 := by
  change (normalized k d).1.2.2.2 + 18 * (normalized k d).1.1 = _
  rw [normalized, normalized_eq k d h]
  dsimp only
  omega

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

noncomputable def input (rho C : ℕ) (ε c : ℚ) (s p h k A B q : ℕ)
    (d : BinaryHeisenberg) : AffinePhysicalThreshold.Input :=
  (((mesh k d,
        (horizontalRadius k d,verticalRadius k d)),
      ((SourcePositiveProgram.output s d).vertices,
        (SourceContactProgram.size d^q,
          ((SourcePositiveProgram.output s d).lower,(SourcePositiveProgram.output s d).upper)))),
    (((SourceContactProgram.size d^(30*B):ℕ):ℚ)⁻¹,
      (PrefactorSourceContactProgram.value rho (CalibrationMesh.prefactor rho) C ε c
        s p h k A B d,
       (SourcePositiveProgram.output s d).bonds.map (fun e => e.2.2))))

noncomputable def value (rho C : ℕ) (ε c : ℚ) (s p h k A B q : ℕ)
    (d : BinaryHeisenberg) : ℚ×ℚ :=
  AffinePhysicalThreshold.value rho (input rho C ε c s p h k A B q d)

noncomputable opaque inputProgram (rho C : ℕ) (ε c : ℚ) (s p h k A B q : ℕ) :
    Procedure binaryHeisenbergCodec.encode AffinePhysicalThreshold.inputCode
      (input rho C ε c s p h k A B q) := by
  let geometry := (SourceContactProgram.powerProgram (10*k)).pair
    ((SourceContactProgram.powerProgram (60*k)).pair (SourceContactProgram.powerProgram (15*k)))
  let bounds := (SourcePositiveProgram.lowerProgram s).pair (SourcePositiveProgram.upperProgram s)
  let metadata := (SourcePositiveProgram.verticesProgram s).pair
    ((SourceContactProgram.powerProgram q).pair bounds)
  let sites := PrefactorSourceContactProgram.program rho (CalibrationMesh.prefactor rho) C ε c
    s p h k A B
  let weights := SourceContactProgram.coefficientsProgram s
  exact (geometry.pair metadata).pair ((tauProgram B).pair (sites.pair weights))

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

noncomputable def sites (rho C : ℕ) (ε c : ℚ) (s p h k A B : ℕ)
    (d : BinaryHeisenberg) : List (ℚ×ℚ) :=
  PrefactorSourceContactProgram.value rho (CalibrationMesh.prefactor rho) C ε c s p h k A B d

noncomputable def input (rho C : ℕ) (ε c : ℚ) (s p h k A B r : ℕ)
    (d : BinaryHeisenberg) : PhysicalNuclearProgram.Input :=
  (((SourceContactProgram.size d^r,SourcePhysicalThreshold.mesh k d),
    ((amplification rho k d,SourcePhysicalThreshold.slabVertical k d),
      sites rho C ε c s p h k A B d)),
    (SourcePhysicalThreshold.horizontalRadius k d,
      (SourcePhysicalThreshold.horizontalRadius k d,SourcePhysicalThreshold.verticalRadius k d)))

noncomputable opaque inputProgram (rho C : ℕ) (ε c : ℚ) (s p h k A B r : ℕ) :
    Procedure binaryHeisenbergCodec.encode PhysicalNuclearProgram.inputCode
      (input rho C ε c s p h k A B r) := by
  let mesh := Procedure.unaryToBits.comp (SourceContactProgram.powerProgram (10*k))
  let precise := SourceContactProgram.powerProgram r
  let hs := SourceContactProgram.powerProgram (60*k)
  let vs := SourceContactProgram.powerProgram (15*k)
  let points := PrefactorSourceContactProgram.program rho (CalibrationMesh.prefactor rho) C ε c
    s p h k A B
  let field := ((amplificationProgram rho k).pair (verticalProgram k)).pair points
  exact ((precise.pair mesh).pair field).pair (hs.pair (hs.pair vs))

end ContinuumCoulomb.SourceNuclearProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumUnaryMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual Hermitian matrix on all clock and computation qubits. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaUnaryPropagationMap (c : QMACircuit) :
    (QMAUnaryBasis c → ℂ) →ₗ[ℂ] (QMAUnaryRow c → ℂ) where
  toFun u p := if QMAClockGuard c.gates.length p.1 p.2.1 ∧
      p.2.1 (qmaClockMiddle c.gates.length p.1) = 0 then
    qmaUnaryResidual c u p.1 p.2.1 p.2.2 else 0
  map_add' u v := by
    funext p
    by_cases h : QMAClockGuard c.gates.length p.1 p.2.1 ∧
        p.2.1 (qmaClockMiddle c.gates.length p.1) = 0
    · simp only [ite_eq_left h,Pi.add_apply]
      change (u _+v _)-(qmaStepMatrix c p.1.val).mulVec
        ((fun a => u (p.2.1,a))+(fun a => v (p.2.1,a))) p.2.2 = _
      rw [Matrix.mulVec_add]
      simp only [qmaUnaryResidual,Pi.add_apply]
      ring
    · simp only [ite_eq_right h,Pi.add_apply,add_zero]
  map_smul' a u := by
    funext p
    by_cases h : QMAClockGuard c.gates.length p.1 p.2.1 ∧
        p.2.1 (qmaClockMiddle c.gates.length p.1) = 0
    · simp only [ite_eq_left h,Pi.smul_apply,RingHom.id_apply]
      change a*u _-(qmaStepMatrix c p.1.val).mulVec
        (a • (fun b => u (p.2.1,b))) p.2.2 = _
      rw [Matrix.mulVec_smul]
      simp only [qmaUnaryResidual,Pi.smul_apply,smul_eq_mul]
      ring
    · simp only [ite_eq_right h,Pi.smul_apply,RingHom.id_apply,smul_zero]

def qmaUnaryPropagationMatrix (c : QMACircuit) : Matrix (QMAUnaryRow c) (QMAUnaryBasis c) ℂ :=
  LinearMap.toMatrix' (qmaUnaryPropagationMap c)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPropagationAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact agreement of the local propagation operator with the full
unary-clock Hamiltonian. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaPropagationSlice (c : QMACircuit) (t : Fin c.gates.length) :
    Matrix (QMAUnaryBasis c) (QMAUnaryBasis c) ℂ :=
  (qmaUnaryPropagationMatrix c).submatrix (fun p => (t,p)) id

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumDistributedMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The distributed-input history is an actual Hermitian matrix on all unary strings. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaUnaryDistributedHamiltonian (c : QMACircuit)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) : Matrix (QMAUnaryBasis c) (QMAUnaryBasis c) ℂ :=
  Matrix.diagonal (fun p => (qmaUnaryClockDiagonal c p : ℂ))+
    Matrix.diagonal (fun p => (qmaUnaryOutputDiagonal c p : ℂ))+
    (14:ℂ) • Matrix.diagonal (fun p => (qmaUnaryDistributedDiagonal c τ p : ℂ))+
    ((14*(c.work+1)+8)*c.gates.length:ℂ) •
      ((qmaUnaryPropagationMatrix c).conjTranspose*qmaUnaryPropagationMatrix c)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumDistributedFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A linear-size, five-local term family with distributed initialization checks. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaDistributedQubitHamiltonian (c : QMACircuit)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) :
    Matrix (QMACircuitQubit c → Fin 2) (QMACircuitQubit c → Fin 2) ℂ :=
  (qmaUnaryDistributedHamiltonian c τ).submatrix (qmaCircuitQubitSplit c) (qmaCircuitQubitSplit c)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRowInsertion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A logical gate is inserted immediately after its last operand arrives. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped Classical

theorem qmaGateCut_le (work : ℕ) (e : Equiv.Perm (Fin (work+1))) (g : QMAGate) :
    qmaGateCut work e g ≤ work+1 := by
  apply Nat.succ_le_of_lt
  apply (Finset.sup_lt_iff (by omega : 0 < work+1)).mpr
  intro i _
  exact (e.symm i).isLt

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRowStageBounds
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The insertion keeps the exact stage size and well-formed gate set. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaRowStage_length (width work : ℕ)
    (l r : Fin (width+1) → Fin (work+1)) (e : Equiv.Perm (Fin (width+1)))
    (g : QMAGate) : (qmaRowStage width work l r e g).length = 3*(width+1)+1 := by
  let ps := qmaRowPairs (l ∘ e) (r ∘ e)
  have hs : (ps.take (qmaGateCut width e g)).length+
      (ps.drop (qmaGateCut width e g)).length = width+1 := by
    rw [←List.length_append,List.take_append_drop]
    simp [ps,qmaRowPairs]
  change (qmaTransferGates (ps.take (qmaGateCut width e g)) ++
    [qmaMapGate width work r g] ++ qmaTransferGates (ps.drop (qmaGateCut width e g))).length = _
  simp only [List.length_append,List.length_singleton,qmaTransferGates_length]
  omega

theorem qmaRowStage_wellFormed (width work : ℕ)
    (l r : Fin (width+1) → Fin (work+1)) (hr : Function.Injective r)
    (hlr : ∀ i j, l i ≠ r j) (e : Equiv.Perm (Fin (width+1)))
    (g : QMAGate) (hg : g.WellFormed (width+1)) :
    ∀ k ∈ qmaRowStage width work l r e g, k.WellFormed (work+1) := by
  have hp := qmaRowPairs_distinct (l ∘ e) (r ∘ e) (fun i j => hlr (e i) (e j))
  intro k hk
  simp only [qmaRowStage,List.mem_append,List.mem_singleton] at hk
  rcases hk with (hk | rfl) | hk
  · exact qmaTransferGates_wellFormed _
      (fun p hm => hp p (List.mem_of_mem_take hm)) k hk
  · exact qmaMapGate_wellFormed width work r hr g hg
  · exact qmaTransferGates_wellFormed _
      (fun p hm => hp p (List.mem_of_mem_drop hm)) k hk

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSweepCircuit
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Alternating row sweeps with gates inserted at the arrival of their operands. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped Classical

theorem qmaSweepCircuitFrom_length (rows width start : ℕ) (gs : List QMAGate)
    (h : start+gs.length ≤ rows) :
    (qmaSweepCircuitFrom rows width start gs h).length = (3*(width+1)+1)*gs.length := by
  induction gs generalizing start with
  | nil => simp [qmaSweepCircuitFrom]
  | cons g gs ih =>
    simp only [qmaSweepCircuitFrom,List.length_append,qmaRowStage_length,ih,List.length_cons]
    ring

theorem qmaSweepCircuitFrom_wellFormed (rows width start : ℕ) (gs : List QMAGate)
    (h : start+gs.length ≤ rows) (hg : ∀ g ∈ gs, g.WellFormed (width+1)) :
    ∀ g ∈ qmaSweepCircuitFrom rows width start gs h,
      g.WellFormed (qmaGridWork rows width+1) := by
  induction gs generalizing start with
  | nil => simp [qmaSweepCircuitFrom]
  | cons g gs ih =>
    intro k hk
    have hs : start < rows := by simp only [List.length_cons] at h; omega
    have ht : start+1+gs.length ≤ rows := by simp only [List.length_cons] at h; omega
    rcases List.mem_append.mp hk with hk | hk
    · exact qmaRowStage_wellFormed _ _ _ _ (qmaGridRow_injective rows width _)
        (qmaGridRows_disjoint rows width _ _ (qmaGridRow_ne rows ⟨start,hs⟩))
        _ g (hg g (by simp)) k hk
    · exact ih (start+1) ht (fun k hk => hg k (by simp [hk])) k hk

theorem qmaSweepCircuit_wellFormed (c : QMACircuit) (hc : c.WellFormed) :
    (qmaSweepCircuit c).WellFormed := by
  exact ⟨hc.1.trans (Nat.le_add_right _ _),qmaSweepCircuitFrom_wellFormed _ _ _ _ _ hc.2⟩

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumGridLocality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete polynomial-size verifier with geometrically local computation gates. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaSparseCircuit_wellFormed (c : QMACircuit) (hc : c.WellFormed) :
    (qmaSparseCircuit c).WellFormed :=
  qmaSweepCircuit_wellFormed (qmaNearestCircuit c) (qmaNearestCircuit_wellFormed c hc)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumGateArrival
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The insertion column is an actual operand, so adjacent gates remain close to the sweep. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

def qmaGateArrivalIndex (work : ℕ) (e : Equiv.Perm (Fin (work+1))) (g : QMAGate) :
    Fin (work+1) :=
  ⟨qmaGateCut work e g-1,by
    have h := qmaGateCut_le work e g
    have hp : 0 < qmaGateCut work e g := by unfold qmaGateCut; omega
    omega⟩

def qmaGateArrivalColumn (work : ℕ) (e : Equiv.Perm (Fin (work+1))) (g : QMAGate) :
    Fin (work+1) := e (qmaGateArrivalIndex work e g)

theorem qmaGateArrivalColumn_mem (work : ℕ) (e : Equiv.Perm (Fin (work+1))) (g : QMAGate) :
    qmaGateArrivalColumn work e g ∈ qmaGateSites work g := by
  obtain ⟨i,hi,he⟩ := Finset.exists_mem_eq_sup (qmaGateSites work g)
    (qmaGateSites_nonempty work g) (fun j => (e.symm j).val)
  have heq : qmaGateArrivalIndex work e g = e.symm i := by
    apply Fin.ext
    change (qmaGateSites work g).sup (fun j => (e.symm j).val)+1-1 = _
    omega
  simpa only [qmaGateArrivalColumn,heq,Equiv.apply_symm_apply] using hi

theorem qmaGateArrivalColumn_near (work : ℕ) (e : Equiv.Perm (Fin (work+1)))
    (g : QMAGate) (hg : g.WellFormed (work+1)) (ha : g.Adjacent)
    (i : Fin (work+1)) (hi : i ∈ qmaGateSites work g) :
    i.val ≤ (qmaGateArrivalColumn work e g).val+1 ∧
      (qmaGateArrivalColumn work e g).val ≤ i.val+1 := by
  obtain ⟨lo,hlo⟩ := qmaAdjacentGate_window work g hg ha
  have h1 := hlo i hi
  have h2 := hlo _ (qmaGateArrivalColumn_mem work e g)
  omega

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumTaggedStage
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact labelled row stages with at most four computation gates per column. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

def qmaTaggedRowStage (width work : ℕ)
    (l r : Fin (width+1) → Fin (work+1)) (e : Equiv.Perm (Fin (width+1)))
    (g : QMAGate) : List (QMAGate × Fin (width+1)) :=
  let cols := List.ofFn e
  qmaColumnTransfer l r (cols.take (qmaGateCut width e g)) ++
    [(qmaMapGate width work r g,qmaGateArrivalColumn width e g)] ++
      qmaColumnTransfer l r (cols.drop (qmaGateCut width e g))

theorem qmaTaggedRowStage_gates (width work : ℕ)
    (l r : Fin (width+1) → Fin (work+1)) (e : Equiv.Perm (Fin (width+1)))
    (g : QMAGate) :
    (qmaTaggedRowStage width work l r e g).map Prod.fst = qmaRowStage width work l r e g := by
  have hp : (List.ofFn e).map (fun i => (l i,r i)) = qmaRowPairs (l ∘ e) (r ∘ e) := by
    simp [qmaRowPairs,List.map_ofFn,Function.comp_def]
  simp only [qmaTaggedRowStage,List.map_append,List.map_cons,List.map_nil,
    qmaColumnTransfer_gates,List.map_take,List.map_drop,hp,qmaRowStage]

theorem qmaTaggedRowStage_count (width work : ℕ)
    (l r : Fin (width+1) → Fin (work+1)) (e : Equiv.Perm (Fin (width+1)))
    (g : QMAGate) (j : Fin (width+1)) :
    ((qmaTaggedRowStage width work l r e g).filter (fun p => decide (p.2 = j))).length ≤ 4 := by
  let cols := List.ofFn e
  have hc : (cols.filter (fun i => decide (i = j))).length ≤ 1 :=
    qmaNodup_filter_singleton_length cols (List.nodup_ofFn.mpr e.injective) j
  have hs : ((cols.take (qmaGateCut width e g)).filter (fun i => decide (i = j))).length+
      ((cols.drop (qmaGateCut width e g)).filter (fun i => decide (i = j))).length ≤ 1 := by
    rw [←List.length_append,←List.filter_append,List.take_append_drop]
    exact hc
  simp only [qmaTaggedRowStage,List.filter_append,List.length_append,qmaColumnTransfer_count]
  change 3*((cols.take (qmaGateCut width e g)).filter (fun i => decide (i = j))).length+
      ([(qmaMapGate width work r g,qmaGateArrivalColumn width e g)].filter (fun p => decide (p.2 = j))).length+
      3*((cols.drop (qmaGateCut width e g)).filter (fun i => decide (i = j))).length ≤ 4
  have hi : ([(qmaMapGate width work r g,qmaGateArrivalColumn width e g)].filter (fun p : QMAGate × Fin (width+1) =>
      decide (p.2 = j))).length ≤ 1 := by
    exact le_trans (List.length_filter_le _ _) (by simp)
  omega

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSweepCursor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact sweep cursor around the inserted logical gate. -/

noncomputable section
namespace ContinuumCoulomb

def qmaStageCursorFin (width : ℕ) (e : Equiv.Perm (Fin (width+1))) (g : QMAGate)
    (t : Fin (3*(width+1)+1)) : Fin (width+1) :=
  ⟨qmaStageCursor (qmaGateCut width e g) t.val,
    qmaStageCursor_lt _ _ _ (by unfold qmaGateCut; omega) (qmaGateCut_le width e g) t.isLt⟩

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumTransferIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact time-to-column indexing for the three-gate transfer blocks. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaTaggedRowStage_length (width work : ℕ)
    (l r : Fin (width+1) → Fin (work+1)) (e : Equiv.Perm (Fin (width+1))) (g : QMAGate) :
    (qmaTaggedRowStage width work l r e g).length = 3*(width+1)+1 := by
  have h := congrArg List.length (qmaTaggedRowStage_gates width work l r e g)
  simpa only [List.length_map,qmaRowStage_length] using h

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumStageIndex
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual tagged row-stage column is the explicit insertion cursor. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaTaggedRowStage_get_column (width work : ℕ)
    (l r : Fin (width+1) → Fin (work+1)) (e : Equiv.Perm (Fin (width+1)))
    (g : QMAGate) (t : Fin (3*(width+1)+1)) :
    ((qmaTaggedRowStage width work l r e g)[t.val]'
      (by rw [qmaTaggedRowStage_length]; exact t.isLt)).2 = e (qmaStageCursorFin width e g t) := by
  let cut := qmaGateCut width e g
  let cols := List.ofFn e
  let pre := qmaColumnTransfer l r (cols.take cut)
  let post := qmaColumnTransfer l r (cols.drop cut)
  let ins := (qmaMapGate width work r g,qmaGateArrivalColumn width e g)
  have hc : cut ≤ width+1 := qmaGateCut_le width e g
  have hp : 0 < cut := by dsimp [cut,qmaGateCut]; omega
  have hpre : pre.length = 3*cut := by
    simp only [pre,qmaColumnTransfer_length,List.length_take,cols,List.length_ofFn,Nat.min_eq_left hc]
  have hpost : post.length = 3*(width+1-cut) := by
    simp only [post,qmaColumnTransfer_length,List.length_drop,cols,List.length_ofFn]
  have ht := t.isLt
  have hbound : t.val < ((pre ++ [ins]) ++ post).length := by
    simp only [List.length_append,List.length_singleton,hpre,hpost]
    omega
  change (((pre ++ [ins]) ++ post)[t.val]'hbound).2 = _
  by_cases hb : t.val < 3*cut
  · rw [List.getElem_append_left (by simp only [List.length_append,List.length_singleton,hpre]; omega),
      List.getElem_append_left (by omega)]
    have hsmall : t.val < 3*(cols.take cut).length := by
      simp only [List.length_take,cols,List.length_ofFn,Nat.min_eq_left hc]
      exact hb
    rw [qmaColumnTransfer_get_column l r (cols.take cut) t.val hsmall,List.getElem_take,
      List.getElem_ofFn]
    apply congrArg e
    apply Fin.ext
    simp only [qmaStageCursorFin,Fin.val_mk,qmaStageCursor,cut,hb,ite_true, if_true]
  · by_cases he : t.val = 3*cut
    · rw [List.getElem_append_left (by simp only [List.length_append,List.length_singleton,hpre]; omega),
        List.getElem_append_right (by omega)]
      have hz : t.val-pre.length = 0 := by omega
      simp only [hz,List.getElem_cons_zero]
      change qmaGateArrivalColumn width e g = e (qmaStageCursorFin width e g t)
      apply congrArg e
      apply Fin.ext
      simp only [qmaGateArrivalIndex,qmaStageCursorFin,Fin.val_mk,qmaStageCursor]
      change cut-1 = if t.val < 3*cut then _ else if t.val = 3*cut then _ else _
      simp [he,cut]
    · rw [List.getElem_append_right (by simp only [List.length_append,List.length_singleton,hpre]; omega)]
      have hsmall : t.val-(pre ++ [ins]).length < 3*(cols.drop cut).length := by
        simp only [List.length_append,List.length_singleton,hpre,List.length_drop,cols,List.length_ofFn]
        omega
      rw [qmaColumnTransfer_get_column l r (cols.drop cut) _ hsmall,List.getElem_drop,List.getElem_ofFn]
      apply congrArg e
      apply Fin.ext
      simp only [qmaStageCursorFin,Fin.val_mk,List.length_append,List.length_singleton,hpre]
      change cut+(t.val-(3*cut+1))/3 = qmaStageCursor cut t.val
      unfold qmaStageCursor
      simp only [hb,he,ite_false, if_false]
      omega

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

theorem qmaTaggedRowStage_step (width work row : ℕ)
    (l r : Fin (width+1) → Fin (work+1)) (g : QMAGate) (t : Fin (3*(width+1))) :
    QMALabeledColumnNear
      ((qmaTaggedRowStage width work l r (qmaSweepOrder width row) g)[t.val]'
        (by rw [qmaTaggedRowStage_length]; omega))
      ((qmaTaggedRowStage width work l r (qmaSweepOrder width row) g)[t.val+1]'
        (by rw [qmaTaggedRowStage_length]; omega)) := by
  have hstep := qmaStageCursor_step (qmaGateCut width (qmaSweepOrder width row) g) t.val
    (by unfold qmaGateCut; omega)
  change _ ≤ _ ∧ _ ≤ _
  have h0 := qmaTaggedRowStage_get_column width work l r (qmaSweepOrder width row) g t.castSucc
  have h1 := qmaTaggedRowStage_get_column width work l r (qmaSweepOrder width row) g t.succ
  simp only [Fin.val_castSucc] at h0
  simp only [Fin.val_succ] at h1
  rw [h0,h1]
  apply qmaSweepOrder_near
  · change qmaStageCursor _ t.val ≤ qmaStageCursor _ (t.val+1)+1
    omega
  · exact hstep.2

theorem qmaTaggedRowStage_chain (width work row : ℕ)
    (l r : Fin (width+1) → Fin (work+1)) (g : QMAGate) :
    (qmaTaggedRowStage width work l r (qmaSweepOrder width row) g).IsChain QMALabeledColumnNear := by
  apply List.isChain_iff_getElem.mpr
  intro t ht
  have hlt : t < 3*(width+1) := by rw [qmaTaggedRowStage_length] at ht; omega
  exact qmaTaggedRowStage_step width work row l r g ⟨t,hlt⟩

theorem qmaTaggedRowStage_first_column (width work : ℕ)
    (l r : Fin (width+1) → Fin (work+1)) (e : Equiv.Perm (Fin (width+1))) (g : QMAGate) :
    ((qmaTaggedRowStage width work l r e g)[0]'
      (by rw [qmaTaggedRowStage_length]; omega)).2 = e 0 := by
  have h0 := qmaTaggedRowStage_get_column width work l r e g 0
  simp only [Fin.val_zero] at h0
  rw [h0]
  apply congrArg e
  apply Fin.ext
  change qmaStageCursor (qmaGateCut width e g) 0 = 0
  exact qmaStageCursor_zero _ (by unfold qmaGateCut; omega)

theorem qmaTaggedRowStage_last_column (width work : ℕ)
    (l r : Fin (width+1) → Fin (work+1)) (e : Equiv.Perm (Fin (width+1))) (g : QMAGate) :
    ((qmaTaggedRowStage width work l r e g)[3*(width+1)]'
      (by rw [qmaTaggedRowStage_length]; omega)).2 = e (Fin.last width) := by
  have h0 := qmaTaggedRowStage_get_column width work l r e g (Fin.last (3*(width+1)))
  simp only [Fin.val_last] at h0
  rw [h0]
  apply congrArg e
  apply Fin.ext
  simpa only [qmaStageCursorFin,Fin.val_mk,Fin.val_last,Nat.add_sub_cancel] using
    qmaStageCursor_last (width+1) (qmaGateCut width e g)
      (by unfold qmaGateCut; omega) (qmaGateCut_le width e g)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumTaggedSupport
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every column label gives an explicit bounded spatial support for its gate. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaTaggedRowStage_located (rows width : ℕ) (r : Fin rows)
    (e : Equiv.Perm (Fin (width+1))) (g : QMAGate)
    (hg : g.WellFormed (width+1)) (ha : g.Adjacent)
    (k : QMAGate) (j : Fin (width+1))
    (hk : (k,j) ∈ qmaTaggedRowStage width (qmaGridWork rows width)
      (qmaGridQubit rows width r.castSucc) (qmaGridQubit rows width r.succ) e g) :
    QMALocatedGate rows width r.castSucc j k := by
  simp only [qmaTaggedRowStage,List.mem_append,List.mem_singleton] at hk
  rcases hk with (hk | hk) | hk
  · exact qmaColumnTransfer_located rows width r _ k j hk
  · have he1 := congrArg Prod.fst hk
    have he2 := congrArg Prod.snd hk
    dsimp only at he1 he2
    subst k
    subst j
    intro v hv
    rw [qmaMapGate_sites] at hv
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
    have hn := qmaGateArrivalColumn_near width e g hg ha i hi
    exact ⟨r.succ,i,rfl,by simp,by simp,hn.1,hn.2⟩
  · exact qmaColumnTransfer_located rows width r _ k j hk

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumTaggedSweep
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QMASpatialExchangeModel.withOrdinalSlots_term_index _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal sparse sweep comes with row and column labels. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

def qmaTaggedSweepFrom (rows width : ℕ) :
    (start : ℕ) → (gs : List QMAGate) → start+gs.length ≤ rows →
      List (QMAGate × QMAGridCell rows width)
  | _,[],_ => []
  | start,g::gs,h =>
      (qmaTaggedRowStage width (qmaGridWork rows width)
        (qmaGridQubit rows width ⟨start,by simp only [List.length_cons] at h; omega⟩)
        (qmaGridQubit rows width ⟨start+1,by simp only [List.length_cons] at h; omega⟩)
        (qmaSweepOrder width (rows-1-start)) g).map
          (fun p => (p.1,(⟨start,by simp only [List.length_cons] at h; omega⟩,p.2))) ++
      qmaTaggedSweepFrom rows width (start+1) gs (by simp only [List.length_cons] at h; omega)

theorem qmaTaggedSweepFrom_gates (rows width start : ℕ) (gs : List QMAGate)
    (h : start+gs.length ≤ rows) :
    (qmaTaggedSweepFrom rows width start gs h).map Prod.fst =
      qmaSweepCircuitFrom rows width start gs h := by
  induction gs generalizing start with
  | nil => rfl
  | cons g gs ih =>
    simp only [qmaTaggedSweepFrom,List.map_append,List.map_map,Function.comp_def,
      qmaTaggedRowStage_gates,ih,qmaSweepCircuitFrom]

theorem qmaTaggedSweepFrom_rows (rows width start : ℕ) (gs : List QMAGate)
    (h : start+gs.length ≤ rows) (p : QMAGate × QMAGridCell rows width)
    (hp : p ∈ qmaTaggedSweepFrom rows width start gs h) :
    start ≤ p.2.1.val ∧ p.2.1.val < start+gs.length := by
  induction gs generalizing start with
  | nil => simp [qmaTaggedSweepFrom] at hp
  | cons g gs ih =>
    simp only [qmaTaggedSweepFrom,List.mem_append] at hp
    rcases hp with hp | hp
    · obtain ⟨q,_,hq⟩ := List.mem_map.mp hp
      subst p
      simp only [List.length_cons]
      exact ⟨le_rfl,by omega⟩
    · have hh := ih (start+1) _ hp
      simp only [List.length_cons]
      omega

theorem qmaTaggedSweepFrom_located (rows width start : ℕ) (gs : List QMAGate)
    (h : start+gs.length ≤ rows)
    (hg : ∀ g ∈ gs, g.WellFormed (width+1)) (ha : ∀ g ∈ gs, g.Adjacent)
    (p : QMAGate × QMAGridCell rows width)
    (hp : p ∈ qmaTaggedSweepFrom rows width start gs h) :
    QMALocatedGate rows width p.2.1 p.2.2 p.1 := by
  induction gs generalizing start with
  | nil => simp [qmaTaggedSweepFrom] at hp
  | cons g gs ih =>
    simp only [qmaTaggedSweepFrom,List.mem_append] at hp
    rcases hp with hp | hp
    · obtain ⟨q,hq,hqp⟩ := List.mem_map.mp hp
      subst p
      exact qmaTaggedRowStage_located rows width ⟨start,by simp at h; omega⟩ _ g
        (hg g (by simp)) (ha g (by simp)) q.1 q.2 hq
    · exact ih (start+1) _ (fun g hh => hg g (by simp [hh]))
        (fun g hh => ha g (by simp [hh])) hp

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSweepCongestion
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QMASpatialExchangeModel.withOrdinalSlots_term_index _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete literal sweep has at most four gates assigned to any grid cell. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaTaggedSweepFrom_before (rows width start : ℕ) (gs : List QMAGate)
    (h : start+gs.length ≤ rows) (c : QMAGridCell rows width) (hc : c.1.val < start) :
    ((qmaTaggedSweepFrom rows width start gs h).filter (fun p => decide (p.2 = c))).length = 0 := by
  have he : (qmaTaggedSweepFrom rows width start gs h).filter (fun p => decide (p.2 = c)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro p hp
    simp only [decide_eq_true_eq]
    intro hpc
    have hh := qmaTaggedSweepFrom_rows rows width start gs h p hp
    rw [hpc] at hh
    omega
  rw [he]
  rfl

theorem qmaTaggedSweepFrom_count (rows width start : ℕ) (gs : List QMAGate)
    (h : start+gs.length ≤ rows) (c : QMAGridCell rows width) :
    ((qmaTaggedSweepFrom rows width start gs h).filter (fun p => decide (p.2 = c))).length ≤ 4 := by
  induction gs generalizing start with
  | nil => simp [qmaTaggedSweepFrom]
  | cons g gs ih =>
    rcases c with ⟨q,j⟩
    rw [qmaTaggedSweepFrom,List.filter_append,List.length_append,qmaTagRow_count]
    split_ifs with hr
    · have hq : q.val = start := by rw [←hr]
      rw [qmaTaggedSweepFrom_before rows width (start+1) gs _ (q,j) (by simp [hq]),add_zero]
      exact qmaTaggedRowStage_count _ _ _ _ _ _ _
    · simpa only [zero_add] using ih (start+1) _

def qmaSparseTags (c : QMACircuit) :
    List (QMAGate × QMAGridCell (qmaNearestCircuit c).gates.length c.work) :=
  qmaTaggedSweepFrom (qmaNearestCircuit c).gates.length c.work 0
    (qmaNearestCircuit c).gates (by omega)

theorem qmaSparseTags_gates (c : QMACircuit) :
    (qmaSparseTags c).map Prod.fst = (qmaSparseCircuit c).gates :=
  qmaTaggedSweepFrom_gates _ _ _ _ _

theorem qmaSparseTags_count (c : QMACircuit)
    (p : QMAGridCell (qmaNearestCircuit c).gates.length c.work) :
    ((qmaSparseTags c).filter (fun q => decide (q.2 = p))).length ≤ 4 :=
  qmaTaggedSweepFrom_count _ _ _ _ _ _

theorem qmaSparseTags_located (c : QMACircuit) (hc : c.WellFormed)
    (p : QMAGate × QMAGridCell (qmaNearestCircuit c).gates.length c.work)
    (hp : p ∈ qmaSparseTags c) :
    QMALocatedGate (qmaNearestCircuit c).gates.length c.work p.2.1 p.2.2 p.1 :=
  qmaTaggedSweepFrom_located _ _ _ _ _ (qmaNearestCircuit_wellFormed c hc).2
    (qmaNearestCircuit_adjacent c hc) p hp

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

def qmaGridStageTags (rows width : ℕ) (r : Fin rows) (e : Equiv.Perm (Fin (width+1)))
    (g : QMAGate) : List (QMAGate × QMAGridCell rows width) :=
  qmaRowLift r.castSucc (qmaTaggedRowStage width (qmaGridWork rows width)
    (qmaGridQubit rows width r.castSucc) (qmaGridQubit rows width r.succ) e g)

theorem qmaGridStageTags_nonempty (rows width : ℕ) (r : Fin rows)
    (e : Equiv.Perm (Fin (width+1))) (g : QMAGate) : qmaGridStageTags rows width r e g ≠ [] := by
  intro h
  have hh := congrArg List.length h
  simp only [qmaGridStageTags,qmaRowLift,List.length_map,qmaTaggedRowStage_length,List.length_nil] at hh
  omega

theorem qmaGridStageTags_head (rows width : ℕ) (r : Fin rows)
    (e : Equiv.Perm (Fin (width+1))) (g : QMAGate) :
    (qmaGridStageTags rows width r e g).head?.map Prod.snd = some (r.castSucc,e 0) := by
  let ps := qmaTaggedRowStage width (qmaGridWork rows width)
    (qmaGridQubit rows width r.castSucc) (qmaGridQubit rows width r.succ) e g
  have hp : 0 < ps.length := by rw [qmaTaggedRowStage_length]; omega
  simp only [qmaGridStageTags,qmaRowLift,List.head?_map,Option.map_map,Function.comp_def]
  rw [List.head?_eq_getElem?,List.getElem?_eq_getElem hp]
  simp only [Option.map_some]
  congr 1
  exact Prod.ext rfl (qmaTaggedRowStage_first_column _ _ _ _ _ _)

theorem qmaGridStageTags_last (rows width : ℕ) (r : Fin rows)
    (e : Equiv.Perm (Fin (width+1))) (g : QMAGate) :
    (qmaGridStageTags rows width r e g).getLast?.map Prod.snd = some (r.castSucc,e (Fin.last width)) := by
  let ps := qmaTaggedRowStage width (qmaGridWork rows width)
    (qmaGridQubit rows width r.castSucc) (qmaGridQubit rows width r.succ) e g
  have hp : 3*(width+1) < ps.length := by rw [qmaTaggedRowStage_length]; omega
  simp only [qmaGridStageTags,qmaRowLift,List.getLast?_map,Option.map_map,Function.comp_def]
  rw [List.getLast?_eq_getElem?]
  simp only [qmaTaggedRowStage_length,Nat.add_sub_cancel]
  rw [List.getElem?_eq_getElem hp]
  simp only [Option.map_some]
  congr 1
  exact Prod.ext rfl (qmaTaggedRowStage_last_column _ _ _ _ _ _)

theorem qmaGridStageTags_chain (rows width : ℕ) (r : Fin rows) (g : QMAGate) :
    (qmaGridStageTags rows width r (qmaSweepOrder width (rows-1-r.val)) g).IsChain QMAGridTagNear :=
  qmaRowLift_chain _ _ (qmaTaggedRowStage_chain _ _ _ _ _ _)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumClockPath
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QMASpatialExchangeModel.withOrdinalSlots_term_index _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full literal clock path has bounded steps, including every row transition. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaTaggedSweepFrom_head (rows width start : ℕ) (g : QMAGate) (gs : List QMAGate)
    (h : start+(g::gs).length ≤ rows) :
    (qmaTaggedSweepFrom rows width start (g::gs) h).head?.map Prod.snd =
      some ((⟨start,by simp only [List.length_cons] at h; omega⟩ : Fin (rows+1)),
        qmaSweepOrder width (rows-1-start) 0) := by
  have hs : start < rows := by simp only [List.length_cons] at h; omega
  change ((qmaGridStageTags rows width ⟨start,hs⟩ (qmaSweepOrder width (rows-1-start)) g) ++
    qmaTaggedSweepFrom rows width (start+1) gs _).head?.map Prod.snd = _
  rw [List.head?_append_of_ne_nil _ (qmaGridStageTags_nonempty _ _ _ _ _)]
  exact qmaGridStageTags_head _ _ _ _ _

theorem qmaTaggedSweepFrom_chain (rows width start : ℕ) (gs : List QMAGate)
    (h : start+gs.length ≤ rows) :
    (qmaTaggedSweepFrom rows width start gs h).IsChain QMAGridTagNear := by
  induction gs generalizing start with
  | nil => exact List.IsChain.nil
  | cons g gs ih =>
    have hs : start < rows := by simp only [List.length_cons] at h; omega
    let r : Fin rows := ⟨start,hs⟩
    change (qmaGridStageTags rows width r (qmaSweepOrder width (rows-1-start)) g ++
      qmaTaggedSweepFrom rows width (start+1) gs _).IsChain QMAGridTagNear
    apply List.IsChain.append (qmaGridStageTags_chain rows width r g) (ih (start+1) _)
    intro x hx y hy
    cases gs with
    | nil => simp [qmaTaggedSweepFrom] at hy
    | cons g' gs' =>
      have hlast := qmaGridStageTags_last rows width r (qmaSweepOrder width (rows-1-start)) g
      have hhead := qmaTaggedSweepFrom_head rows width (start+1) g' gs' (by
        simp only [List.length_cons] at h ⊢; omega)
      have hx' := Option.mem_map_of_mem Prod.snd hx
      have hy' := Option.mem_map_of_mem Prod.snd hy
      rw [hlast] at hx'
      rw [hhead] at hy'
      have hxc := (Option.mem_some_iff.mp hx').symm
      have hyc := (Option.mem_some_iff.mp hy').symm
      have hrow : 0 < rows-1-start := by simp only [List.length_cons] at h; omega
      have hturn := qmaSweepOrder_turn width (rows-1-start) hrow
      have he : rows-1-start-1 = rows-1-(start+1) := by omega
      rw [he] at hturn
      unfold QMAGridTagNear
      rw [hxc,hyc]
      change start ≤ start+1+1 ∧ start+1 ≤ start+1 ∧
        (qmaSweepOrder width (rows-1-start) (Fin.last width)).val ≤
          (qmaSweepOrder width (rows-1-(start+1)) 0).val+1 ∧
        (qmaSweepOrder width (rows-1-(start+1)) 0).val ≤
          (qmaSweepOrder width (rows-1-start) (Fin.last width)).val+1
      rw [hturn]
      exact ⟨by omega,le_rfl,by omega,by omega⟩

theorem qmaSparseTags_chain (c : QMACircuit) : (qmaSparseTags c).IsChain QMAGridTagNear :=
  qmaTaggedSweepFrom_chain _ _ _ _ _

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSweepCoverage
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every physical row is touched in a nonempty sweep, including the final row. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaRowStage_containsSwap (width work : ℕ)
    (l r : Fin (width+1) → Fin (work+1)) (e : Equiv.Perm (Fin (width+1)))
    (g k : QMAGate) (i : Fin (width+1)) (hk : k ∈ qmaWireSwapGates (l i) (r i)) :
    k ∈ qmaRowStage width work l r e g := by
  let ps := qmaRowPairs (l ∘ e) (r ∘ e)
  have hp : (l i,r i) ∈ ps := by
    exact List.mem_ofFn.mpr ⟨e.symm i,by simp⟩
  have hcases : (l i,r i) ∈ ps.take (qmaGateCut width e g) ∨
      (l i,r i) ∈ ps.drop (qmaGateCut width e g) := by
    rw [←List.mem_append,List.take_append_drop]
    exact hp
  change k ∈ qmaTransferGates (ps.take (qmaGateCut width e g)) ++ [_] ++
    qmaTransferGates (ps.drop (qmaGateCut width e g))
  rcases hcases with hp | hp
  · exact List.mem_append_left _ (List.mem_append_left _
      ((qmaTransferGates_member _ k).mpr ⟨_,hp,hk⟩))
  · exact List.mem_append_right _ ((qmaTransferGates_member _ k).mpr ⟨_,hp,hk⟩)

theorem qmaGridStage_touches (rows width : ℕ) (r : Fin rows)
    (e : Equiv.Perm (Fin (width+1))) (g : QMAGate) (j : Fin (width+1)) :
    ∃ k ∈ qmaRowStage width (qmaGridWork rows width)
      (qmaGridQubit rows width r.castSucc) (qmaGridQubit rows width r.succ) e g,
      qmaGridQubit rows width r.castSucc j ∈ qmaGateSites (qmaGridWork rows width) k ∧
      qmaGridQubit rows width r.succ j ∈ qmaGateSites (qmaGridWork rows width) k := by
  let a := qmaGridQubit rows width r.castSucc j
  let b := qmaGridQubit rows width r.succ j
  refine ⟨.controlledNot a.val b.val,?_,?_⟩
  · apply qmaRowStage_containsSwap _ _ _ _ _ g _ j
    simp [qmaWireSwapGates,a,b]
  · simp [qmaGateSites,qmaQubit_fin,a,b]

theorem qmaSweepCircuitFrom_touches (rows width start : ℕ) (gs : List QMAGate)
    (h : start+gs.length ≤ rows) (hne : gs ≠ [])
    (q : Fin (rows+1)) (hq : start ≤ q.val) (hq' : q.val ≤ start+gs.length)
    (j : Fin (width+1)) :
    ∃ k ∈ qmaSweepCircuitFrom rows width start gs h,
      qmaGridQubit rows width q j ∈ qmaGateSites (qmaGridWork rows width) k := by
  induction gs generalizing start with
  | nil => exact False.elim (hne rfl)
  | cons g gs ih =>
    have hs : start < rows := by simp only [List.length_cons] at h; omega
    by_cases hnear : q.val ≤ start+1
    · obtain ⟨k,hk,hl,hr⟩ := qmaGridStage_touches rows width ⟨start,hs⟩
        (qmaSweepOrder width (rows-1-start)) g j
      refine ⟨k,List.mem_append_left _ hk,?_⟩
      have hqcases : q = (⟨start,hs⟩ : Fin rows).castSucc ∨
          q = (⟨start,hs⟩ : Fin rows).succ := by
        have : q.val = start ∨ q.val = start+1 := by omega
        exact this.imp (fun h => Fin.ext h) (fun h => Fin.ext h)
      rcases hqcases with rfl | rfl
      · exact hl
      · exact hr
    · have htail : gs ≠ [] := by
        intro he
        simp only [he,List.length_cons,List.length_nil] at hq'
        omega
      obtain ⟨k,hk,hv⟩ := ih (start+1) (by simp only [List.length_cons] at h; omega)
        htail (by omega) (by simp only [List.length_cons] at hq'; omega)
      exact ⟨k,List.mem_append_right _ hk,hv⟩

theorem qmaSweepCircuit_touches (c : QMACircuit) (hne : c.gates ≠ [])
    (i : Fin ((qmaSweepCircuit c).work+1)) :
    ∃ g ∈ (qmaSweepCircuit c).gates, i ∈ qmaGateSites (qmaSweepCircuit c).work g := by
  obtain ⟨⟨r,j⟩,he⟩ := qmaGridQubit_surjective c.gates.length c.work i
  rw [←he]
  exact qmaSweepCircuitFrom_touches _ _ _ _ _ hne r (by omega) (by have := r.isLt; omega) j

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFirstUseSites
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! First-use initialization contributes at most two qubits at each gate time. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

def qmaFirstUseSites (c : QMACircuit) (t : Fin c.gates.length) : Finset (Fin (c.work+1)) :=
  Finset.univ.filter (fun i => qmaFirstUse c i = t.val)

theorem qmaFirstUseSites_subset (c : QMACircuit) (t : Fin c.gates.length) :
    qmaFirstUseSites c t ⊆ qmaGateSites c.work c.gates[t.val] := by
  intro i hi
  have he := (Finset.mem_filter.mp hi).2
  have ht : qmaFirstUse c i < c.gates.length := he.symm ▸ t.isLt
  have hh := List.findIdx_getElem (p := fun g => decide (i ∈ qmaGateSites c.work g))
    (xs := c.gates) (w := ht)
  change decide (i ∈ qmaGateSites c.work c.gates[qmaFirstUse c i]) = true at hh
  simpa only [he,decide_eq_true_eq] using hh

theorem qmaFirstUseSites_card (c : QMACircuit) (t : Fin c.gates.length) :
    (qmaFirstUseSites c t).card ≤ 2 :=
  (Finset.card_le_card (qmaFirstUseSites_subset c t)).trans (qmaGateSites_card _ _)

theorem qmaFirstUse_lt_of_touched (c : QMACircuit) (i : Fin (c.work+1))
    (h : ∃ g ∈ c.gates, i ∈ qmaGateSites c.work g) : qmaFirstUse c i < c.gates.length := by
  apply List.findIdx_lt_length_of_exists
  simpa only [decide_eq_true_eq] using h

theorem qmaSweepFirstUse_lt (c : QMACircuit) (hne : c.gates ≠ [])
    (i : Fin ((qmaSweepCircuit c).work+1)) :
    qmaFirstUse (qmaSweepCircuit c) i < (qmaSweepCircuit c).gates.length :=
  qmaFirstUse_lt_of_touched _ _ (qmaSweepCircuit_touches c hne i)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSparseFirstUse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! First-use input checks inherit the actual sweep geometry and constant congestion. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

theorem qmaSparseTags_length (c : QMACircuit) :
    (qmaSparseTags c).length = (qmaSparseCircuit c).gates.length := by
  have h := congrArg List.length (qmaSparseTags_gates c)
  simpa only [List.length_map] using h

def qmaSparseTime (c : QMACircuit) (t : Fin (qmaSparseTags c).length) :
    Fin (qmaSparseCircuit c).gates.length := t.cast (qmaSparseTags_length c)

def qmaSparseCell (c : QMACircuit) (t : Fin (qmaSparseTags c).length) :
    QMAGridCell (qmaNearestCircuit c).gates.length c.work := (qmaSparseTags c)[t.val].2

theorem qmaSparseTag_gate (c : QMACircuit) (t : Fin (qmaSparseTags c).length) :
    (qmaSparseTags c)[t.val].1 = (qmaSparseCircuit c).gates[(qmaSparseTime c t).val] := by
  have ht : t.val < (qmaSparseCircuit c).gates.length := by
    rw [←qmaSparseTags_length]
    exact t.isLt
  have hm : ((qmaSparseTags c)[t.val]?).map Prod.fst = (qmaSparseCircuit c).gates[t.val]? := by
    rw [←List.getElem?_map,qmaSparseTags_gates]
  simpa only [List.getElem?_eq_getElem t.isLt,List.getElem?_eq_getElem ht,
    Option.map_some,Option.some.injEq,qmaSparseTime,Fin.val_cast] using hm

def qmaSparseCellTimes (c : QMACircuit)
    (p : QMAGridCell (qmaNearestCircuit c).gates.length c.work) : Finset (Fin (qmaSparseTags c).length) :=
  Finset.univ.filter (fun t => qmaSparseCell c t = p)

theorem qmaSparseCellTimes_card (c : QMACircuit)
    (p : QMAGridCell (qmaNearestCircuit c).gates.length c.work) :
    (qmaSparseCellTimes c p).card ≤ 4 := by
  have he := qmaList_filter_index_card (qmaSparseTags c) (fun q => decide (q.2 = p))
  change (Finset.univ.filter (fun t : Fin (qmaSparseTags c).length =>
    (qmaSparseTags c)[t.val].2 = p)).card ≤ 4
  simpa only [decide_eq_true_eq] using he.trans_le (qmaSparseTags_count c p)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumClockCells
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QMASpatialExchangeModel.withOrdinalSlots_term_index _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual unary clock bits stay next to their computation gates with bounded cell occupancy. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

def qmaSparseGateCell (c : QMACircuit) (t : Fin (qmaSparseCircuit c).gates.length) :
    QMAGridCell (qmaNearestCircuit c).gates.length c.work :=
  qmaSparseCell c (t.cast (qmaSparseTags_length c).symm)

def qmaSparseClockCell (c : QMACircuit) (hT : 0 < (qmaSparseCircuit c).gates.length)
    (b : Fin ((qmaSparseCircuit c).gates.length+2)) :
    QMAGridCell (qmaNearestCircuit c).gates.length c.work :=
  qmaSparseGateCell c (qmaClockAnchorIndex _ hT b)

theorem qmaSparseGateCells_near (c : QMACircuit) (i j : Fin (qmaSparseCircuit c).gates.length)
    (hij : i.val ≤ j.val+1) (hji : j.val ≤ i.val+1) :
    QMAGridCellsNear (qmaSparseGateCell c i) (qmaSparseGateCell c j) := by
  exact qmaGridTagChain_near (qmaSparseTags c) (qmaSparseTags_chain c)
    (i.cast (qmaSparseTags_length c).symm) (j.cast (qmaSparseTags_length c).symm) hij hji

theorem qmaSparseClockCells_near_gate (c : QMACircuit) (hT : 0 < (qmaSparseCircuit c).gates.length)
    (t : Fin (qmaSparseCircuit c).gates.length) (b : Fin ((qmaSparseCircuit c).gates.length+2))
    (hb : t.val ≤ b.val ∧ b.val ≤ t.val+2) :
    QMAGridCellsNear (qmaSparseClockCell c hT b) (qmaSparseGateCell c t) :=
  qmaSparseGateCells_near c _ t (qmaClockAnchorIndex_near _ hT t b hb).1
    (qmaClockAnchorIndex_near _ hT t b hb).2

def qmaSparseClockCellBits (c : QMACircuit) (hT : 0 < (qmaSparseCircuit c).gates.length)
    (p : QMAGridCell (qmaNearestCircuit c).gates.length c.work) :
    Finset (Fin ((qmaSparseCircuit c).gates.length+2)) :=
  (qmaSparseCellTimes c p).biUnion (fun t => Finset.univ.filter
    (fun b => qmaClockAnchorIndex _ hT b = qmaSparseTime c t))

theorem qmaSparseClockCellBits_card (c : QMACircuit) (hT : 0 < (qmaSparseCircuit c).gates.length)
    (p : QMAGridCell (qmaNearestCircuit c).gates.length c.work) :
    (qmaSparseClockCellBits c hT p).card ≤ 12 := by
  calc
    _ ≤ ∑ t ∈ qmaSparseCellTimes c p, (Finset.univ.filter
        (fun b => qmaClockAnchorIndex _ hT b = qmaSparseTime c t)).card := Finset.card_biUnion_le
    _ ≤ ∑ _t ∈ qmaSparseCellTimes c p, 3 :=
      Finset.sum_le_sum (fun t _ => qmaClockAnchorIndex_fiber_card _ hT (qmaSparseTime c t))
    _ = (qmaSparseCellTimes c p).card*3 := by simp
    _ ≤ 12 := by have := qmaSparseCellTimes_card c p; omega

theorem qmaSparseClockCellBits_mem (c : QMACircuit) (hT : 0 < (qmaSparseCircuit c).gates.length)
    (b : Fin ((qmaSparseCircuit c).gates.length+2)) :
    b ∈ qmaSparseClockCellBits c hT (qmaSparseClockCell c hT b) := by
  let t := (qmaClockAnchorIndex _ hT b).cast (qmaSparseTags_length c).symm
  apply Finset.mem_biUnion.mpr
  refine ⟨t,?_,?_⟩
  · simp only [qmaSparseCellTimes,Finset.mem_filter,Finset.mem_univ,true_and]
    rfl
  · simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    apply Fin.ext
    rfl

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumGridCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit row/column coordinates for every physical computation qubit. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

def qmaSparseWorkCell (c : QMACircuit) (i : Fin ((qmaSparseCircuit c).work+1)) :
    QMAGridCell (qmaNearestCircuit c).gates.length c.work :=
  qmaGridCoordinates (qmaNearestCircuit c).gates.length c.work i

theorem qmaSparseWorkCell_near_gate (c : QMACircuit) (hc : c.WellFormed)
    (t : Fin (qmaSparseCircuit c).gates.length) (i : Fin ((qmaSparseCircuit c).work+1))
    (hi : i ∈ qmaGateSites (qmaSparseCircuit c).work (qmaSparseCircuit c).gates[t.val]) :
    QMAGridCellsNear (qmaSparseWorkCell c i) (qmaSparseGateCell c t) := by
  let u := t.cast (qmaSparseTags_length c).symm
  have hu : qmaSparseTime c u = t := by apply Fin.ext; rfl
  rw [←hu,←qmaSparseTag_gate] at hi
  obtain ⟨r,j,he,hl,hr,hj,hj'⟩ :=
    qmaSparseTags_located c hc _ (List.getElem_mem u.isLt) i hi
  unfold qmaSparseWorkCell
  rw [he,qmaGridCoordinates_left]
  change r.val ≤ (qmaSparseCell c u).1.val+1 ∧
    (qmaSparseCell c u).1.val ≤ r.val+1 ∧
    j.val ≤ (qmaSparseCell c u).2.val+1 ∧ (qmaSparseCell c u).2.val ≤ j.val+1
  exact ⟨hr,hl.trans (Nat.le_succ _),hj,hj'⟩

def qmaSparseQubitCell (c : QMACircuit) (hT : 0 < (qmaSparseCircuit c).gates.length) :
    QMACircuitQubit (qmaSparseCircuit c) → QMAGridCell (qmaNearestCircuit c).gates.length c.work
  | .inl b => qmaSparseClockCell c hT b
  | .inr i => qmaSparseWorkCell c i

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSpatialPropagation
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every actual propagation interaction is contained near its computation-gate anchor. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaSparsePropagation_cell (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0 < (qmaSparseCircuit c).gates.length) (t : Fin (qmaSparseCircuit c).gates.length)
    (k : QMACircuitQubit (qmaSparseCircuit c)) (hk : k ∈ qmaPropagationSites (qmaSparseCircuit c) t) :
    QMAGridCellsNear (qmaSparseQubitCell c hT k) (qmaSparseGateCell c t) := by
  cases k with
  | inl b =>
    have hb : b = qmaClockLeft _ t ∨ b = qmaClockMiddle _ t ∨ b = qmaClockRight _ t := by
      simpa [qmaPropagationSites] using hk
    rcases hb with rfl | rfl | rfl
    · exact qmaSparseClockCells_near_gate c hT t _ ⟨le_rfl,by simp [qmaClockLeft]⟩
    · apply qmaSparseClockCells_near_gate c hT t
      simp [qmaClockMiddle]
    · apply qmaSparseClockCells_near_gate c hT t
      simp [qmaClockRight]
  | inr i =>
    apply qmaSparseWorkCell_near_gate c hc t i
    have hi : i ∈ qmaGateSites (qmaSparseCircuit c).work
        ((qmaSparseCircuit c).gates.getD t.val (.hadamard 0)) := by
      simpa [qmaPropagationSites] using hk
    simpa only [List.getD_eq_getElem _ _ t.isLt] using hi

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSpatialInput
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Both clock bits and the initialized qubit are near the first-use gate. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaSparseInput_cell (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0 < (qmaSparseCircuit c).gates.length) (i : Fin ((qmaSparseCircuit c).work+1))
    (ht : qmaFirstUse (qmaSparseCircuit c) i < (qmaSparseCircuit c).gates.length)
    (k : QMACircuitQubit (qmaSparseCircuit c))
    (hk : k ∈ qmaDistributedInputSites (qmaSparseCircuit c) (qmaFirstUseTime (qmaSparseCircuit c)) i) :
    QMAGridCellsNear (qmaSparseQubitCell c hT k)
      (qmaSparseGateCell c ⟨qmaFirstUse (qmaSparseCircuit c) i,ht⟩) := by
  let t : Fin (qmaSparseCircuit c).gates.length := ⟨qmaFirstUse (qmaSparseCircuit c) i,ht⟩
  cases k with
  | inl b =>
    have hb : b = (qmaFirstUseTime (qmaSparseCircuit c) i).castSucc ∨
        b = (qmaFirstUseTime (qmaSparseCircuit c) i).succ := by
      simpa [qmaDistributedInputSites] using hk
    rcases hb with rfl | rfl
    · apply qmaSparseClockCells_near_gate c hT t
      change t.val ≤ t.val ∧ t.val ≤ t.val+2
      omega
    · apply qmaSparseClockCells_near_gate c hT t
      change t.val ≤ t.val+1 ∧ t.val+1 ≤ t.val+2
      omega
  | inr j =>
    have hj : j = i := by simpa [qmaDistributedInputSites] using hk
    subst j
    apply qmaSparseWorkCell_near_gate c hc t i
    apply qmaFirstUseSites_subset
    simp only [qmaFirstUseSites,Finset.mem_filter,Finset.mem_univ,true_and]
    rfl

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedReference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A consecutive reference label for the time-ordered actual interaction family. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

def qmaOrderedSparseReferenceCell (c : QMACircuit)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (i : Fin (qmaHistoryReferenceWork (qmaSparseCircuit c)+1)) :
    QMAGridCell (qmaNearestCircuit c).gates.length c.work :=
  qmaSparseGateCell c (qmaOrderedReferenceTime (qmaSparseCircuit c) hT
    (qmaFirstUseTime (qmaSparseCircuit c)) i)

theorem qmaOrderedSparseReferenceCell_near (c : QMACircuit)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (i : Fin (qmaHistoryReferenceWork (qmaSparseCircuit c))) :
    QMAGridCellsNear (qmaOrderedSparseReferenceCell c hT i.castSucc)
      (qmaOrderedSparseReferenceCell c hT i.succ) := by
  have h := qmaOrderedReferenceTime_step (qmaSparseCircuit c) hT
    (qmaFirstUseTime (qmaSparseCircuit c)) i
  exact qmaSparseGateCells_near c _ _ (by omega) h.2

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumTimeCongestion
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! At most eight actual interaction terms are assigned to any clock time. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

theorem qmaHistoryTimeFiber_card (c : QMACircuit) (hT : 0 < c.gates.length)
    (hi : ∀ i, qmaFirstUse c i < c.gates.length) (t : Fin c.gates.length) :
    (Finset.univ.filter (fun a : QMACircuitTerm c =>
      qmaHistoryTermTime c hT (qmaFirstUseTime c) a = t)).card ≤ 8 := by
  have hclock := qmaBoundedClockTime_fiber_card c.gates.length hT t
  have hboundary : (Finset.univ.filter (fun b : Fin 2 =>
      (if b = 0 then (⟨0,hT⟩ : Fin c.gates.length)
      else qmaBoundedClockTime _ hT c.gates.length) = t)).card ≤ 2 := by
    exact (Finset.card_filter_le _ _).trans (by simp)
  have hinput : (Finset.univ.filter (fun i : Fin (c.work+1) =>
      qmaBoundedClockTime _ hT (qmaFirstUse c i) = t)).card ≤ 2 := by
    apply le_trans (Finset.card_le_card (show _ ⊆ qmaFirstUseSites c t from ?_))
      (qmaFirstUseSites_card c t)
    intro i hm
    have hv := congrArg Fin.val (Finset.mem_filter.mp hm).2
    change min (qmaFirstUse c i) (c.gates.length-1) = t.val at hv
    simp only [qmaFirstUseSites,Finset.mem_filter,Finset.mem_univ,true_and]
    have := hi i
    omega
  have houtput : (Finset.univ.filter (fun _ : Unit =>
      qmaBoundedClockTime _ hT c.gates.length = t)).card ≤ 1 := by
    exact (Finset.card_filter_le _ _).trans (by simp)
  have hprop : (Finset.univ.filter (fun u : Fin c.gates.length => u = t)).card ≤ 1 := by
    have hs : (Finset.univ.filter (fun u : Fin c.gates.length => u = t)) ⊆
        ({t} : Finset (Fin c.gates.length)) := by
      intro u hu
      simpa only [Finset.mem_singleton] using (Finset.mem_filter.mp hu).2
    exact (Finset.card_le_card hs).trans (by simp)
  change (Finset.univ.filter (fun a :
    Fin (c.gates.length+1) ⊕ (Fin 2 ⊕ (Fin (c.work+1) ⊕ (Unit ⊕ Fin c.gates.length))) =>
    qmaHistoryTermTime c hT (qmaFirstUseTime c) a = t)).card ≤ 8
  rw [qmaSumFilter_card,qmaSumFilter_card,qmaSumFilter_card,qmaSumFilter_card]
  simp only [qmaHistoryTermTime]
  exact (Nat.add_le_add hclock (Nat.add_le_add hboundary
    (Nat.add_le_add hinput (Nat.add_le_add houtput hprop)))).trans (by decide)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumReferenceCongestion
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QMASpatialExchangeModel.withOrdinalSlots_term_index _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Time ordering gives a constant number of reference qubits per spatial cell. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

theorem qmaOrderedReferenceTime_fiber_card (c : QMACircuit) (hT : 0 < c.gates.length)
    (hi : ∀ i, qmaFirstUse c i < c.gates.length) (t : Fin c.gates.length) :
    (Finset.univ.filter (fun i => qmaOrderedReferenceTime c hT (qmaFirstUseTime c) i = t)).card ≤ 8 := by
  calc
    _ = (Finset.univ.filter (fun a : QMACircuitTerm c =>
        qmaHistoryTermTime c hT (qmaFirstUseTime c) a = t)).card := by
      apply Finset.card_equiv (qmaOrderedTermEquiv c hT (qmaFirstUseTime c))
      intro i
      constructor
      · intro hm
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hm).2⟩
      · intro hm
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hm).2⟩
    _ ≤ 8 := qmaHistoryTimeFiber_card c hT hi t

def qmaSparseReferenceCellIndices (c : QMACircuit)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (p : QMAGridCell (qmaNearestCircuit c).gates.length c.work) :
    Finset (Fin (qmaHistoryReferenceWork (qmaSparseCircuit c)+1)) :=
  (qmaSparseCellTimes c p).biUnion (fun t => Finset.univ.filter
    (fun i => qmaOrderedReferenceTime (qmaSparseCircuit c) hT
      (qmaFirstUseTime (qmaSparseCircuit c)) i = qmaSparseTime c t))

theorem qmaSparseReferenceCellIndices_card (c : QMACircuit)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates ≠ [])
    (p : QMAGridCell (qmaNearestCircuit c).gates.length c.work) :
    (qmaSparseReferenceCellIndices c hT p).card ≤ 32 := by
  calc
    _ ≤ ∑ t ∈ qmaSparseCellTimes c p, (Finset.univ.filter
        (fun i => qmaOrderedReferenceTime (qmaSparseCircuit c) hT
          (qmaFirstUseTime (qmaSparseCircuit c)) i = qmaSparseTime c t)).card := Finset.card_biUnion_le
    _ ≤ ∑ _t ∈ qmaSparseCellTimes c p, 8 := by
      apply Finset.sum_le_sum
      intro t _
      exact qmaOrderedReferenceTime_fiber_card _ hT (qmaSweepFirstUse_lt _ hne) _
    _ = (qmaSparseCellTimes c p).card*8 := by simp
    _ ≤ 32 := by have := qmaSparseCellTimes_card c p; omega

theorem qmaSparseReferenceCellIndices_mem (c : QMACircuit)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (i : Fin (qmaHistoryReferenceWork (qmaSparseCircuit c)+1)) :
    i ∈ qmaSparseReferenceCellIndices c hT (qmaOrderedSparseReferenceCell c hT i) := by
  let t := (qmaOrderedReferenceTime (qmaSparseCircuit c) hT
    (qmaFirstUseTime (qmaSparseCircuit c)) i).cast (qmaSparseTags_length c).symm
  apply Finset.mem_biUnion.mpr
  refine ⟨t,?_,?_⟩
  · simp only [qmaSparseCellTimes,Finset.mem_filter,Finset.mem_univ,true_and]
    rfl
  · simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    apply Fin.ext
    rfl

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSweepEndpoint
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QMASpatialExchangeModel.withOrdinalSlots_term_index _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The last clock cell lies beside the measured output on the final sweep row. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaTaggedSweepFrom_last (rows width start : ℕ) (g : QMAGate) (gs : List QMAGate)
    (h : start+(g::gs).length ≤ rows) :
    (qmaTaggedSweepFrom rows width start (g::gs) h).getLast?.map Prod.snd =
      some ((⟨start+gs.length,by simp only [List.length_cons] at h; omega⟩ : Fin (rows+1)),
        qmaSweepOrder width (rows-1-start-gs.length) (Fin.last width)) := by
  induction gs generalizing start g with
  | nil =>
    have hs : start < rows := by simp only [List.length_cons,List.length_nil] at h; omega
    change ((qmaGridStageTags rows width ⟨start,hs⟩ (qmaSweepOrder width (rows-1-start)) g) ++
      []).getLast?.map Prod.snd = _
    simp only [List.append_nil]
    exact qmaGridStageTags_last rows width ⟨start,hs⟩ _ g
  | cons g' gs ih =>
    have hs : start < rows := by simp only [List.length_cons] at h; omega
    change ((qmaGridStageTags rows width ⟨start,hs⟩ (qmaSweepOrder width (rows-1-start)) g) ++
      qmaTaggedSweepFrom rows width (start+1) (g'::gs) _).getLast?.map Prod.snd = _
    have ht : start+1+(g'::gs).length ≤ rows := by
      simp only [List.length_cons] at h ⊢; omega
    have hlast := ih (start+1) g' ht
    have hne : (qmaTaggedSweepFrom rows width (start+1) (g'::gs) ht).getLast? ≠ none := by
      intro he
      rw [he] at hlast
      simp at hlast
    rw [List.getLast?_append,Option.or_eq_left_of_isSome (Option.isSome_iff_ne_none.mpr hne)]
    have he : rows-1-(start+1)-gs.length = rows-1-start-(gs.length+1) := by omega
    rw [hlast]
    simp only [List.length_cons]
    rw [he]
    congr 2
    apply Fin.ext
    dsimp only
    omega

theorem qmaTaggedSweepFrom_last_nonempty (rows width start : ℕ) (gs : List QMAGate)
    (h : start+gs.length ≤ rows) (hne : gs ≠ []) :
    (qmaTaggedSweepFrom rows width start gs h).getLast?.map Prod.snd =
      some ((⟨start+gs.length-1,by have := List.length_pos_iff.mpr hne; omega⟩ : Fin (rows+1)),
        qmaSweepOrder width (rows-start-gs.length) (Fin.last width)) := by
  cases gs with
  | nil => exact (hne rfl).elim
  | cons g gs =>
    have hr : start+(g::gs).length-1 = start+gs.length := by
      simp only [List.length_cons]; omega
    have he : rows-start-(g::gs).length = rows-1-start-gs.length := by
      simp only [List.length_cons]; omega
    simpa only [hr,he] using qmaTaggedSweepFrom_last rows width start g gs h

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSparseEndpoint
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QMASpatialExchangeModel.withOrdinalSlots_term_index _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The last physical gate sits immediately above the output qubit. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaSparseTags_last (c : QMACircuit)
    (hT : 0 < (qmaSparseCircuit c).gates.length) :
    (qmaSparseTags c).getLast?.map Prod.snd = some
      ((⟨(qmaNearestCircuit c).gates.length-1,by omega⟩ :
        Fin ((qmaNearestCircuit c).gates.length+1)),Fin.last c.work) := by
  have hn : (qmaNearestCircuit c).gates ≠ [] := by
    intro he
    have hl := qmaSweepCircuitFrom_length (qmaNearestCircuit c).gates.length c.work 0
      (qmaNearestCircuit c).gates (by omega)
    change (qmaSparseCircuit c).gates.length = _ at hl
    rw [hl,he] at hT
    simp at hT
  have hl := qmaTaggedSweepFrom_last_nonempty (qmaNearestCircuit c).gates.length c.work 0
    (qmaNearestCircuit c).gates (by omega) hn
  simpa only [qmaSparseTags,Nat.zero_add,Nat.sub_zero,Nat.sub_self,qmaSweepOrder,
    Nat.zero_mod,ite_true, if_true,Equiv.refl_apply] using hl

theorem qmaSparseGateCell_last (c : QMACircuit)
    (hT : 0 < (qmaSparseCircuit c).gates.length) :
    qmaSparseGateCell c ⟨(qmaSparseCircuit c).gates.length-1,by omega⟩ =
      ((⟨(qmaNearestCircuit c).gates.length-1,by omega⟩ :
        Fin ((qmaNearestCircuit c).gates.length+1)),Fin.last c.work) := by
  have hl := qmaSparseTags_last c hT
  have hlen := qmaSparseTags_length c
  have hb : (qmaSparseTags c).length-1 < (qmaSparseTags c).length := by omega
  rw [List.getLast?_eq_getElem?,List.getElem?_eq_getElem hb] at hl
  simp only [Option.map_some,Option.some.injEq] at hl
  unfold qmaSparseGateCell qmaSparseCell
  simpa only [Fin.val_cast,hlen] using hl

theorem qmaSparseWorkCell_last (c : QMACircuit) :
    qmaSparseWorkCell c (Fin.last (qmaSparseCircuit c).work) =
      (Fin.last (qmaNearestCircuit c).gates.length,Fin.last c.work) := by
  change qmaGridCoordinates (qmaNearestCircuit c).gates.length c.work
    (Fin.last (qmaGridWork (qmaNearestCircuit c).gates.length c.work)) = _
  rw [←qmaGridQubit_last,qmaGridCoordinates_left]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSpatialClockTerms
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Clock faults and endpoint pins are close to their assigned history time. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaSparseClockFault_cell (c : QMACircuit)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (i : Fin ((qmaSparseCircuit c).gates.length+1))
    (k : QMACircuitQubit (qmaSparseCircuit c))
    (hk : k ∈ qmaCircuitTermSites (qmaSparseCircuit c) (.inl i)) :
    QMAGridCellsNear (qmaSparseQubitCell c hT k)
      (qmaSparseGateCell c (qmaBoundedClockTime _ hT i.val)) := by
  have hb := qmaBoundedClockTime_pair _ hT i
  have hk' : k = .inl i.castSucc ∨ k = .inl i.succ := by
    simpa [qmaCircuitTermSites] using hk
  rcases hk' with rfl | rfl
  · apply qmaSparseClockCells_near_gate c hT
    change (qmaBoundedClockTime _ hT i.val).val ≤ i.val ∧
      i.val ≤ (qmaBoundedClockTime _ hT i.val).val+2
    omega
  · apply qmaSparseClockCells_near_gate c hT
    change (qmaBoundedClockTime _ hT i.val).val ≤ i.val+1 ∧
      i.val+1 ≤ (qmaBoundedClockTime _ hT i.val).val+2
    omega

theorem qmaSparseClockPin_cell (c : QMACircuit)
    (hT : 0 < (qmaSparseCircuit c).gates.length) (b : Fin 2)
    (k : QMACircuitQubit (qmaSparseCircuit c))
    (hk : k ∈ qmaCircuitTermSites (qmaSparseCircuit c) (.inr (.inl b))) :
    QMAGridCellsNear (qmaSparseQubitCell c hT k)
      (qmaSparseGateCell c (qmaHistoryTermTime (qmaSparseCircuit c) hT
        (qmaFirstUseTime (qmaSparseCircuit c)) (.inr (.inl b)))) := by
  fin_cases b
  · have hk' : k = .inl 0 := by simpa [qmaCircuitTermSites] using hk
    subst k
    apply qmaSparseClockCells_near_gate
    exact ⟨by simp [qmaHistoryTermTime],by simp [qmaHistoryTermTime]⟩
  · have hk' : k = .inl (Fin.last ((qmaSparseCircuit c).gates.length+1)) := by
      simpa [qmaCircuitTermSites] using hk
    subst k
    apply qmaSparseClockCells_near_gate
    dsimp [qmaHistoryTermTime,qmaBoundedClockTime]
    omega

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSpatialTerms
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QMASpatialExchangeModel.withOrdinalSlots_term_index _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every term in the actual distributed history is near its ordered reference. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaSparseOutput_cell (c : QMACircuit)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (k : QMACircuitQubit (qmaSparseCircuit c))
    (hk : k ∈ qmaCircuitTermSites (qmaSparseCircuit c) (.inr (.inr (.inr (.inl ()))))) :
    QMAGridCellsNear (qmaSparseQubitCell c hT k)
      (qmaSparseGateCell c (qmaBoundedClockTime _ hT (qmaSparseCircuit c).gates.length)) := by
  have he : qmaBoundedClockTime _ hT (qmaSparseCircuit c).gates.length =
      (⟨(qmaSparseCircuit c).gates.length-1,by omega⟩ : Fin (qmaSparseCircuit c).gates.length) := by
    apply Fin.ext
    change min _ (_-1) = _-1
    omega
  have hk' : k = .inl (qmaOutputMarker (qmaSparseCircuit c)) ∨
      k = .inr (Fin.last (qmaSparseCircuit c).work) := by
    simpa [qmaCircuitTermSites] using hk
  rcases hk' with rfl | rfl
  · rw [he]
    apply qmaSparseClockCells_near_gate c hT
    change (qmaSparseCircuit c).gates.length-1 ≤ (qmaSparseCircuit c).gates.length ∧
      (qmaSparseCircuit c).gates.length ≤ (qmaSparseCircuit c).gates.length-1+2
    omega
  · change QMAGridCellsNear (qmaSparseWorkCell c (Fin.last (qmaSparseCircuit c).work)) _
    rw [he,qmaSparseWorkCell_last,qmaSparseGateCell_last c hT]
    unfold QMAGridCellsNear
    simp only [Fin.val_last]
    omega

theorem qmaSparseHistoryTerm_cell (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates ≠ []) (a : QMACircuitTerm (qmaSparseCircuit c))
    (k : QMACircuitQubit (qmaSparseCircuit c))
    (hk : k ∈ qmaDistributedTermSites (qmaSparseCircuit c)
      (qmaFirstUseTime (qmaSparseCircuit c)) a) :
    QMAGridCellsNear (qmaSparseQubitCell c hT k)
      (qmaSparseGateCell c (qmaHistoryTermTime (qmaSparseCircuit c) hT
        (qmaFirstUseTime (qmaSparseCircuit c)) a)) := by
  rcases a with i | (b | (i | (u | t)))
  · exact qmaSparseClockFault_cell c hT i k hk
  · exact qmaSparseClockPin_cell c hT b k hk
  · have hi := qmaSweepFirstUse_lt (qmaNearestCircuit c) hne i
    have he := qmaBoundedClockTime_eq _ hT (⟨qmaFirstUse (qmaSparseCircuit c) i,hi⟩ :
      Fin (qmaSparseCircuit c).gates.length)
    change QMAGridCellsNear _ (qmaSparseGateCell c (qmaBoundedClockTime _ hT _))
    rw [he]
    exact qmaSparseInput_cell c hc hT i hi k hk
  · cases u
    exact qmaSparseOutput_cell c hT k hk
  · exact qmaSparsePropagation_cell c hc hT t k hk

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSpatialReference
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! All terms of the real reference model are localized in the actual clock grid. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

def qmaOrderedQubitCell (c : QMACircuit) (hT : 0 < (qmaSparseCircuit c).gates.length) :
    Fin (qmaHistoryReferenceWork (qmaSparseCircuit c)+1) ⊕ QMACircuitQubit (qmaSparseCircuit c) →
      QMAGridCell (qmaNearestCircuit c).gates.length c.work :=
  Sum.elim (qmaOrderedSparseReferenceCell c hT) (qmaSparseQubitCell c hT)

def qmaOrderedTermCell (c : QMACircuit) (hT : 0 < (qmaSparseCircuit c).gates.length) :
    QMAReferenceTerm (qmaHistoryReferenceWork (qmaSparseCircuit c)) →
      QMAGridCell (qmaNearestCircuit c).gates.length c.work
  | .inl i => qmaOrderedSparseReferenceCell c hT i
  | .inr i => qmaOrderedSparseReferenceCell c hT i.castSucc

theorem qmaOrderedHistoryModel_spatial (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates ≠ [])
    (a : QMAReferenceTerm (qmaHistoryReferenceWork (qmaSparseCircuit c)))
    (k : Fin (qmaHistoryReferenceWork (qmaSparseCircuit c)+1) ⊕ QMACircuitQubit (qmaSparseCircuit c))
    (hk : k ∈ (qmaOrderedHistoryModel (qmaSparseCircuit c) hT).sites a) :
    QMAGridCellsNear (qmaOrderedQubitCell c hT k) (qmaOrderedTermCell c hT a) := by
  change k ∈ qmaReferenceTermSites _ (qmaOrderedHistorySites (qmaSparseCircuit c) hT) a at hk
  cases a with
  | inl i =>
    cases k with
    | inl j =>
      have he : j = i := by
        simpa [qmaReferenceTermSites,qmaDistributedRebitSites] using hk
      subst j
      exact qmaGridCellsNear_refl _
    | inr k =>
      have hk' : k ∈ qmaOrderedHistorySites (qmaSparseCircuit c) hT i := by
        simpa [qmaReferenceTermSites,qmaDistributedRebitSites] using hk
      exact qmaSparseHistoryTerm_cell c hc hT hne _ k hk'
  | inr i =>
    have hk' : k = .inl i.castSucc ∨ k = .inl i.succ := by
      simpa [qmaReferenceTermSites,qmaReferenceEdgeSites] using hk
    rcases hk' with rfl | rfl
    · exact qmaGridCellsNear_refl _
    · exact qmaGridCellsNear_symm (qmaOrderedSparseReferenceCell_near c hT i)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSpatialOccupancy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete real history model has bounded qubit and term density in its grid. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaSparseWorkCell_injective (c : QMACircuit) : Function.Injective (qmaSparseWorkCell c) := by
  intro i j h
  have hh := congrArg (fun p => qmaGridQubit (qmaNearestCircuit c).gates.length c.work p.1 p.2) h
  simpa only [qmaSparseWorkCell,qmaGridCoordinates_right] using hh

theorem qmaSparseWorkCell_fiber_card (c : QMACircuit)
    (p : QMAGridCell (qmaNearestCircuit c).gates.length c.work) :
    (Finset.univ.filter (fun i => qmaSparseWorkCell c i = p)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro i hi j hj
  exact qmaSparseWorkCell_injective c
    ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm)

theorem qmaSparseClockCell_fiber_card (c : QMACircuit)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (p : QMAGridCell (qmaNearestCircuit c).gates.length c.work) :
    (Finset.univ.filter (fun b => qmaSparseClockCell c hT b = p)).card ≤ 12 := by
  apply (Finset.card_le_card (show _ ⊆ qmaSparseClockCellBits c hT p from ?_)).trans
    (qmaSparseClockCellBits_card c hT p)
  intro b hb
  have hm := qmaSparseClockCellBits_mem c hT b
  rw [(Finset.mem_filter.mp hb).2] at hm
  exact hm

theorem qmaOrderedReferenceCell_fiber_card (c : QMACircuit)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates ≠ [])
    (p : QMAGridCell (qmaNearestCircuit c).gates.length c.work) :
    (Finset.univ.filter (fun i => qmaOrderedSparseReferenceCell c hT i = p)).card ≤ 32 := by
  apply (Finset.card_le_card (show _ ⊆ qmaSparseReferenceCellIndices c hT p from ?_)).trans
    (qmaSparseReferenceCellIndices_card c hT hne p)
  intro i hi
  have hm := qmaSparseReferenceCellIndices_mem c hT i
  rw [(Finset.mem_filter.mp hi).2] at hm
  exact hm

theorem qmaOrderedQubitCell_fiber_card (c : QMACircuit)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates ≠ [])
    (p : QMAGridCell (qmaNearestCircuit c).gates.length c.work) :
    (Finset.univ.filter (fun k => qmaOrderedQubitCell c hT k = p)).card ≤ 45 := by
  rw [qmaSumFilter_card]
  change (Finset.univ.filter (fun i => qmaOrderedSparseReferenceCell c hT i = p)).card+
    (Finset.univ.filter (fun k : Fin ((qmaSparseCircuit c).gates.length+2) ⊕
      Fin ((qmaSparseCircuit c).work+1) => qmaSparseQubitCell c hT k = p)).card ≤ 45
  rw [qmaSumFilter_card]
  exact (Nat.add_le_add (qmaOrderedReferenceCell_fiber_card c hT hne p)
    (Nat.add_le_add (qmaSparseClockCell_fiber_card c hT p) (qmaSparseWorkCell_fiber_card c p))).trans
      (by decide)

theorem qmaOrderedTermCell_fiber_card (c : QMACircuit)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates ≠ [])
    (p : QMAGridCell (qmaNearestCircuit c).gates.length c.work) :
    (Finset.univ.filter (fun a => qmaOrderedTermCell c hT a = p)).card ≤ 64 := by
  have hr := qmaOrderedReferenceCell_fiber_card c hT hne p
  have he : (Finset.univ.filter (fun i : Fin (qmaHistoryReferenceWork (qmaSparseCircuit c)) =>
      qmaOrderedSparseReferenceCell c hT i.castSucc = p)).card ≤
      (Finset.univ.filter (fun i => qmaOrderedSparseReferenceCell c hT i = p)).card := by
    apply Finset.card_le_card_of_injOn Fin.castSucc
    · intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2⟩
    · intro i _ j _ h
      exact (Fin.castSucc_inj.mp h)
  change (Finset.univ.filter (fun a : Fin (qmaHistoryReferenceWork (qmaSparseCircuit c)+1) ⊕
    Fin (qmaHistoryReferenceWork (qmaSparseCircuit c)) => qmaOrderedTermCell c hT a = p)).card ≤ 64
  rw [qmaSumFilter_card]
  exact (Nat.add_le_add hr (he.trans hr)).trans (by decide)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCircuitPadding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two cancelling Hadamards remove the empty-circuit exception without changing acceptance. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped Classical

theorem qmaNonemptyCircuit_sparse_pos (c : QMACircuit) :
    0 < (qmaSparseCircuit (qmaNonemptyCircuit c)).gates.length := by
  have hn := List.length_pos_iff.mpr (qmaNonemptyCircuit_nearest c)
  change 0 < (qmaSweepCircuitFrom _ _ 0 _ _).length
  rw [qmaSweepCircuitFrom_length]
  exact Nat.mul_pos (by omega) hn

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRawProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal polynomial programs for fixed-size physical exchange instructions. -/

noncomputable section
namespace ContinuumCoulomb.QuantumRawExchange
open QuantumAxisSample MediatorListProgram ExactQuantumFactoring.BitStackProgram

noncomputable opaque fieldCoefficientProgram (e : Fin 3) : Procedure inputCode ratCode
    (fun x => fieldValue x.1.1 (axis x.2.2.2.1.1) x.2.2.2.2 e) :=
  selectAxis axisLeftProgram (fun a => (fieldValueProgram a e).comp radialProgram)

noncomputable opaque fieldBondProgram (e : Fin 3) : Procedure inputCode bondCode
    (fun x => (4*x.2.2.1.1,4*x.2.2.1.1+(qmaFieldEdgeRight e).val,
      fieldValue x.1.1 (axis x.2.2.2.1.1) x.2.2.2.2 e)) :=
  baseLeftProgram.pair ((shiftedLeftProgram _).pair (fieldCoefficientProgram e))

noncomputable opaque fieldProgram : Procedure inputCode (listCode bondCode)
    (fun x => field x.1.1 x.2.2.1.1 (axis x.2.2.2.1.1) x.2.2.2.2) :=
  fixedListProgram inputCode bondCode 3 _ fieldBondProgram

noncomputable opaque crossCoefficientProgram (p q : Fin 4) : Procedure inputCode ratCode
    (fun x => crossValue x.1.1 x.1.2 (axis x.2.2.2.1.1) (axis x.2.2.2.1.2) x.2.2.2.2 p q) :=
  selectAxis axisLeftProgram (fun a => selectAxis axisRightProgram
    (fun b => (crossValueProgram a b p q).comp crossInputProgram))

noncomputable opaque crossBondProgram (p q : Fin 4) : Procedure inputCode bondCode
    (fun x => (4*x.2.2.1.1+p.val,4*x.2.2.1.2+q.val,
      crossValue x.1.1 x.1.2 (axis x.2.2.2.1.1) (axis x.2.2.2.1.2) x.2.2.2.2 p q)) :=
  (shiftedLeftProgram p).pair ((shiftedRightProgram q).pair (crossCoefficientProgram p q))

noncomputable opaque crossProgram : Procedure inputCode (listCode bondCode)
    (fun x => cross x.1.1 x.1.2 x.2.2.1.1 x.2.2.1.2
      (axis x.2.2.2.1.1) (axis x.2.2.2.1.2) x.2.2.2.2) :=
  fixedListProgram inputCode bondCode 16 _ (fun e =>
    crossBondProgram ((finProdFinEquiv : Fin 4 × Fin 4 ≃ Fin 16).symm e).1
      ((finProdFinEquiv : Fin 4 × Fin 4 ≃ Fin 16).symm e).2)

end ContinuumCoulomb.QuantumRawExchange

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRawTermProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complete polynomial evaluation of each rational X/Z instruction. -/

noncomputable section
namespace ContinuumCoulomb.QuantumRawExchange
open QuantumAxisSample MediatorListProgram ExactQuantumFactoring.BitStackProgram

noncomputable opaque counterLeftCoefficientProgram (e : Fin 3) : Procedure inputCode ratCode
    (fun x => fieldValue x.1.1 (axis x.2.2.2.1.1)
      (counterA x.1.1 (axis x.2.2.2.1.1) (axis x.2.2.2.1.2) x.2.2.2.2) e) :=
  selectAxis axisLeftProgram (fun a => selectAxis axisRightProgram
    (fun b => (counterFieldAProgram a b e).comp radialProgram))

noncomputable opaque counterRightCoefficientProgram (e : Fin 3) : Procedure inputCode ratCode
    (fun x => fieldValue x.1.1 (axis x.2.2.2.1.2)
      (counterB x.1.1 (axis x.2.2.2.1.1) (axis x.2.2.2.1.2) x.2.2.2.2) e) :=
  selectAxis axisLeftProgram (fun a => selectAxis axisRightProgram
    (fun b => (counterFieldBProgram a b e).comp radialProgram))

noncomputable opaque counterLeftBondProgram (e : Fin 3) : Procedure inputCode bondCode
    (fun x => (4*x.2.2.1.1,4*x.2.2.1.1+(qmaFieldEdgeRight e).val,
      fieldValue x.1.1 (axis x.2.2.2.1.1)
        (counterA x.1.1 (axis x.2.2.2.1.1) (axis x.2.2.2.1.2) x.2.2.2.2) e)) :=
  baseLeftProgram.pair ((shiftedLeftProgram _).pair (counterLeftCoefficientProgram e))

noncomputable opaque counterRightBondProgram (e : Fin 3) : Procedure inputCode bondCode
    (fun x => (4*x.2.2.1.2,4*x.2.2.1.2+(qmaFieldEdgeRight e).val,
      fieldValue x.1.1 (axis x.2.2.2.1.2)
        (counterB x.1.1 (axis x.2.2.2.1.1) (axis x.2.2.2.1.2) x.2.2.2.2) e)) :=
  baseRightProgram.pair ((shiftedRightProgram _).pair (counterRightCoefficientProgram e))

noncomputable opaque counterLeftProgram : Procedure inputCode (listCode bondCode)
    (fun x => field x.1.1 x.2.2.1.1 (axis x.2.2.2.1.1)
      (counterA x.1.1 (axis x.2.2.2.1.1) (axis x.2.2.2.1.2) x.2.2.2.2)) :=
  fixedListProgram inputCode bondCode 3 _ counterLeftBondProgram

noncomputable opaque counterRightProgram : Procedure inputCode (listCode bondCode)
    (fun x => field x.1.1 x.2.2.1.2 (axis x.2.2.2.1.2)
      (counterB x.1.1 (axis x.2.2.2.1.1) (axis x.2.2.2.1.2) x.2.2.2.2)) :=
  fixedListProgram inputCode bondCode 3 _ counterRightBondProgram

noncomputable opaque pairProgram : Procedure inputCode (listCode bondCode)
    (fun x => cross x.1.1 x.1.2 x.2.2.1.1 x.2.2.1.2
      (axis x.2.2.2.1.1) (axis x.2.2.2.1.2) x.2.2.2.2 ++
      field x.1.1 x.2.2.1.1 (axis x.2.2.2.1.1)
        (counterA x.1.1 (axis x.2.2.2.1.1) (axis x.2.2.2.1.2) x.2.2.2.2) ++
      field x.1.1 x.2.2.1.2 (axis x.2.2.2.1.2)
        (counterB x.1.1 (axis x.2.2.2.1.1) (axis x.2.2.2.1.2) x.2.2.2.2)) :=
  (Procedure.listAppend bondCode zeroBond).comp
    (((Procedure.listAppend bondCode zeroBond).comp (crossProgram.pair counterLeftProgram)).pair
      counterRightProgram)

noncomputable opaque bondsProgram : Procedure inputCode (listCode bondCode) bonds :=
  (Procedure.conditional pairFlagProgram pairProgram
    (Procedure.conditional fieldFlagProgram fieldProgram (Procedure.constant inputCode (listCode bondCode) []))).congrFun
      (by intro x; rfl)

noncomputable opaque offsetProgram : Procedure inputCode ratCode
    (fun x => offset x.1.1 (axis x.2.2.2.1.1) (axis x.2.2.2.1.2) x.2.2.2.2) :=
  selectAxis axisLeftProgram (fun a => selectAxis axisRightProgram
    (fun b => (QuantumAxisSample.offsetProgram a b).comp radialProgram))

noncomputable opaque fieldShiftProgram : Procedure inputCode ratCode
    (fun x => shiftValue (axis x.2.2.2.1.1) x.2.2.2.2) :=
  selectAxis axisLeftProgram (fun a => (shiftValueProgram a).comp weightProgram)

noncomputable opaque scalarProgram : Procedure inputCode ratCode scalar :=
  (Procedure.conditional pairFlagProgram (Procedure.ratNeg.comp offsetProgram)
    (Procedure.conditional fieldFlagProgram (Procedure.ratNeg.comp fieldShiftProgram) weightProgram)).congrFun
      (by intro x; rfl)

end ContinuumCoulomb.QuantumRawExchange

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRawFamilyProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete finite rational edge list and offset are computed in polynomial time. -/

noncomputable section
namespace ContinuumCoulomb.QuantumRawExchange
open QuantumAxisSample MediatorListProgram ExactQuantumFactoring.BitStackProgram

noncomputable opaque termBondsProgram : Procedure familyCode (listCode bondCode) termBondsList :=
  (flattenProgram bondCode zeroBond).comp
    (Procedure.listMapWith (ea := environmentCode) (eb := rawCode) (ec := listCode bondCode)
      (f := fun env t => bonds (env,t)) zeroRaw [] bondsProgram)

noncomputable opaque termScalarProgram : Procedure familyCode ratCode termScalarList :=
  RationalSumProgram.sumProgram.comp
    (Procedure.listMapWith (ea := environmentCode) (eb := rawCode) (ec := ratCode)
      (f := fun env t => scalar (env,t)) zeroRaw 0 scalarProgram)

noncomputable opaque penaltyBlockProgram : Procedure penaltyCode (listCode bondCode)
    (fun x => penaltyBlock x.2 x.1) := fixedListProgram penaltyCode bondCode 6 _ penaltyBondProgram
noncomputable opaque penaltyProgram : Procedure penaltyCode (listCode bondCode)
    (fun x => penalty x.1 x.2) :=
  (flattenProgram bondCode zeroBond).comp (Procedure.tabulate [] penaltyBlockProgram)

noncomputable opaque fullBondsProgram : Procedure fullCode (listCode bondCode) fullBonds :=
  (Procedure.listAppend bondCode zeroBond).comp ((penaltyProgram.comp fullPenaltyInputProgram).pair
    (termBondsProgram.comp fullFamilyProgram))
noncomputable opaque fullScalarProgram : Procedure fullCode ratCode fullScalar :=
  Procedure.ratAdd.comp (fullPenaltyScalarProgram.pair (termScalarProgram.comp fullFamilyProgram))

end ContinuumCoulomb.QuantumRawExchange

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPathProgram
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal polynomial coefficient program for both parities of a path gadget. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPathCode
open ExactQuantumFactoring.BitStackProgram QuantumRoutingCode

noncomputable opaque spokeProgram : Procedure inputCode ratCode
    (fun x => if x.1 then -2*x.2.1*x.2.2 else 2*x.2.1*x.2.2) := by
  let p := twiceProductProgram radiusProgram weightProgram
  exact (Procedure.conditional evenProgram (Procedure.ratNeg.comp p) p).congrFun
    (by rintro ⟨b,r,j⟩; cases b <;> simp [neg_mul])
noncomputable opaque offsetProgram : Procedure inputCode ratCode
    (fun x => 3/4+3*x.2.2^2+3*x.2.1^2) := by
  let j := Procedure.ratMul.comp ((Procedure.constant inputCode ratCode 3).pair (squareProgram weightProgram))
  let r := Procedure.ratMul.comp ((Procedure.constant inputCode ratCode 3).pair (squareProgram radiusProgram))
  exact Procedure.ratAdd.comp ((Procedure.ratAdd.comp
    ((Procedure.constant inputCode ratCode (3/4)).pair j)).pair r)

noncomputable opaque coefficientProgram (k : Fin 4) : Procedure inputCode ratCode (fun x => coefficients x k) := by
  by_cases h0 : k = 0
  · subst k
    exact (squareProgram radiusProgram).congrFun (by intro x; rfl)
  by_cases h1 : k = 1
  · subst k
    exact radiusProgram.congrFun (by intro x; rfl)
  by_cases h2 : k = 2
  · subst k
    exact spokeProgram.congrFun (by intro x; rfl)
  have h3 : k = 3 := by omega
  subst k
  exact offsetProgram.congrFun (by intro x; rfl)

end ContinuumCoulomb.QuantumPathCode

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
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode QuantumFiniteMembership

noncomputable opaque crossingProgram : Procedure inputCode Procedure.boolCode
    (fun x => decide (x.2 ∈ x.1.2.2)) := pairMemberProgram.comp (cellProgram.pair crossingsProgram)

noncomputable opaque rayAllowedProgram (a : Fin 4) : Procedure inputCode Procedure.boolCode
    (fun x => allowed x.1 (.ray x.2 a)) :=
  Procedure.boolAnd.comp ((pairMemberProgram.comp (cellProgram.pair sourcesProgram)).pair
    (Procedure.boolNot.comp crossingProgram))

noncomputable opaque pairAllowedProgram (e : Fin 6) : Procedure inputCode Procedure.boolCode
    (fun x => allowed x.1 (.pair x.2 e)) := by
  let memp := memberProgram visitCode ((0,0),(0,0)) (Procedure.prodEq pairEqProgram pairEqProgram)
  let v := cellProgram.pair (Procedure.constant inputCode pairCode
    ((qmaCellPairLeft e).val,(qmaCellPairRight e).val))
  exact Procedure.boolAnd.comp ((Procedure.boolNot.comp crossingProgram).pair
    (memp.comp (v.pair visitsProgram)))

noncomputable opaque patchAllowedProgram (e : Fin 9) : Procedure inputCode Procedure.boolCode
    (fun x => allowed x.1 (.patch x.2 e)) := crossingProgram

noncomputable opaque corridorAllowedProgram (a : Fin 4) (b c : Bool) :
    Procedure inputCode Procedure.boolCode (fun x => allowed x.1 (.corridor x.2 a b c)) := by
  let eqb := Procedure.ofBool Procedure.boolCode (fun x => decide (b=x))
  let eqc := Procedure.ofBool Procedure.boolCode (fun x => decide (c=x))
  let next := pairMemberProgram.comp
    ((QuantumCellPathProgram.neighborProgram a |>.comp cellProgram).pair crossingsProgram)
  exact Procedure.boolAnd.comp ((eqb.comp crossingProgram).pair (eqc.comp next))

end ContinuumCoulomb.QuantumRoutingTable

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRoutingCrossingTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Crossing cells are detected from the two opposite port pairs in the finite
visit table. No search over a proof-level finite type is needed. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode QuantumRoutingTable
namespace QuantumRoutingTable

noncomputable def crossingTestProgram : Procedure inputCode Procedure.boolCode
    (fun x => crossingTest x.1 x.2) := by
  let memp := QuantumFiniteMembership.memberProgram visitCode ((0,0),(0,0))
    (Procedure.prodEq QuantumFiniteMembership.pairEqProgram QuantumFiniteMembership.pairEqProgram)
  let check (a b : ℕ) := memp.comp
    ((cellProgram.pair (Procedure.constant inputCode pairCode (a,b))).pair visitsProgram)
  exact Procedure.boolAnd.comp ((check 0 2).pair (check 1 3))

end QuantumRoutingTable
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumComputedRoutingTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compute the crossing list from encoded visits, and preserve exactly the
routing permissions of the geometric construction. -/

noncomputable section
namespace ContinuumCoulomb.QuantumRoutingTable
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

noncomputable def selectCrossingProgram :
    Procedure inputCode (listCode pairCode)
      (fun x => if crossingTest x.1 x.2 then [x.2] else []) :=
  Procedure.conditional crossingTestProgram
    ((Procedure.listCons pairCode).comp
      (cellProgram.pair (Procedure.constant inputCode (listCode pairCode) [])))
    (Procedure.constant inputCode (listCode pairCode) [])

noncomputable def computedCrossingsProgram : Procedure tableCode (listCode pairCode)
    computedCrossings := by
  let visits : Procedure tableCode (listCode visitCode) (fun t => t.2.1) :=
    (Procedure.first (listCode visitCode) (listCode pairCode)).comp
      (Procedure.second (listCode pairCode) (prodCode (listCode visitCode) (listCode pairCode)))
  let cells := (Procedure.listMap ((0,0),(0,0)) (0,0)
    (Procedure.first pairCode pairCode)).comp visits
  let selected := (Procedure.listMapWith (f := fun t p => if crossingTest t p then [p] else [])
    (0,0) [] selectCrossingProgram).comp ((Procedure.identity tableCode).pair cells)
  exact ((QuantumRawExchange.flattenProgram pairCode (0,0)).comp selected).congrFun (by
    intro t
    change ((t.2.1.map Prod.fst).map (fun p => if crossingTest t p then [p] else [])).flatten = _
    exact filter_eq_flatten (crossingTest t) (t.2.1.map Prod.fst))

noncomputable def computedTableProgram : Procedure tableCode tableCode computedTable := by
  let rest := Procedure.second (listCode pairCode) (prodCode (listCode visitCode) (listCode pairCode))
  let visits := (Procedure.first (listCode visitCode) (listCode pairCode)).comp rest
  exact (Procedure.first (listCode pairCode) _).pair (visits.pair computedCrossingsProgram)

end ContinuumCoulomb.QuantumRoutingTable

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPathScaleProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact rational calibration from the retained and selected edge weights.
The sums are computed by the proved polynomial rational-list accumulator. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPathScaleProgram
open ExactQuantumFactoring.BitStackProgram
open scoped BigOperators Classical

noncomputable def linearProgram : Procedure ratCode ratCode linearCost :=
  Procedure.ratAdd.comp ((Procedure.constant ratCode ratCode 1).pair
    (Procedure.ratMul.comp ((Procedure.constant ratCode ratCode 2).pair
      MediatorProgram.absoluteProgram)))

noncomputable def squareProgram : Procedure ratCode ratCode squareCost :=
  QuantumRoutingCode.squareProgram (Procedure.ratAdd.comp
    ((Procedure.constant ratCode ratCode 1).pair MediatorProgram.absoluteProgram))

noncomputable def program : Procedure inputCode ratCode value := by
  let params := Procedure.first (prodCode ratCode ratCode)
    (prodCode (listCode ratCode) (listCode ratCode))
  let lists := Procedure.second (prodCode ratCode ratCode)
    (prodCode (listCode ratCode) (listCode ratCode))
  let n := (Procedure.first ratCode ratCode).comp params
  let c := (Procedure.second ratCode ratCode).comp params
  let retained := (Procedure.first (listCode ratCode) (listCode ratCode)).comp lists
  let selected := (Procedure.second (listCode ratCode) (listCode ratCode)).comp lists
  let b := Procedure.ratAdd.comp
    ((Procedure.ratMul.comp ((Procedure.constant inputCode ratCode 3).pair
      ((sumMapProgram MediatorProgram.absoluteProgram).comp retained))).pair
      (MediatorProgram.absoluteProgram.comp c))
  let a := Procedure.ratMul.comp ((Procedure.constant inputCode ratCode 3).pair
    ((sumMapProgram linearProgram).comp selected))
  let d := Procedure.ratAdd.comp (b.pair
    (Procedure.ratMul.comp ((Procedure.constant inputCode ratCode 4).pair
      ((sumMapProgram squareProgram).comp selected))))
  exact QuantumRoutingCode.scaleProgram.comp (a.pair (d.pair n))

end ContinuumCoulomb.QuantumPathScaleProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListPathProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal three-edge output for one selected path subdivision. Fresh spin
labels are assigned in the input list order; both path parities are supported. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListPathProgram
open ExactQuantumFactoring.BitStackProgram MediatorListProgram

noncomputable opaque coefficientProgram (k : Fin 4) :
    Procedure inputCode ratCode (fun x => coefficient x k) := by
  let r : Procedure inputCode ratCode (fun x => x.1.2.2) :=
    (Procedure.second Procedure.boolCode ratCode).comp
      ((Procedure.second unaryCode (prodCode Procedure.boolCode ratCode)).comp (Procedure.first _ _))
  let j : Procedure inputCode ratCode (fun x => x.2.2.2.2) :=
    (Procedure.second Nat.bits ratCode).comp
    ((Procedure.second Nat.bits (prodCode Nat.bits ratCode)).comp sourceProgram)
  exact (QuantumPathCode.coefficientProgram k).comp (parityProgram.pair (r.pair j))

noncomputable opaque bondProgram (k : Fin 3) : Procedure inputCode bondCode (fun x => bond x k) :=
  (leftProgram k).pair ((rightProgram k).pair (coefficientProgram k.castSucc))
noncomputable opaque offsetProgram : Procedure inputCode ratCode offset := coefficientProgram 3

noncomputable opaque familyOffsetProgram : Procedure familyCode ratCode familyOffset := by
  let p := Procedure.first parametersCode bondCode
  let e := Procedure.second parametersCode bondCode
  let entry := offsetProgram.comp (p.pair ((Procedure.constant _ unaryCode 0).pair e))
  exact RationalSumProgram.sumProgram.comp
    (Procedure.listMapWith (ea := parametersCode) (eb := bondCode) (ec := ratCode)
      (f := fun p e => offset (p,0,e)) zeroBond 0 entry)

end ContinuumCoulomb.QuantumListPathProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListPathStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A calibrated selected-subdivision step acting directly on finite bond
lists. The selected list order fixes the labels of every new mediator pair. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListPathStep
open ExactQuantumFactoring.BitStackProgram MediatorListProgram

noncomputable opaque scaleInputProgram :
    Procedure inputCode QuantumPathScaleProgram.inputCode scaleInput :=
  constantsProgram.pair ((weightsProgram.comp retainedProgram).pair (weightsProgram.comp selectedProgram))
noncomputable opaque parametersProgram :
    Procedure inputCode QuantumListPathProgram.parametersCode parameters :=
  countInputProgram.pair (parityProgram.pair (QuantumPathScaleProgram.program.comp scaleInputProgram))
noncomputable opaque familyInputProgram : Procedure inputCode QuantumListPathProgram.familyCode
    (fun x => (parameters x,x.2.2)) := parametersProgram.pair selectedProgram
noncomputable opaque constantProgram : Procedure inputCode ratCode constant :=
  Procedure.ratAdd.comp
    (((Procedure.second ratCode ratCode).comp constantsProgram).pair
      (QuantumListPathProgram.familyOffsetProgram.comp familyInputProgram))

end ContinuumCoulomb.QuantumListPathStep

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCrossingSelectProgram
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.edges_length _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.lower_value _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.upper_value _root_.OAI.ContinuumCoulomb.QuantumPortChainProgram.value_length _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Select crossing interactions directly from the finite bond tape.
Both orientations contribute to each rational coupling; every other bond is
retained. All scans are literal polynomial programs. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCrossingSelectProgram
open ExactQuantumFactoring.BitStackProgram MediatorListProgram QuantumRouteCode
open QuantumCrossingListBlock

noncomputable opaque pairsProgram : Procedure (listCode sitesCode) (listCode pairCode) pairs := by
  let entry := (Procedure.listCons pairCode).comp ((terminalProgram 0).pair
    ((Procedure.listCons pairCode).comp ((terminalProgram 1).pair
      (Procedure.constant sitesCode (listCode pairCode) []))))
  exact (QuantumRawExchange.flattenProgram pairCode (0,0)).comp
    (Procedure.listMap ((0,0),(0,0)) [] entry)

noncomputable opaque weightProgram : Procedure (prodCode (listCode bondCode) pairCode) ratCode weight := by
  let ctx := Procedure.second (listCode bondCode) pairCode
  let es := Procedure.first (listCode bondCode) pairCode
  let term : Procedure (prodCode pairCode bondCode) ratCode
      (fun x => contribution (x.2,x.1)) :=
    contributionProgram.comp ((Procedure.second pairCode bondCode).pair
      (Procedure.first pairCode bondCode))
  exact RationalSumProgram.sumProgram.comp
    ((Procedure.listMapWith (f := fun p e => contribution (e,p)) zeroBond 0 term).comp
      (ctx.pair es))

noncomputable opaque keepProgram : Procedure (prodCode (listCode pairCode) bondCode)
    Procedure.boolCode keep := by
  let ps := Procedure.first (listCode pairCode) bondCode
  let e := Procedure.second (listCode pairCode) bondCode
  exact (Procedure.boolNot.comp (QuantumFiniteMembership.anyProgram.comp
    ((Procedure.listMapWith (f := fun e p => hits (e,p)) (0,0) false hitsProgram).comp
      (e.pair ps)))).congrFun (by
        intro x
        simp only [Function.comp_apply,List.any_map,Function.comp_def,id_eq,keep])

noncomputable opaque retainedProgram :
    Procedure (prodCode (listCode pairCode) (listCode bondCode)) (listCode bondCode) retained := by
  let entry := Procedure.conditional keepProgram
    ((Procedure.listCons bondCode).comp ((Procedure.second (listCode pairCode) bondCode).pair
      (Procedure.constant _ (listCode bondCode) [])))
    (Procedure.constant _ (listCode bondCode) [])
  refine ((QuantumRawExchange.flattenProgram bondCode zeroBond).comp
    (Procedure.listMapWith (f := fun ps e => if keep (ps,e) then [e] else [])
      zeroBond [] entry)).congrFun ?_
  intro x
  change (x.2.map (fun e => if keep (x.1,e) then [e] else [])).flatten =
    x.2.filter (fun e => keep (x.1,e))
  induction x.2 with
  | nil => rfl
  | cons e es ih =>
    simp only [List.map_cons,List.flatten_cons,List.filter_cons] at *
    cases h : keep (x.1,e) <;> simpa [h] using ih

noncomputable opaque crossingProgram : Procedure (prodCode (listCode bondCode) sitesCode)
    crossingCode crossing := by
  let es := Procedure.first (listCode bondCode) sitesCode
  let s := Procedure.second (listCode bondCode) sitesCode
  exact ((weightProgram.comp (es.pair ((terminalProgram 0).comp s))).pair
    (weightProgram.comp (es.pair ((terminalProgram 1).comp s)))).pair s

noncomputable opaque crossingsProgram :
    Procedure (prodCode (listCode bondCode) (listCode sitesCode)) (listCode crossingCode) crossings :=
  Procedure.listMapWith (f := fun es s => crossing (es,s)) ((0,0),(0,0)) zeroCrossing crossingProgram

noncomputable opaque sitesProgram : Procedure inputCode (listCode sitesCode) (fun x => x.2.2) :=
  (Procedure.second QuantumListPathStep.outputCode (listCode sitesCode)).comp
    (Procedure.second ratCode (prodCode QuantumListPathStep.outputCode (listCode sitesCode)))
noncomputable opaque program :
    Procedure inputCode QuantumCrossingListLayer.inputCode value := by
  let n := (Procedure.first unaryCode (prodCode (listCode bondCode) ratCode)).comp packetProgram
  let c := (Procedure.second (listCode bondCode) ratCode).comp
    ((Procedure.second unaryCode (prodCode (listCode bondCode) ratCode)).comp packetProgram)
  let es := retainedProgram.comp ((pairsProgram.comp sitesProgram).pair bondsProgram)
  let cs := crossingsProgram.comp (bondsProgram.pair sitesProgram)
  exact (precisionProgram.pair (n.pair (es.pair c))).pair cs

end ContinuumCoulomb.QuantumCrossingSelectProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFirstUseProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal first-use indices for the actual circuit gates. The fold stores a
unary index bounded by the gate-list length, including the no-use case. -/

noncomputable section
namespace ContinuumCoulomb.QuantumFirstUseProgram
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode

theorem value_eq (c : QMACircuit) (i : Fin (c.work+1)) :
    value (c,i.val)=qmaFirstUse c i := by
  unfold value touchList
  simp only [Function.comp_apply]
  rw [first_eq_findIdx,List.findIdx_map]
  unfold qmaFirstUse
  congr 1
  funext g
  exact touches_spec c i g

end ContinuumCoulomb.QuantumFirstUseProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPathVisitProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Encoded path lists determine the two directional ports of every internal
cell. The output contains both orientations, as required by the route table. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPathVisitProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode QuantumRoutingTable

noncomputable def visitsProgram : Procedure (listCode pairCode) (listCode visitCode) visits := by
  let count := Procedure.unarySub.comp
    ((ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength pairCode (0,0)).pair
      (Procedure.constant (listCode pairCode) unaryCode 2))
  let tab := (Procedure.tabulate (f := fun xs i => both (visit xs i)) []
    (bothProgram.comp visitProgram)).comp
    (count.pair (Procedure.identity (listCode pairCode)))
  exact (QuantumRawExchange.flattenProgram visitCode ((0,0),(0,0))).comp tab

end ContinuumCoulomb.QuantumPathVisitProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPortChainProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal evaluation of the physical port chain on a computed coarse path.
The output enumerates both endpoint centers and every incoming/outgoing port. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPortChainProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

noncomputable def portProgram : Procedure (prodCode pairCode Nat.bits) pairCode
    (fun x => port x.1 x.2) := by
  let p := Procedure.first pairCode Nat.bits
  let a := Procedure.second pairCode Nat.bits
  let is (i : ℕ) := Procedure.binaryEq.comp (a.pair (Procedure.constant _ Nat.bits i))
  exact (Procedure.conditional (is 0) ((offsetProgram 23 16).comp p)
    (Procedure.conditional (is 1) ((offsetProgram 16 23).comp p)
      (Procedure.conditional (is 2) ((offsetProgram 9 16).comp p)
        ((offsetProgram 16 9).comp p)))).congrFun (by
          intro x
          simp only [Function.comp_apply,decide_eq_true_eq,port])

noncomputable def directedProgram : Procedure (prodCode pairCode pairCode) pairCode
    (fun x => qmaDirectedPort x.1 x.2) :=
  (portProgram.comp ((Procedure.first pairCode pairCode).pair
    QuantumPathVisitProgram.neighborIndexProgram)).congrFun (by
      intro x
      exact port_fin x.1 (qmaGridNeighborIndex x.1 x.2))

noncomputable def lengthProgram : Procedure (listCode pairCode) unaryCode
    (fun xs => xs.length-1) :=
  Procedure.unarySub.comp
    ((ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength pairCode (0,0)).pair
      (Procedure.constant (listCode pairCode) unaryCode 1))

noncomputable def pointProgram : Procedure inputCode pairCode (fun x => point x.2 x.1) := by
  let k := Procedure.unaryToBits.comp (Procedure.first unaryCode (listCode pairCode))
  let xs := Procedure.second unaryCode (listCode pairCode)
  let len := Procedure.unaryToBits.comp (lengthProgram.comp xs)
  let last := Procedure.binaryAdd.comp
    ((Procedure.binaryMul.comp ((Procedure.constant inputCode Nat.bits 2).pair len)).pair
      (Procedure.constant inputCode Nat.bits 1))
  let first := (Procedure.listGet pairCode (0,0)).comp
    ((Procedure.constant inputCode Nat.bits 0).pair xs)
  let final := (Procedure.listGet pairCode (0,0)).comp (len.pair xs)
  let half := Procedure.binaryDiv.comp (k.pair (Procedure.constant inputCode Nat.bits 2))
  let here := (Procedure.listGet pairCode (0,0)).comp (half.pair xs)
  let there := (Procedure.listGet pairCode (0,0)).comp ((neighborProgram.comp k).pair xs)
  let inner := directedProgram.comp (here.pair there)
  exact (Procedure.conditional (Procedure.binaryZero.comp k) (centerProgram.comp first)
    (Procedure.conditional (Procedure.binaryEq.comp (k.pair last))
      (centerProgram.comp final) inner)).congrFun (by
        intro x
        simp only [Function.comp_apply,id_eq,decide_eq_true_eq,point,qmaPortChain,
          qmaRoutePort,QuantumPathVisitProgram.lookup])

noncomputable def program : Procedure (listCode pairCode) (listCode pairCode) value := by
  let n := Procedure.unaryAdd.comp
    ((Procedure.unaryMul.comp ((Procedure.constant (listCode pairCode) unaryCode 2).pair
      lengthProgram)).pair (Procedure.constant (listCode pairCode) unaryCode 2))
  exact (Procedure.tabulate (f := point) (0,0) pointProgram).comp
    (n.pair (Procedure.identity (listCode pairCode)))

end ContinuumCoulomb.QuantumPortChainProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCrossingSiteProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Locate crossing terminals by scanning the actual physical position tape.
The finite search returns exactly the existing terminal spin indices. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCrossingSiteProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode QuantumCrossingListBlock
open scoped Classical

def inputCode : Input → List Bool := prodCode (listCode pairCode) pairCode
def index (x : Input) : ℕ := QuantumFirstUseProgram.first (flags x)

noncomputable opaque flagsProgram : Procedure inputCode (listCode Procedure.boolCode) flags := by
  let targets := Procedure.second (listCode pairCode) pairCode
  let ps := Procedure.first (listCode pairCode) pairCode
  let eq := QuantumFiniteMembership.pairEqProgram.comp
    ((Procedure.second pairCode pairCode).pair (Procedure.first pairCode pairCode))
  exact (Procedure.listMapWith (f := fun q p => decide (p=q)) (0,0) false eq).comp
    (targets.pair ps)
noncomputable opaque indexProgram : Procedure inputCode unaryCode index :=
  QuantumFirstUseProgram.firstProgram.comp flagsProgram

def target (a : Fin 4) (x : Input) : Input :=
  (x.1,qmaGridPort x.2 (qmaPatchDirection a))
def terminal (a : Fin 4) (x : Input) : ℕ := index (target a x)
def sites (x : Input) : Sites := ((terminal 0 x,terminal 1 x),(terminal 2 x,terminal 3 x))

noncomputable opaque targetProgram (a : Fin 4) : Procedure inputCode inputCode (target a) := by
  let p := Procedure.second (listCode pairCode) pairCode
  let endpoint := (QuantumPortChainProgram.portProgram.comp
    (p.pair (Procedure.constant inputCode Nat.bits (qmaPatchDirection a).val))).congrFun
      (by intro x; exact QuantumPortChainProgram.port_fin x.2 (qmaPatchDirection a))
  exact (Procedure.first (listCode pairCode) pairCode).pair endpoint
noncomputable opaque terminalProgram (a : Fin 4) : Procedure inputCode Nat.bits (terminal a) :=
  Procedure.unaryToBits.comp (indexProgram.comp (targetProgram a))
noncomputable opaque sitesProgram : Procedure inputCode sitesCode sites :=
  ((terminalProgram 0).pair (terminalProgram 1)).pair
    ((terminalProgram 2).pair (terminalProgram 3))

def allSites (x : List Pair × List Pair) : List Sites := x.2.map (fun c => sites (x.1,c))
noncomputable opaque allSitesProgram :
    Procedure (prodCode (listCode pairCode) (listCode pairCode)) (listCode sitesCode) allSites :=
  Procedure.listMapWith (f := fun ps c => sites (ps,c)) (0,0) ((0,0),(0,0)) sitesProgram

end ContinuumCoulomb.QuantumCrossingSiteProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal short support lists for the time-ordered history compiler.
The list order, duplicate removal, and local-coordinate equivalence are
explicit; no arbitrary finite-type enumeration enters the input algorithm. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedSupport
open scoped Classical

theorem sites_length (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c)) : (sites c hT a).length ≤ 6 := by
  rw [← List.toFinset_card_of_nodup (sites_nodup c hT a),sites_finset]
  exact (qmaOrderedHistoryModel c hT).card a

def encodedSites (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c)) : List ℕ :=
  (sites c hT a).map (siteNumber c)

end ContinuumCoulomb.QuantumOrderedSupport

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedDescriptors
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numeric time grouping agrees with the exact ordered reference family.
The first-use time is computed from the actual gate list. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryDescriptors
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode

theorem time_encode (c : QMACircuit) (hT : 0 < c.gates.length) (a : QMACircuitTerm c) :
    timeValue c (encode c a) =
      (qmaHistoryTermTime c hT (qmaFirstUseTime c) a).val := by
  rcases a with i | (b | (i | (u | t)))
  · rfl
  · fin_cases b
    · simp only [timeValue,encode,qmaHistoryTermTime]
      norm_num
    · simp only [timeValue,encode,qmaHistoryTermTime,qmaBoundedClockTime]
      have he : min c.gates.length (c.gates.length-1)=c.gates.length-1 :=
        min_eq_right (Nat.sub_le _ _)
      norm_num [he]
  · simp only [timeValue,encode,qmaHistoryTermTime,qmaBoundedClockTime]
    norm_num only
    rw [QuantumFirstUseProgram.value_eq]
    rfl
  · cases u
    simp only [timeValue,encode,qmaHistoryTermTime,qmaBoundedClockTime]
    have he : min c.gates.length (c.gates.length-1)=c.gates.length-1 :=
      min_eq_right (Nat.sub_le _ _)
    norm_num [he]
  · simp only [timeValue,encode,qmaHistoryTermTime]
    norm_num

theorem bucket_actual (c : QMACircuit) (hT : 0 < c.gates.length)
    (t : Fin c.gates.length) :
    bucket c t.val =
      ((qmaHistoryTermList c).filter
        (fun a => decide (qmaHistoryTermTime c hT (qmaFirstUseTime c) a=t))).map
        (encode c) := by
  rw [bucket,source_actual,List.filter_map]
  congr 1
  apply List.filter_congr
  intro a _
  change decide (timeValue c (encode c a)=t.val) = _
  rw [time_encode c hT]
  simp only [Fin.ext_iff]

theorem ordered_actual (c : QMACircuit) (hT : 0 < c.gates.length) :
    ordered c=(qmaOrderedHistoryTerms c hT (qmaFirstUseTime c)).map (encode c) := by
  unfold ordered qmaOrderedHistoryTerms qmaGroupByTime
  rw [List.map_flatMap]
  have hr : List.range c.gates.length =
      (List.ofFn (fun t : Fin c.gates.length => t)).map Fin.val := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp only [List.getElem_range,List.getElem_map,List.getElem_ofFn]
  rw [hr,List.flatMap_map]
  apply List.flatMap_congr
  intro t _
  exact bucket_actual c hT t

theorem ordered_length (c : QMACircuit) (hT : 0 < c.gates.length) :
    (ordered c).length=qmaHistoryReferenceWork c+1 := by
  rw [ordered_actual c hT,List.length_map,qmaOrderedHistoryTerms_length]

end ContinuumCoulomb.QuantumHistoryDescriptors

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedWeightProgram
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform literal rational-list programs for all five early gadget stages.
The lists retain input order and emit each fixed block in its word order. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedWeightProgram
open ExactQuantumFactoring.BitStackProgram
open scoped BigOperators Classical

noncomputable opaque radiusSquare : Procedure pairCode ratCode (fun x => x.1^2) :=
  QuantumRoutingCode.squareProgram radius
noncomputable opaque radiusCube : Procedure pairCode ratCode (fun x => x.1^3) :=
  (Procedure.ratMul.comp (radiusSquare.pair radius)).congrFun (by intro x; dsimp; ring)
noncomputable opaque radiusHalf : Procedure pairCode ratCode (fun x => x.1^2/2) :=
  Procedure.ratDiv.comp (radiusSquare.pair (Procedure.constant pairCode ratCode 2))
noncomputable opaque cubeHalf : Procedure pairCode ratCode (fun x => x.1^3/2) :=
  Procedure.ratDiv.comp (radiusCube.pair (Procedure.constant pairCode ratCode 2))
noncomputable opaque correction : Procedure pairCode ratCode (fun x => 1+(x.2/2)^2) :=
  Procedure.ratAdd.comp ((Procedure.constant pairCode ratCode 1).pair
    (QuantumRoutingCode.squareProgram couplingHalf))

noncomputable opaque fourProgram (k : Fin 4) : Procedure pairCode ratCode
    (fun x => QuantumPolarizedSubdivision.weight x.1 x.2 k) := by
  refine Fin.cases ?_ (fun k => ?_) k
  · exact (Procedure.ratAdd.comp (radiusHalf.pair correction)).congrFun
      (by intro x; change x.1^2/2+(1+(x.2/2)^2) = x.1^2/2+1+(x.2/2)^2; ring)
  · refine Fin.cases ?_ (fun k => ?_) k
    · exact (Procedure.ratNeg.comp radiusHalf).congrFun (by
        intro x; change -(x.1^2/2) = -x.1^2/2; ring)
    · refine Fin.cases ?_ (fun k => ?_) k
      · exact radius.congrFun (by intro x; rfl)
      · refine Fin.cases ?_ (fun k => Fin.elim0 k) k
        exact (Procedure.ratDiv.comp ((Procedure.ratMul.comp
          ((Procedure.ratNeg.comp radius).pair coupling)).pair
            (Procedure.constant pairCode ratCode 2))).congrFun (by intro x; rfl)

noncomputable opaque sevenProgram (k : Fin 7) : Procedure pairCode ratCode
    (fun x => QuantumPolarizedThird.weight x.1 x.2 k) := by
  refine Fin.cases ?_ (fun k => ?_) k
  · exact (Procedure.ratAdd.comp (cubeHalf.pair
      (Procedure.ratMul.comp (radius.pair correction)))).congrFun (by intro x; rfl)
  · refine Fin.cases ?_ (fun k => ?_) k
    · exact (Procedure.ratNeg.comp cubeHalf).congrFun (by
        intro x; change -(x.1^3/2) = -x.1^3/2; ring)
    · refine Fin.cases ?_ (fun k => ?_) k
      · exact (Procedure.ratMul.comp (radius.pair coupling)).congrFun (by intro x; rfl)
      · refine Fin.cases ?_ (fun k => ?_) k
        · exact (Procedure.ratSub.comp (radiusHalf.pair correction)).congrFun (by intro x; rfl)
        · refine Fin.cases ?_ (fun k => ?_) k
          · exact (Procedure.ratNeg.comp radiusHalf).congrFun (by
              intro x; change -(x.1^2/2) = -x.1^2/2; ring)
          · refine Fin.cases ?_ (fun k => ?_) k
            · exact radiusSquare.congrFun (by intro x; rfl)
            · refine Fin.cases ?_ (fun k => Fin.elim0 k) k
              exact (Procedure.ratDiv.comp ((Procedure.ratMul.comp (radiusSquare.pair coupling)).pair
                (Procedure.constant pairCode ratCode 2))).congrFun (by intro x; rfl)

noncomputable opaque scaleProgram : Procedure inputCode ratCode scale := by
  let n := Procedure.natToRat.comp (Procedure.unaryToBits.comp
    (Procedure.first unaryCode (listCode ratCode)))
  let s := (QuantumPathScaleProgram.sumMapProgram QuantumPathScaleProgram.squareProgram).comp
    (Procedure.second unaryCode (listCode ratCode))
  let b := Procedure.ratMul.comp ((Procedure.constant inputCode ratCode 4).pair
    (Procedure.ratAdd.comp ((Procedure.constant inputCode ratCode 1).pair s)))
  let fourth := QuantumRoutingCode.squareProgram (QuantumRoutingCode.squareProgram b)
  exact (Procedure.ratMul.comp ((Procedure.ratMul.comp
    ((Procedure.constant inputCode ratCode 8).pair fourth)).pair n)).congrFun (by
      intro x
      simp only [Function.comp_apply,id_eq,scale,
        show QuantumPathScaleProgram.squareCost = (fun j : ℚ => (1+|j|)^2) from rfl]
      ring)

end ContinuumCoulomb.QuantumOrderedWeightProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedLabelFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal indexed list stage, shared by the six fixed local reductions.
New mediator indices are the old qubit count plus the input term index.
Unary counts bound the output size; rational coefficients stay binary. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedLabelFamily
open ExactQuantumFactoring.BitStackProgram
open QuantumOrderedLabelData

noncomputable opaque radiusProgram : Procedure inputCode ratCode radius :=
  QuantumOrderedWeightProgram.scaleProgram.comp weightsProgram

noncomputable opaque indexedProgram : Procedure (prodCode unaryCode inputCode) blockCode indexed := by
  let i := Procedure.first unaryCode inputCode
  let x := Procedure.second unaryCode inputCode
  let n := (Procedure.unaryToBits.comp countProgram).comp x
  let j := Procedure.unaryToBits.comp i
  let selected :=  (Procedure.listGet entryCode ([],0)).comp (j.pair (entriesProgram.comp x))
  exact ((Procedure.binaryAdd.comp (n.pair j)).pair (radiusProgram.comp x)).pair selected

noncomputable def blockProgram (d : ℕ)
    (f : ℕ → List Letter → Fin d → List Letter) (g : ℚ → ℚ → Fin d → ℚ)
    (pf : ∀ k, Procedure QuantumOrderedLabelData.blockCode labelsCode (fun x => f x.1 x.2 k))
    (pg : ∀ k, Procedure QuantumOrderedWeightProgram.pairCode ratCode (fun x => g x.1 x.2 k)) :
    Procedure blockCode (listCode entryCode) (block d f g) := by
  let params := Procedure.first (prodCode Nat.bits ratCode) entryCode
  let entry := Procedure.second (prodCode Nat.bits ratCode) entryCode
  let mediator := (Procedure.first Nat.bits ratCode).comp params
  let scale := (Procedure.second Nat.bits ratCode).comp params
  let labels := (Procedure.first labelsCode ratCode).comp entry
  let coefficient := (Procedure.second labelsCode ratCode).comp entry
  exact QuantumRawExchange.fixedListProgram blockCode entryCode d _
    (fun k => ((pf k).comp (mediator.pair labels)).pair
      ((pg k).comp (scale.pair coefficient)))

noncomputable def familyProgram (d : ℕ)
    (f : ℕ → List Letter → Fin d → List Letter) (g : ℚ → ℚ → Fin d → ℚ)
    (p : Procedure blockCode (listCode entryCode) (block d f g)) :
    Procedure inputCode (listCode entryCode) (family d f g) := by
  let tab := Procedure.tabulate (f := fun x i => block d f g (indexed (i,x))) []
    (p.comp indexedProgram)
  exact (QuantumRawExchange.flattenProgram entryCode ([],0)).comp
    (tab.comp (lengthProgram.pair (Procedure.identity inputCode)))

noncomputable def valueProgram (d : ℕ)
    (f : ℕ → List Letter → Fin d → List Letter) (g : ℚ → ℚ → Fin d → ℚ)
    (p : Procedure blockCode (listCode entryCode) (block d f g)) :
    Procedure inputCode stateCode (value d f g) :=
  (Procedure.unaryAdd.comp (countProgram.pair lengthProgram)).pair (familyProgram d f g p)

end ContinuumCoulomb.QuantumOrderedLabelFamily

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPaddedHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal 4096-word family for each actual ordered history term.  The
term type is a product, so its emitted order requires no filtered finite type. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPaddedHistory
open QuantumAlgebraicHistory
open scoped BigOperators Classical

def tableMatrix (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c)) :=
  denote (orderedTable c hT a)

def word (c : QMACircuit) (hT : 0 < c.gates.length) (p : Term c) :
    (qmaOrderedHistoryModel c hT).Q → Fin 4 :=
  QuantumPaddedLocal.word ((qmaOrderedHistoryModel c hT).sites p.1)
    (QuantumOrderedSupport.supportEquiv c hT p.1)
    (6-(QuantumOrderedSupport.sites c hT p.1).length)
    (widthIndex _ (QuantumOrderedSupport.sites_length c hT p.1) p.2)

def coefficient (c : QMACircuit) (hT : 0 < c.gates.length) (p : Term c) : ℝ :=
  QuantumPaddedPauli.paddedCoefficient
    (QuantumOrderedSupport.sites c hT p.1).length
    (6-(QuantumOrderedSupport.sites c hT p.1).length)
    (tableMatrix c hT p.1)
    (widthIndex _ (QuantumOrderedSupport.sites_length c hT p.1) p.2)

end ContinuumCoulomb.QuantumPaddedHistory

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedDescriptorProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal polynomial program for the exact time-grouped descriptor list. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryDescriptors
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode

noncomputable opaque bucketProgram : Procedure bucketCode (listCode descriptorCode)
    (fun x => bucket x.1 x.2) := by
  let chunks := (Procedure.listMapWith (f := fun e d => chunk (e,d)) (0,0) []
    chunkProgram).comp ((Procedure.identity bucketCode).pair
      (sourceProgram.comp (Procedure.first circuitCode Nat.bits)))
  exact ((QuantumRawExchange.flattenProgram descriptorCode (0,0)).comp chunks).congrFun
    (by intro x; exact chunks_eq x.1 x.2 (source x.1))

noncomputable opaque orderedEntryProgram :
    Procedure (prodCode unaryCode circuitCode) (listCode descriptorCode)
      (fun x => bucket x.2 x.1) :=
  bucketProgram.comp ((Procedure.second unaryCode circuitCode).pair
    (Procedure.unaryToBits.comp (Procedure.first unaryCode circuitCode)))

noncomputable opaque orderedProgram : Procedure circuitCode (listCode descriptorCode) ordered :=
  ((QuantumRawExchange.flattenProgram descriptorCode (0,0)).comp
    ((Procedure.tabulate (f := fun c i => bucket c i) [] orderedEntryProgram).comp
      (timeProgram.pair (Procedure.identity circuitCode)))).congrFun (by
        intro c
        simp only [ordered,List.flatMap_def,Function.comp_apply,id_eq])

end ContinuumCoulomb.QuantumHistoryDescriptors

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSupportDedup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The support compiler retains the last occurrence of each numeric label,
exactly as `List.dedup` does in the mathematical ordered support. -/

noncomputable section
open scoped List
namespace ContinuumCoulomb.QuantumSupportDedup
open ExactQuantumFactoring.BitStackProgram

noncomputable opaque insertProgram :
    Procedure (prodCode Nat.bits (listCode Nat.bits)) (listCode Nat.bits)
      (fun x => insert x.1 x.2) :=
  (Procedure.conditional (QuantumFiniteMembership.memberProgram Nat.bits 0 Procedure.binaryEq)
    (Procedure.second Nat.bits (listCode Nat.bits)) (Procedure.listCons Nat.bits)).congrFun
      (by intro x; simp only [insert,decide_eq_true_eq])

noncomputable opaque foldProgram :
    Procedure (prodCode (listCode Nat.bits) (listCode Nat.bits)) (listCode Nat.bits)
      (fun x => x.1.foldl (fun zs a => insert a zs) x.2) :=
  Procedure.foldList 0 insertProgram Polynomial.X (by
    intro xs ys i
    have h := fold_bound (xs.take i) ys
    have ht := listCode_length_take_le Nat.bits i xs
    simp only [Polynomial.eval_X]
    omega)

noncomputable opaque program : Procedure (listCode Nat.bits) (listCode Nat.bits) List.dedup :=
  (foldProgram.comp ((Procedure.listReverse Nat.bits 0).pair
    (Procedure.constant (listCode Nat.bits) (listCode Nat.bits) []))).congrFun (by
      intro xs
      simp only [Function.comp_apply,List.foldl_reverse,foldr_eq])

end ContinuumCoulomb.QuantumSupportDedup

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumDescriptorSiteProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial programs for the exact numeric support lists of every
time-ordered rebit term and reference edge. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryDescriptors
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode

noncomputable opaque orderedAtProgram : Procedure referenceCode descriptorCode
    (fun x => orderedAt x.1 x.2) :=
  (Procedure.listGet descriptorCode (0,0)).comp
    ((Procedure.second circuitCode Nat.bits).pair
      (orderedProgram.comp (Procedure.first circuitCode Nat.bits)))

noncomputable opaque rebitLabelsProgram : Procedure referenceCode (listCode Nat.bits)
    (fun x => rebitLabels x.1 x.2) := by
  let c := Procedure.first circuitCode Nat.bits
  let i := Procedure.second circuitCode Nat.bits
  let offset := Procedure.successor.comp (referenceWorkProgram.comp c)
  let labels := distributedLabelsProgram.comp (c.pair orderedAtProgram)
  let shifted := (Procedure.listMapWith (f := fun a b : ℕ => a+b) 0 0
    Procedure.binaryAdd).comp (offset.pair labels)
  exact consLabel i shifted

noncomputable opaque referenceLabelsProgram : Procedure referenceCode (listCode Nat.bits)
    (fun x => referenceLabels x.1 x.2) := by
  let c := Procedure.first circuitCode Nat.bits
  let i := Procedure.second circuitCode Nat.bits
  let cut := Procedure.successor.comp (referenceWorkProgram.comp c)
  let edge := Procedure.binarySub.comp (i.pair cut)
  let labels := consLabel edge (oneLabel (Procedure.successor.comp edge))
  exact (Procedure.conditional (Procedure.binaryLt.comp (i.pair cut)) rebitLabelsProgram
    labels).congrFun (by
      intro x
      simp only [referenceLabels,Function.comp_apply,decide_eq_true_eq])

noncomputable opaque supportLabelsProgram : Procedure referenceCode (listCode Nat.bits)
    (fun x => supportLabels x.1 x.2) := QuantumSupportDedup.program.comp referenceLabelsProgram

end ContinuumCoulomb.QuantumHistoryDescriptors

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFixedPauliProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal polynomial evaluator for every coefficient of a fixed
local core.  Six is the largest arity used by the history construction;
the finite loops below are part of the fixed program, not the input. -/

noncomputable section
namespace ContinuumCoulomb.QuantumFixedPauli
open QuantumAlgebraicScalar ExactQuantumFactoring.BitStackProgram
open scoped Classical

attribute [local instance] OAI.ContinuumCoulomb.QuantumFixedPauli.finDecision
noncomputable def finiteSumProgram {α β : Type} [Fintype β]
    (ea : α → List Bool) (f : β → α → Scalar)
    (p : ∀ i, Procedure ea scalarCode (f i)) :
    Procedure ea scalarCode (fun x => finiteSum (fun i => f i x)) :=
  (fixedSumProgram ea (Fintype.card β)
    (fun i => f ((Fintype.equivFin β).symm i))
    (fun i => p ((Fintype.equivFin β).symm i))).congrFun (by
      intro x
      simp only [finiteSum,enumerate,List.map_ofFn,Function.comp_def])

noncomputable opaque coefficientCellProgram (n : ℕ) (w : Fin n → Fin 4)
    (s t : Fin n → Fin 2) : Procedure matrixCode scalarCode
      (fun xs => mul (entry xs s t) (word w t s)) :=
  mulProgram.comp
    ((entryProgram s t).pair (Procedure.constant matrixCode scalarCode (word w t s)))

noncomputable opaque coefficientRowProgram (n : ℕ) (w : Fin n → Fin 4)
    (s : Fin n → Fin 2) : Procedure matrixCode scalarCode
      (fun xs => finiteSum (fun t => mul (entry xs s t) (word w t s))) :=
  finiteSumProgram matrixCode _ (coefficientCellProgram n w s)

noncomputable opaque coefficientTotalProgram (n : ℕ) (w : Fin n → Fin 4) :
    Procedure matrixCode scalarCode
      (fun xs => finiteSum (fun s : Fin n → Fin 2 =>
        finiteSum (fun t => mul (entry xs s t) (word w t s)))) :=
  finiteSumProgram matrixCode _ (coefficientRowProgram n w)

noncomputable opaque coefficientProgram (n : ℕ) (w : Fin n → Fin 4) :
    Procedure matrixCode scalarCode
      (fun xs => coefficient (fun s t : Fin n → Fin 2 => entry xs s t) w) := by
  let c : Scalar := rat (((2:ℚ)^Fintype.card (Fin n))⁻¹)
  let pc : Procedure matrixCode scalarCode (fun _ => c) :=
    Procedure.constant matrixCode scalarCode c
  let pt := coefficientTotalProgram n w
  let pp : Procedure matrixCode (prodCode scalarCode scalarCode)
      (fun xs => (c,finiteSum (fun s : Fin n → Fin 2 =>
        finiteSum (fun t => mul (entry xs s t) (word w t s))))) := pc.pair pt
  exact (mulProgram.comp pp).congrFun (by intro xs; rfl)

noncomputable def realCoefficientProgram (n : ℕ) (w : Fin n → Fin 4) :
    Procedure matrixCode realCode
      (fun xs => realCoefficient (fun s t : Fin n → Fin 2 => entry xs s t) w) :=
  (Procedure.first realCode realCode).comp (coefficientProgram n w)

end ContinuumCoulomb.QuantumFixedPauli

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFixedMatrixProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal arithmetic on a fixed local matrix table.  These templates implement
the adjoint-product and realification used in the actual history cores; their
matrix dimensions are fixed before the program receives its rational registers. -/

noncomputable section
namespace ContinuumCoulomb.QuantumFixedMatrix
open QuantumFixedPauli QuantumAlgebraicScalar QuantumAlgebraicHistory
open ExactQuantumFactoring.BitStackProgram
open scoped Classical

noncomputable def dataProgram {α β : Type} [Fintype β] (ea : α → List Bool)
    (A : α → Matrix β β Scalar)
    (p : ∀ s t, Procedure ea scalarCode (fun x => A x s t)) :
    Procedure ea matrixCode (fun x => matrixData (A x)) :=
  (QuantumRawExchange.fixedListProgram ea scalarCode (Fintype.card (β×β))
    (fun i x => A x ((Fintype.equivFin (β×β)).symm i).1
      ((Fintype.equivFin (β×β)).symm i).2)
    (fun i => p _ _)).congrFun (by
      intro x
      simp only [matrixData,enumerate,List.map_ofFn,Function.comp_def])

noncomputable opaque gramCellProgram {β : Type} [Fintype β] (s t u : β) :
    Procedure matrixCode scalarCode (fun xs => mul (conj (entry xs u s)) (entry xs u t)) :=
  mulProgram.comp ((conjProgram.comp (entryProgram u s)).pair (entryProgram u t))

noncomputable opaque gramEntryProgram {β : Type} [Fintype β] (s t : β) :
    Procedure matrixCode scalarCode
      (fun xs => matMul (adjoint (fun a b : β => entry xs a b))
        (fun a b : β => entry xs a b) s t) :=
  finiteSumProgram matrixCode _ (fun u => gramCellProgram s t u)

noncomputable def gramProgram (β : Type) [Fintype β] :
    Procedure matrixCode matrixCode (gramData (β := β)) :=
  dataProgram matrixCode _ gramEntryProgram

end ContinuumCoulomb.QuantumFixedMatrix

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSupportLookup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual local support coordinates are read by literal label lookup.
This identifies a small matrix input with its zero extension on spectator
qubits, without enumerating the ambient spin basis. -/

noncomputable section
namespace ContinuumCoulomb.QuantumSupportLookup
open ExactQuantumFactoring.BitStackProgram

open QuantumOrderedSupport
open scoped Classical

def supportBits (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c))
    (s : Fin (sites c hT a).length → Fin 2) : List ℕ :=
  List.ofFn (fun i => (s i).val)

end ContinuumCoulomb.QuantumSupportLookup

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryDiagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The four diagonal descriptor cases are evaluated directly from their
clock/work bits.  Their values are exact rational entries of the actual
distributed history operator, before the rebit construction. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryDiagonal
open QuantumHistoryDescriptors QuantumHistorySiteProgram QuantumHistoryBitProgram
open QuantumAlgebraicScalar
open scoped Classical

def supportData (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c))
    (s t : Fin (QuantumOrderedSupport.sites c hT a).length → Fin 2) : Data :=
  (QuantumOrderedSupport.encodedSites c hT a,
    QuantumSupportLookup.supportBits c hT a s,QuantumSupportLookup.supportBits c hT a t)

end ContinuumCoulomb.QuantumHistoryDiagonal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRebitDiagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A real diagonal term remains diagonal under the reference-spin rebit
construction.  These entry identities avoid any sum over spectators. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryDiagonal
open QuantumAlgebraicHistory QuantumAlgebraicScalar
open scoped Classical

def orderedExtend (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c))
    (s : Fin (QuantumOrderedSupport.sites c hT a).length → Fin 2) :
    QuantumOrderedSupport.Qubit c → Fin 2 :=
  qmaSupportExtend ((qmaOrderedHistoryModel c hT).sites a)
    (fun j => s ((QuantumOrderedSupport.supportEquiv c hT a).symm j))

end ContinuumCoulomb.QuantumHistoryDiagonal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumDiagonalTableProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed-arity scalar tables for the actual diagonal history terms.
Only the local support bits are tabulated; the arity is at most six. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryDiagonal
open ExactQuantumFactoring.BitStackProgram QuantumAlgebraicScalar QuantumFixedPauli
open QuantumCircuitCode QuantumHistoryDescriptors
open scoped Classical

noncomputable def tableProgram (n : ℕ) :
    Procedure tableCode matrixCode (tableList n) :=
  QuantumFixedMatrix.dataProgram tableCode (table n) (tableEntryProgram n)

end ContinuumCoulomb.QuantumHistoryDiagonal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPairDedup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The crossing compiler retains one occurrence of each coordinate pair,
with an output bound from the original list. -/

noncomputable section
open scoped List Classical
namespace ContinuumCoulomb.QuantumPairDedup
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

noncomputable opaque insertProgram :
    Procedure (prodCode pairCode (listCode pairCode)) (listCode pairCode)
      (fun x => insertPair x.1 x.2) :=
  (Procedure.conditional (QuantumFiniteMembership.memberProgram pairCode (0,0) QuantumFiniteMembership.pairEqProgram)
    (Procedure.second pairCode (listCode pairCode)) (Procedure.listCons pairCode)).congrFun
      (by intro x; simp only [insertPair,decide_eq_true_eq])

noncomputable opaque foldProgram :
    Procedure (prodCode (listCode pairCode) (listCode pairCode)) (listCode pairCode)
      (fun x => x.1.foldl (fun zs a => insertPair a zs) x.2) :=
  Procedure.foldList (0,0) insertProgram Polynomial.X (by
    intro xs ys i
    have h := fold_bound (xs.take i) ys
    have ht := listCode_length_take_le pairCode i xs
    simp only [Polynomial.eval_X]
    convert h.trans (Nat.add_le_add_right ht _) using 1)

noncomputable opaque program : Procedure (listCode pairCode) (listCode pairCode) List.dedup :=
  (foldProgram.comp ((Procedure.listReverse pairCode (0,0)).pair
    (Procedure.constant (listCode pairCode) (listCode pairCode) []))).congrFun (by
      intro xs
      simp only [Function.comp_apply,List.foldl_reverse,foldr_eq])

end ContinuumCoulomb.QuantumPairDedup

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPathTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite lists of actual routes produce a routing table with exactly
the permissions of the physical graph proof. Lists may use any complete edge
order; this does not change a routing decision. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode QuantumRoutingTable QuantumPathVisitProgram
namespace QuantumPathTable

noncomputable def compileProgram : Procedure inputCode tableCode compile := by
  let sources := Procedure.first (listCode pairCode) (listCode (listCode pairCode))
  let paths := Procedure.second (listCode pairCode) (listCode (listCode pairCode))
  let vs := (QuantumRawExchange.flattenProgram visitCode ((0,0),(0,0))).comp
    ((Procedure.listMap [] [] visitsProgram).comp paths)
  let base := sources.pair (vs.pair (Procedure.constant inputCode (listCode pairCode) []))
  exact computedTableProgram.comp base

 theorem beforeCrossings_visits {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)
    (es : List G.Edge) (hcover : ∀ e, e ∈ es) (v : Visit) :
    v ∈ (beforeCrossings (List.ofFn P.position,es.map P.routeList)).2.1 ↔
      v ∈ P.routingTable.2.1 := by
  change v ∈ ((es.map P.routeList).map visits).flatten ↔ _
  rw [List.map_map]
  exact P.listedVisits_mem es hcover v

 theorem compile_crossings {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)
    (es : List G.Edge) (hcover : ∀ e, e ∈ es) (p : Pair) :
    p ∈ (compile (List.ofFn P.position,es.map P.routeList)).2.2 ↔ P.IsCrossing p := by
  change p ∈ computedCrossings (beforeCrossings (List.ofFn P.position,es.map P.routeList)) ↔ _
  rw [mem_computedCrossings]
  simp only [crossingTest,Bool.and_eq_true,decide_eq_true_eq,
    beforeCrossings_visits P es hcover]
  exact (P.crossing_iff_opposite_visits p).symm

end QuantumPathTable
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumDistinctCrossings
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite crossing list, with duplicates removed, enumerates
each physical crossing cell exactly once. -/

noncomputable section
namespace ContinuumCoulomb.QuantumDistinctCrossings
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode
open scoped Classical

noncomputable opaque program :
    Procedure QuantumPathTable.inputCode (listCode pairCode) value :=
  QuantumPairDedup.program.comp
    (((Procedure.second (listCode QuantumRoutingTable.visitCode) (listCode pairCode)).comp
      (Procedure.second (listCode pairCode)
        (prodCode (listCode QuantumRoutingTable.visitCode) (listCode pairCode)))).comp
      QuantumPathTable.compileProgram)

theorem mem_actual {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)
    (es : List G.Edge) (hcover : ∀ e, e ∈ es) (p : Pair) :
    p ∈ value (List.ofFn P.position,es.map P.routeList) ↔ P.IsCrossing p := by
  rw [value,List.mem_dedup]
  exact QuantumPathTable.compile_crossings P es hcover p

variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)
    (es : List G.Edge) (hcover : ∀ e, e ∈ es)

def cell (i : Fin (value (List.ofFn P.position,es.map P.routeList)).length) : P.Crossing :=
  ⟨(value (List.ofFn P.position,es.map P.routeList)).get i,
    P.mem_crossingCells.mpr ((mem_actual P es hcover _).mp (List.get_mem _ i))⟩

theorem cell_bijective : Function.Bijective (cell P es hcover) := by
  constructor
  · intro i j hij
    exact (nodup _).injective_get (congrArg Subtype.val hij)
  · intro c
    have hc : c.val ∈ value (List.ofFn P.position,es.map P.routeList) :=
      (mem_actual P es hcover _).mpr (P.mem_crossingCells.mp c.property)
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp hc
    exact ⟨i,Subtype.ext hi⟩

def cellsEquiv : Fin (value (List.ofFn P.position,es.map P.routeList)).length ≃ P.Crossing :=
  Equiv.ofBijective (cell P es hcover) (cell_bijective P es hcover)

end ContinuumCoulomb.QuantumDistinctCrossings

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRawSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! All four-spin scales and precisions are computed from the raw finite input. -/

noncomputable section
namespace ContinuumCoulomb.QuantumRawExchange
open QuantumAxisSample MediatorListProgram ExactQuantumFactoring.BitStackProgram

noncomputable opaque rawAbsoluteProgram : Procedure rawCode ratCode (fun t => |t.2.2.2|) :=
  MediatorProgram.absoluteProgram.comp rawWeightProgram
noncomputable opaque massProgram : Procedure (listCode rawCode) ratCode mass :=
  RationalSumProgram.sumProgram.comp (Procedure.listMap zeroRaw 0 rawAbsoluteProgram)

noncomputable opaque scheduleMassProgram : Procedure scheduleCode ratCode (fun x => mass x.2.2) :=
  massProgram.comp scheduleTermsProgram
noncomputable opaque sizeProgram : Procedure scheduleCode ratCode (fun x => size x.2.2) :=
  Procedure.ratAdd.comp (scheduleLengthRatProgram.pair scheduleMassProgram)
noncomputable opaque linearBudgetProgram : Procedure scheduleCode ratCode (fun x => 2000000*size x.2.2) :=
  Procedure.ratMul.comp ((Procedure.constant scheduleCode ratCode 2000000).pair sizeProgram)
noncomputable opaque quadraticBaseProgram : Procedure scheduleCode ratCode (fun x => 7056*size x.2.2) :=
  Procedure.ratMul.comp ((Procedure.constant scheduleCode ratCode 7056).pair sizeProgram)
noncomputable opaque quadraticBudgetProgram : Procedure scheduleCode ratCode (fun x => (7056*size x.2.2)^2) :=
  (Procedure.ratMul.comp (quadraticBaseProgram.pair quadraticBaseProgram)).congrFun
    (by intro x; change _*_ = _^2; ring)
noncomputable opaque budgetProgram : Procedure scheduleCode ratCode (fun x => budget x.2.2) :=
  Procedure.ratAdd.comp ((Procedure.ratAdd.comp
    ((Procedure.constant scheduleCode ratCode 1).pair linearBudgetProgram)).pair quadraticBudgetProgram)
noncomputable opaque squareBudgetProgram : Procedure scheduleCode ratCode (fun x => (budget x.2.2)^2) :=
  (Procedure.ratMul.comp (budgetProgram.pair budgetProgram)).congrFun
    (by intro x; change _*_ = _^2; ring)
noncomputable opaque cubeBudgetProgram : Procedure scheduleCode ratCode (fun x => (budget x.2.2)^3) :=
  (Procedure.ratMul.comp (squareBudgetProgram.pair budgetProgram)).congrFun
    (by intro x; change _^2*_ = _^3; ring)
noncomputable opaque scheduleScaleProgram : Procedure scheduleCode ratCode (fun x => scale x.2.1 x.2.2) :=
  Procedure.ratMul.comp ((Procedure.ratMul.comp
    ((Procedure.constant scheduleCode ratCode 9).pair cubeBudgetProgram)).pair accuracyRatProgram)
noncomputable opaque absoluteScaleProgram : Procedure scheduleCode ratCode (fun x => |scale x.2.1 x.2.2|) :=
  MediatorProgram.absoluteProgram.comp scheduleScaleProgram
noncomputable opaque crossBudgetProgram : Procedure scheduleCode ratCode
    (fun x => 1568*|scale x.2.1 x.2.2| *(1+size x.2.2)) :=
  Procedure.ratMul.comp ((Procedure.ratMul.comp
    ((Procedure.constant scheduleCode ratCode 1568).pair absoluteScaleProgram)).pair
    (Procedure.ratAdd.comp ((Procedure.constant scheduleCode ratCode 1).pair sizeProgram)))
noncomputable opaque fieldBudgetProgram : Procedure scheduleCode ratCode (fun x => 26064*size x.2.2) :=
  Procedure.ratMul.comp ((Procedure.constant scheduleCode ratCode 26064).pair sizeProgram)
noncomputable opaque matrixBudgetProgram : Procedure scheduleCode ratCode
    (fun x => 3*(6*(x.1:ℚ)+25*(x.2.2.length:ℚ))*
      (1568*|scale x.2.1 x.2.2| *(1+size x.2.2)+26064*size x.2.2)) :=
  Procedure.ratMul.comp ((Procedure.ratMul.comp
    ((Procedure.constant scheduleCode ratCode 3).pair edgeCountProgram)).pair
      (Procedure.ratAdd.comp (crossBudgetProgram.pair fieldBudgetProgram)))
noncomputable opaque scalarBudgetProgram : Procedure scheduleCode ratCode (fun x => 320800*mass x.2.2) :=
  Procedure.ratMul.comp ((Procedure.constant scheduleCode ratCode 320800).pair scheduleMassProgram)
noncomputable opaque errorBoundProgram : Procedure scheduleCode ratCode errorBound :=
  Procedure.ratAdd.comp (matrixBudgetProgram.pair scalarBudgetProgram)
noncomputable opaque bitsProgram : Procedure scheduleCode unaryCode bits :=
  QuantumAxisSample.precisionProgram.comp (errorBoundProgram.pair accuracyProgram)
noncomputable opaque scheduledProgram : Procedure scheduleCode fullCode scheduled :=
  scheduleCountProgram.pair ((bitsProgram.pair scheduleScaleProgram).pair scheduleTermsProgram)
noncomputable opaque compileProgram : Procedure scheduleCode (prodCode (listCode bondCode) ratCode) compile :=
  (fullBondsProgram.pair fullScalarProgram).comp scheduledProgram

end ContinuumCoulomb.QuantumRawExchange

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal finite-list programs for the active-port pairs in a fork round.
Only the finite input lists are enumerated; spin Hilbert-space bases are absent. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open ExactQuantumFactoring.BitStackProgram

noncomputable def catalogProgram : Procedure groupsCode (listCode taggedCode) catalog := by
  let count := ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength (listCode portCode) []
  let blocks := (Procedure.tabulate (f := fun gs i =>
    (pairs (groupAt gs i)).map (fun p => (i,p))) [] taggedPairsProgram).comp
      (count.pair (Procedure.identity groupsCode))
  exact (QuantumRawExchange.flattenProgram taggedCode (0,((0,0),(0,0)))).comp blocks

noncomputable def pairCountProgram : Procedure groupsCode unaryCode pairCount :=
  ((ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength taggedCode (0,((0,0),(0,0)))).comp
    catalogProgram).congrFun catalog_length

noncomputable def retainedProgram : Procedure stateCode (listCode ratCode) retained := by
  let tail := Procedure.second unaryCode
    (prodCode (listCode MediatorListProgram.bondCode) (prodCode ratCode groupsCode))
  let bs := (Procedure.first (listCode MediatorListProgram.bondCode) (prodCode ratCode groupsCode)).comp tail
  let gs := (Procedure.second ratCode groupsCode).comp
    ((Procedure.second (listCode MediatorListProgram.bondCode) (prodCode ratCode groupsCode)).comp tail)
  let weights := (Procedure.listMap (0,0,0) 0
    ((Procedure.second Nat.bits ratCode).comp
      (Procedure.second Nat.bits (prodCode Nat.bits ratCode)))).comp bs
  let leftovers := (QuantumRawExchange.flattenProgram portCode (0,0)).comp
    ((Procedure.listMap [] [] unpairedProgram).comp gs)
  let leftoverWeights := (Procedure.listMap (0,0) 0 (Procedure.second Nat.bits ratCode)).comp leftovers
  exact (Procedure.listAppend ratCode 0).comp (weights.pair leftoverWeights)

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact rational calibration for the ordered fork list. The perturbation
scale includes the unpaired active ports in its retained-energy bound. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open ExactQuantumFactoring.BitStackProgram

noncomputable def pairLinearProgram : Procedure pairCode ratCode pairLinear := by
  let a := MediatorProgram.absoluteProgram.comp leftWeight
  let b := MediatorProgram.absoluteProgram.comp rightWeight
  let two := Procedure.constant pairCode ratCode 2
  exact Procedure.ratAdd.comp
    ((Procedure.ratAdd.comp ((Procedure.constant pairCode ratCode 1).pair
      (Procedure.ratMul.comp (two.pair a)))).pair (Procedure.ratMul.comp (two.pair b)))

noncomputable def pairSquareProgram : Procedure pairCode ratCode pairSquare := by
  let a := MediatorProgram.absoluteProgram.comp leftWeight
  let b := MediatorProgram.absoluteProgram.comp rightWeight
  exact QuantumRoutingCode.squareProgram (Procedure.ratAdd.comp
    ((Procedure.ratAdd.comp ((Procedure.constant pairCode ratCode 1).pair a)).pair b))

noncomputable def pairOffsetProgram : Procedure pairCode ratCode pairOffset := by
  let a := QuantumRoutingCode.squareProgram leftWeight
  let b := QuantumRoutingCode.squareProgram rightWeight
  let three := Procedure.constant pairCode ratCode 3
  exact Procedure.ratAdd.comp
    ((Procedure.ratAdd.comp ((Procedure.constant pairCode ratCode (3/4)).pair
      (Procedure.ratMul.comp (three.pair a)))).pair (Procedure.ratMul.comp (three.pair b)))

noncomputable def scaleProgram : Procedure scaleCode ratCode (fun x => scale x.1 x.2) := by
  let n := Procedure.first ratCode stateCode
  let s := Procedure.second ratCode stateCode
  let c := scalarProgram.comp s
  let gs := groupsProgram.comp s
  let ps := (Procedure.listMap (0,((0,0),(0,0))) ((0,0),(0,0))
    (Procedure.second Nat.bits pairCode)).comp (catalogProgram.comp gs)
  let sumPairs (f : Pair → ℚ) (p : Procedure pairCode ratCode f) :=
    RationalSumProgram.sumProgram.comp ((Procedure.listMap ((0,0),(0,0)) 0 p).comp ps)
  let absRetained := (QuantumPathScaleProgram.sumMapProgram MediatorProgram.absoluteProgram).comp
    (retainedProgram.comp s)
  let b := Procedure.ratAdd.comp
    ((Procedure.ratMul.comp ((Procedure.constant scaleCode ratCode 3).pair absRetained)).pair
      (MediatorProgram.absoluteProgram.comp c))
  let a := Procedure.ratMul.comp ((Procedure.constant scaleCode ratCode 3).pair
    (sumPairs pairLinear pairLinearProgram))
  let d := Procedure.ratAdd.comp (b.pair
    (Procedure.ratMul.comp ((Procedure.constant scaleCode ratCode 12).pair (sumPairs pairSquare pairSquareProgram))))
  exact QuantumRoutingCode.scaleProgram.comp (a.pair (d.pair n))

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListPoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal numbering of the new active ports. A prefix sum of pair counts
gives each center its contiguous block of fresh mediator indices. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open ExactQuantumFactoring.BitStackProgram

noncomputable def pairStartProgram : Procedure (prodCode Nat.bits groupsCode) unaryCode
    (fun x => pairStart x.2 x.1) := pairCountProgram.comp takeGroupsProgram

noncomputable def nextGroupProgram : Procedure (prodCode unaryCode groupCode) (listCode portCode)
    (fun x => nextGroup x.2.1 x.2.2.1 x.2.2.2 x.1) := by
  let i := Procedure.first unaryCode groupCode
  let env := Procedure.second unaryCode groupCode
  let n := (Procedure.first Nat.bits (prodCode ratCode groupsCode)).comp env
  let tail := (Procedure.second Nat.bits (prodCode ratCode groupsCode)).comp env
  let r := (Procedure.first ratCode groupsCode).comp tail
  let gs := (Procedure.second ratCode groupsCode).comp tail
  let ps := groupAtProgram.comp (i.pair gs)
  let count := halfProgram.comp
    ((ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength portCode (0,0)).comp ps)
  let start := Procedure.unaryToBits.comp
    (pairStartProgram.comp ((Procedure.unaryToBits.comp i).pair gs))
  let points := (Procedure.tabulate (0,0) freshPointProgram).comp
    (count.pair ((n.pair start).pair r))
  exact (Procedure.listAppend portCode (0,0)).comp (points.pair (unpairedProgram.comp ps))

noncomputable def nextGroupsProgram : Procedure groupCode groupsCode
    (fun x => (List.range x.2.2.length).map (nextGroup x.1 x.2.1 x.2.2)) := by
  let gs := (Procedure.second ratCode groupsCode).comp
    (Procedure.second Nat.bits (prodCode ratCode groupsCode))
  let count := (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength (listCode portCode) []).comp gs
  exact (Procedure.tabulate (f := fun x i => nextGroup x.1 x.2.1 x.2.2 i)
    [] nextGroupProgram).comp (count.pair (Procedure.identity groupCode))

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListNext
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.edges_length _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.lower_value _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.upper_value _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A complete literal rational fork round, including all four background
bonds, the scalar offset and the remaining active ports. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open ExactQuantumFactoring.BitStackProgram

noncomputable def bondProgram (k : Fin 4) :
    Procedure bondInputCode MediatorListProgram.bondCode (fun x => bond x k) := by
  let n := Procedure.first Nat.bits (prodCode Nat.bits (prodCode ratCode pairCode))
  let tail := Procedure.second Nat.bits (prodCode Nat.bits (prodCode ratCode pairCode))
  let i := (Procedure.first Nat.bits (prodCode ratCode pairCode)).comp tail
  let rest := (Procedure.second Nat.bits (prodCode ratCode pairCode)).comp tail
  let r := (Procedure.first ratCode pairCode).comp rest
  let p := (Procedure.second ratCode pairCode).comp rest
  let a := (Procedure.first Nat.bits ratCode).comp ((Procedure.first portCode portCode).comp p)
  let b := (Procedure.first Nat.bits ratCode).comp ((Procedure.second portCode portCode).comp p)
  let j := leftWeight.comp p
  let q := rightWeight.comp p
  let two := Procedure.constant bondInputCode ratCode 2
  let twiceI := Procedure.binaryMul.comp ((Procedure.constant bondInputCode Nat.bits 2).pair i)
  let first := Procedure.binaryAdd.comp (n.pair twiceI)
  let second := Procedure.successor.comp first
  refine Fin.cases ?_ (fun k => ?_) k
  · exact a.pair (b.pair (Procedure.ratMul.comp ((Procedure.ratMul.comp (two.pair j)).pair q)))
  · refine Fin.cases ?_ (fun k => ?_) k
    · exact first.pair (second.pair (QuantumRoutingCode.squareProgram r))
    · refine Fin.cases ?_ (fun k => ?_) k
      · exact a.pair (second.pair (Procedure.ratMul.comp ((Procedure.ratMul.comp (two.pair r)).pair j)))
      · refine Fin.cases ?_ (fun k => Fin.elim0 k) k
        exact b.pair (second.pair (Procedure.ratMul.comp ((Procedure.ratMul.comp (two.pair r)).pair q)))

noncomputable def pairBondsProgram : Procedure bondInputCode (listCode MediatorListProgram.bondCode)
    (fun x => pairBonds x.1 x.2.1 x.2.2.1 x.2.2.2) :=
  (QuantumRawExchange.fixedListProgram bondInputCode MediatorListProgram.bondCode 4
    (fun k x => bond x k) bondProgram).congrFun (by
      intro x
      simp [bond,pairBonds,List.ofFn_succ])

noncomputable def addedBondInputProgram :
    Procedure (prodCode unaryCode scaleCode) bondInputCode
      (fun x => (x.2.2.1,x.1,x.2.1,
        (((catalog x.2.2.2.2.2).drop x.1).headD (0,((0,0),(0,0)))).2)) := by
  let i := Procedure.unaryToBits.comp (Procedure.first unaryCode scaleCode)
  let env := Procedure.second unaryCode scaleCode
  let r := (Procedure.first ratCode stateCode).comp env
  let s := (Procedure.second ratCode stateCode).comp env
  let n := Procedure.unaryToBits.comp (countProgram.comp s)
  let ps := catalogProgram.comp (groupsProgram.comp s)
  let selected := (Procedure.second Nat.bits pairCode).comp
    ((Procedure.listGet taggedCode (0,((0,0),(0,0)))).comp (i.pair ps))
  exact n.pair (i.pair (r.pair selected))

noncomputable def addedBondsProgram : Procedure scaleCode (listCode MediatorListProgram.bondCode)
    (fun x => addedBonds x.2 x.1) := by
  let s := Procedure.second ratCode stateCode
  let count := pairCountProgram.comp (groupsProgram.comp s)
  let block := pairBondsProgram.comp addedBondInputProgram
  let tab := Procedure.tabulate (f := fun (x : ScaleInput) i => pairBonds x.2.1 i x.1
    (((catalog x.2.2.2.2).drop i).headD (0,((0,0),(0,0)))).2) [] block
  exact ((QuantumRawExchange.flattenProgram MediatorListProgram.bondCode (0,0,0)).comp
    (tab.comp (count.pair (Procedure.identity scaleCode)))).congrFun (by
      intro x
      simp only [Function.comp_apply,addedBonds,catalog_length]
      rfl)

noncomputable def nextProgram : Procedure scaleCode stateCode (fun x => next x.1 x.2) := by
  let s := Procedure.second ratCode stateCode
  let n := countProgram.comp s
  let gs := groupsProgram.comp s
  let count := pairCountProgram.comp gs
  let r := scaleProgram
  let nextCount := Procedure.unaryAdd.comp (n.pair (Procedure.unaryAdd.comp (count.pair count)))
  let nextBonds := (Procedure.listAppend MediatorListProgram.bondCode (0,0,0)).comp
    ((bondsProgram.comp s).pair (addedBondsProgram.comp (r.pair s)))
  let pairs := (Procedure.listMap (0,((0,0),(0,0))) ((0,0),(0,0))
    (Procedure.second Nat.bits pairCode)).comp (catalogProgram.comp gs)
  let offsets := RationalSumProgram.sumProgram.comp
    ((Procedure.listMap ((0,0),(0,0)) 0 pairOffsetProgram).comp pairs)
  let countRat := Procedure.natToRat.comp (Procedure.unaryToBits.comp count)
  let singlets := Procedure.ratMul.comp
    ((Procedure.ratMul.comp ((Procedure.constant scaleCode ratCode 3).pair countRat)).pair
      (QuantumRoutingCode.squareProgram r))
  let nextScalar := Procedure.ratAdd.comp
    ((Procedure.ratAdd.comp ((scalarProgram.comp s).pair offsets)).pair singlets)
  let nextGroups := nextGroupsProgram.comp ((Procedure.unaryToBits.comp n).pair (r.pair gs))
  exact (nextCount.pair (nextBonds.pair (nextScalar.pair nextGroups))).congrFun (by
    intro x
    dsimp only [Function.comp_apply,next]
    rw [two_mul]
    rfl)

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListInitialProgram
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.edges_length _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.lower_value _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.upper_value _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal lookup, parity and rational coefficient programs for the
initial odd subdivision. Endpoint queries read the actual input bond list. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open ExactQuantumFactoring.BitStackProgram MediatorListProgram

noncomputable def initialIndicesProgram : Procedure initialLookupCode (listCode Nat.bits)
    (fun x => initialIndices x.2 x.1) := by
  let bs := Procedure.second Nat.bits (listCode bondCode)
  let len := (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength bondCode (0,0,0)).comp bs
  let count := Procedure.unaryAdd.comp (len.pair len)
  let tab := (Procedure.tabulate (f := fun env j => initialMatch (j,env)) []
    initialMatchProgram).comp (count.pair (Procedure.identity initialLookupCode))
  refine ((QuantumRawExchange.flattenProgram Nat.bits 0).comp tab).congrFun ?_
  intro x
  change ((List.range (x.2.length+x.2.length)).map (fun j => initialMatch (j,x))).flatten=
    initialIndices x.2 x.1
  rw [show x.2.length+x.2.length=2*x.2.length by omega]
  unfold initialIndices
  generalize List.range (2*x.2.length)=js
  induction js with
  | nil => rfl
  | cons j js ih =>
    simp only [initialMatch] at ih
    by_cases h : initialEndpoint x.2 j=x.1 <;> simp [initialMatch,h,ih]

noncomputable def initialGroupProgram : Procedure initialGroupInputCode (listCode portCode)
    (fun x => initialGroup x.1 x.2.2.2 x.2.1 x.2.2.1) := by
  let n := Procedure.first Nat.bits (prodCode ratCode initialLookupCode)
  let tail := Procedure.second Nat.bits (prodCode ratCode initialLookupCode)
  let r := (Procedure.first ratCode initialLookupCode).comp tail
  let lookup := (Procedure.second ratCode initialLookupCode).comp tail
  let bs := (Procedure.second Nat.bits (listCode bondCode)).comp lookup
  let env := n.pair (r.pair bs)
  let js := initialIndicesProgram.comp lookup
  exact ((Procedure.listMapWith
    (f := fun (y : ℕ × (ℚ × List Bond)) (j : ℕ) =>
      (y.1+j,initialWeight y.2.2 y.2.1 j)) 0 (0,0) initialPointProgram).comp
      (env.pair js)).congrFun (by intro x; rfl)

noncomputable def initialGroupAtProgram :
    Procedure (prodCode unaryCode initialGroupsCode) (listCode portCode)
      (fun x => initialGroup x.2.1 x.2.2.2 x.2.2.1 x.1) := by
  let i := Procedure.unaryToBits.comp (Procedure.first unaryCode initialGroupsCode)
  let env := Procedure.second unaryCode initialGroupsCode
  let n := Procedure.unaryToBits.comp
    ((Procedure.first unaryCode (prodCode ratCode (listCode bondCode))).comp env)
  let tail := (Procedure.second unaryCode (prodCode ratCode (listCode bondCode))).comp env
  let r := (Procedure.first ratCode (listCode bondCode)).comp tail
  let bs := (Procedure.second ratCode (listCode bondCode)).comp tail
  exact initialGroupProgram.comp (n.pair (r.pair (i.pair bs)))

noncomputable def initialGroupsProgram : Procedure initialGroupsCode groupsCode
    (fun x => (List.range x.1).map (initialGroup x.1 x.2.2 x.2.1)) := by
  let n := Procedure.first unaryCode (prodCode ratCode (listCode bondCode))
  exact (Procedure.tabulate
    (f := fun (x : ℕ × (ℚ × List Bond)) i => initialGroup x.1 x.2.2 x.2.1 i)
    [] initialGroupAtProgram).comp (n.pair (Procedure.identity initialGroupsCode))

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListInitialStateProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal polynomial program emits the complete initial odd-subdivision
state, with its rational scale, singlet bonds and scalar offset. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open ExactQuantumFactoring.BitStackProgram MediatorListProgram

noncomputable def initialScaleProgram : Procedure initialInputCode ratCode
    (fun x => initialScale x.1 x.2.2.1 x.2.2.2) := by
  let n := Procedure.first ratCode (prodCode unaryCode (prodCode (listCode bondCode) ratCode))
  let ws := (Procedure.listMap (0,0,0) 0 initialBondWeight).comp initialInputBonds
  let input := (n.pair initialInputConstant).pair
    ((Procedure.constant initialInputCode (listCode ratCode) []).pair ws)
  exact (QuantumPathScaleProgram.program.comp input).congrFun (by
    intro x
    simp only [Function.comp_apply,QuantumPathScaleProgram.value,QuantumPathScaleProgram.active,
      QuantumPathScaleProgram.correction,QuantumPathScaleProgram.base,List.map_nil,List.sum_nil,
      mul_zero,zero_add,List.map_map,Function.comp_def,QuantumPathScaleProgram.linearCost,
      QuantumPathScaleProgram.squareCost,initialScale])

noncomputable def initialOffsetProgram : Procedure bondCode ratCode
    (fun b => 3/4+3*b.2.2^2) :=
  Procedure.ratAdd.comp ((Procedure.constant bondCode ratCode (3/4)).pair
    (Procedure.ratMul.comp ((Procedure.constant bondCode ratCode 3).pair
      (QuantumRoutingCode.squareProgram initialBondWeight))))

noncomputable def initialSingletProgram :
    Procedure (prodCode unaryCode portCode) bondCode
      (fun x => (x.2.1+2*x.1,x.2.1+2*x.1+1,x.2.2^2)) := by
  let i := Procedure.unaryToBits.comp (Procedure.first unaryCode portCode)
  let env := Procedure.second unaryCode portCode
  let n := (Procedure.first Nat.bits ratCode).comp env
  let r := (Procedure.second Nat.bits ratCode).comp env
  let a := Procedure.binaryAdd.comp (n.pair (Procedure.binaryMul.comp
    ((Procedure.constant (prodCode unaryCode portCode) Nat.bits 2).pair i)))
  exact a.pair ((Procedure.successor.comp a).pair (QuantumRoutingCode.squareProgram r))

noncomputable def initialStateProgram : Procedure initialInputCode stateCode
    (fun x => initial x.2.1 x.2.2.1 x.2.2.2 x.1) := by
  let n := initialInputCount
  let bs := initialInputBonds
  let c := initialInputConstant
  let r := initialScaleProgram
  let count := (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength bondCode (0,0,0)).comp bs
  let size := Procedure.unaryAdd.comp (n.pair (Procedure.unaryAdd.comp (count.pair count)))
  let singlets := (Procedure.tabulate
    (f := fun (p : Port) i => (p.1+2*i,p.1+2*i+1,p.2^2)) (0,0,0)
      initialSingletProgram).comp (count.pair ((Procedure.unaryToBits.comp n).pair r))
  let offset := RationalSumProgram.sumProgram.comp
    ((Procedure.listMap (0,0,0) 0 initialOffsetProgram).comp bs)
  let countRat := Procedure.natToRat.comp (Procedure.unaryToBits.comp count)
  let penalty := Procedure.ratMul.comp
    ((Procedure.ratMul.comp ((Procedure.constant initialInputCode ratCode 3).pair countRat)).pair
      (QuantumRoutingCode.squareProgram r))
  let scalar := Procedure.ratAdd.comp ((Procedure.ratAdd.comp (c.pair offset)).pair penalty)
  let groups := initialGroupsProgram.comp (n.pair (r.pair bs))
  exact (size.pair (singlets.pair (scalar.pair groups))).congrFun (by
    intro x
    dsimp only [Function.comp_apply,initial]
    rw [two_mul]
    rfl)

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRoutingInputProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compile cell arrays and an edge array into the registers needed by the
buffered-route evaluator. Binary endpoint labels are clipped by the explicit
qubit array length before their conversion to unary loop bounds. -/

noncomputable section
namespace ContinuumCoulomb.QuantumRoutingInputProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

noncomputable def pathProgram (A B : ℕ) : Procedure inputCode (listCode pairCode)
    (fun x => QuantumBufferedListProgram.path A B (value A B x)) :=
  (QuantumBufferedListProgram.pathProgram A B).comp (program A B)

end ContinuumCoulomb.QuantumRoutingInputProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedCellProgram
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumPortChainProgram.value_length _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cell arrays follow the same term-major order as the literal local-word
compiler. Each new mediator inherits its term's cell; each output word retains
that cell as its anchor. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedCellProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

noncomputable def repeatProgram (d : ℕ) :
    Procedure pairCode (listCode pairCode) (fun p : Pair => List.replicate d p) :=
  (QuantumRawExchange.fixedListProgram pairCode pairCode d (fun _ p => p)
    (fun _ => Procedure.identity pairCode)).congrFun (by intro p; simp)

noncomputable def anchorsProgram (d : ℕ) :
    Procedure (listCode pairCode) (listCode pairCode) (anchors d) :=
  (QuantumRawExchange.flattenProgram pairCode (0,0)).comp
    (Procedure.listMap (0,0) [] (repeatProgram d))

noncomputable def program (d : ℕ) : Procedure stateCode stateCode (value d) :=
  (Procedure.listAppend pairCode (0,0)).pair
    ((anchorsProgram d).comp (Procedure.second (listCode pairCode) (listCode pairCode)))

end ContinuumCoulomb.QuantumOrderedCellProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedLabelPipeline
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed six-stage literal sparse-word compiler. The final stage assigns
a private mediator to every two-local term before the four-spin encoding. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedLabelPipeline
open ExactQuantumFactoring.BitStackProgram
open QuantumOrderedLabelData QuantumOrderedLabelFamily

noncomputable opaque subdivisionStepProgram (d : ℕ) : Procedure inputCode inputCode
    (subdivisionStep d) :=
  precisionProgram.pair (valueProgram 4 _ fourWeight
    (blockProgram 4 _ fourWeight (subdivisionProgram d) QuantumOrderedWeightProgram.fourProgram))
noncomputable opaque thirdStepProgram : Procedure inputCode inputCode thirdStep :=
  precisionProgram.pair (valueProgram 7 thirdBlock sevenWeight
    (blockProgram 7 thirdBlock sevenWeight thirdBlockProgram QuantumOrderedWeightProgram.sevenProgram))
noncomputable opaque yyStepProgram : Procedure inputCode inputCode yyStep :=
  precisionProgram.pair (valueProgram 4 yyBlock fourWeight
    (blockProgram 4 yyBlock fourWeight yyBlockProgram QuantumOrderedWeightProgram.fourProgram))
noncomputable opaque privateStepProgram : Procedure inputCode inputCode privateStep :=
  precisionProgram.pair (valueProgram 4 privateBlock fourWeight
    (blockProgram 4 privateBlock fourWeight privateBlockProgram QuantumOrderedWeightProgram.fourProgram))
noncomputable opaque outputProgram : Procedure inputCode stateCode output :=
  (Procedure.second unaryCode stateCode).comp (privateStepProgram.comp
    (thirdStepProgram.comp (yyStepProgram.comp (thirdStepProgram.comp
      ((subdivisionStepProgram 2).comp (subdivisionStepProgram 3))))))

end ContinuumCoulomb.QuantumOrderedLabelPipeline

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedCellTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The computed spatial arrays use exactly the same sum/product enumeration
as the actual ordered Hamiltonian compiler. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedCellTable
open QuantumOrderedCellProgram QuantumOrderedLabelTable QuantumOrderedSpatialComplete
open ExactQuantumFactoring.BitStackProgram
open QuantumRouteCode
variable {ι κ : Type} {n m : ℕ}

noncomputable def completeProgram : Procedure stateCode stateCode complete :=
  (program 4).comp ((program 7).comp ((program 4).comp ((program 7).comp
    ((program 4).comp (program 4)))))

end ContinuumCoulomb.QuantumOrderedCellTable

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedRawCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The raw four-spin compiler repeats each computed logical cell four times,
in exactly the order of its physical spin indices. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedRawCells
open QuantumOrderedCellProgram QuantumOrderedCellTable QuantumOrderedSpatialComplete
open QuantumOrderedLabelTable QuantumRouteCode
open ExactQuantumFactoring.BitStackProgram

noncomputable def program : Procedure stateCode (listCode pairCode) value :=
  (anchorsProgram 4).comp ((Procedure.first (listCode pairCode) (listCode pairCode)).comp completeProgram)

end ContinuumCoulomb.QuantumOrderedRawCells

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkGridProgram
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.edges_length _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.lower_value _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.upper_value _root_.OAI.ContinuumCoulomb.QuantumPortChainProgram.value_length _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual row/column arrays for the fork compiler. The scale remains an
input register; only the number of fork rounds is fixed. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkGridProgram
open QuantumForkList ExactQuantumFactoring.BitStackProgram QuantumRouteCode

noncomputable def nextCellProgram : Procedure queryCode QuantumRouteCode.pairCode
    (fun x => nextCell x.2.1 (lookup x.2.2) x.1) := by
  let v := Procedure.first Nat.bits cellsCode
  let env := Procedure.second Nat.bits cellsCode
  let s := (Procedure.first QuantumForkList.stateCode (listCode QuantumRouteCode.pairCode)).comp env
  let xs := (Procedure.second QuantumForkList.stateCode (listCode QuantumRouteCode.pairCode)).comp env
  let n := Procedure.unaryToBits.comp (countProgram.comp s)
  let before := Procedure.binaryLt.comp (v.pair n)
  let pair := Procedure.binaryDiv.comp
    ((Procedure.binarySub.comp (v.pair n)).pair (Procedure.constant queryCode Nat.bits 2))
  let ps := catalogProgram.comp (groupsProgram.comp s)
  let center := (Procedure.first Nat.bits QuantumForkList.pairCode).comp
    ((Procedure.listGet taggedCode (0,((0,0),(0,0)))).comp (pair.pair ps))
  let target := Procedure.conditional before v center
  exact ((Procedure.listGet QuantumRouteCode.pairCode (0,0)).comp (target.pair xs)).congrFun (by
    intro x
    change lookup x.2.2 (if decide (x.1<x.2.1.1) then x.1 else
      (((catalog x.2.1.2.2.2).drop ((x.1-x.2.1.1)/2)).headD (0,((0,0),(0,0)))).1) = _
    unfold nextCell
    by_cases h : x.1<x.2.1.1 <;> simp [h])

noncomputable def nextCellsProgram : Procedure cellsCode (listCode QuantumRouteCode.pairCode) nextCells := by
  let s := Procedure.first QuantumForkList.stateCode (listCode QuantumRouteCode.pairCode)
  let n := countProgram.comp s
  let pairs := pairCountProgram.comp (groupsProgram.comp s)
  let count := Procedure.unaryAdd.comp (n.pair (Procedure.unaryAdd.comp (pairs.pair pairs)))
  let query : Procedure (prodCode unaryCode cellsCode) queryCode (fun x => (x.1,x.2)) :=
    (Procedure.unaryToBits.comp (Procedure.first unaryCode cellsCode)).pair
      (Procedure.second unaryCode cellsCode)
  let entry := nextCellProgram.comp query
  exact ((Procedure.tabulate (f := fun x i => nextCell x.1 (lookup x.2) i) (0,0) entry).comp
    (count.pair (Procedure.identity cellsCode))).congrFun (by
      intro x
      change (List.range (x.1.1+(pairCount x.1.2.2.2+pairCount x.1.2.2.2))).map _=nextCells x
      simp only [nextCells,two_mul,id_eq])

noncomputable def stepProgram : Procedure inputCode cellsCode step := by
  let scale := Procedure.first ratCode cellsCode
  let env := Procedure.second ratCode cellsCode
  let s := (Procedure.first QuantumForkList.stateCode (listCode QuantumRouteCode.pairCode)).comp env
  exact (nextProgram.comp (scale.pair s)).pair (nextCellsProgram.comp env)

noncomputable def runProgram : (k : ℕ) → Procedure inputCode cellsCode (run k)
  | 0 => Procedure.second ratCode cellsCode
  | k+1 => stepProgram.comp ((Procedure.first ratCode cellsCode).pair (runProgram k))

end ContinuumCoulomb.QuantumForkGridProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListScheduleProgram
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed-round routing compiler on literal bond/work lists. Each active
edge receives one singlet pair; its unfinished tail retains one less work unit. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListSchedule
open ExactQuantumFactoring.BitStackProgram MediatorListProgram

noncomputable opaque partitionProgram (active : Bool) :
    Procedure (listCode entryCode) (listCode entryCode) (partition active) := by
  let single : Procedure entryCode (listCode entryCode) (fun e => [e]) :=
    (Procedure.listCons entryCode).comp ((Procedure.identity entryCode).pair
      (Procedure.constant entryCode (listCode entryCode) []))
  let chunk := Procedure.conditional (selectedProgram active) single
    (Procedure.constant entryCode (listCode entryCode) [])
  refine ((QuantumRawExchange.flattenProgram entryCode zeroEntry).comp
    (Procedure.listMap zeroEntry [] chunk)).congrFun ?_
  intro xs
  induction xs with
  | nil => rfl
  | cons e xs ih =>
    dsimp only [Function.comp_apply] at ih
    cases h : selected active e <;> simpa [partition,h] using ih

noncomputable opaque selectedEntriesProgram (b : Bool) :
    Procedure inputCode (listCode entryCode) (fun x => partition b x.2.2.2) :=
  (partitionProgram b).comp entriesProgram
noncomputable opaque stepInputProgram :
    Procedure inputCode QuantumListPathStep.inputCode stepInput :=
  (countInputProgram.pair ((Procedure.constant inputCode Procedure.boolCode false).pair
    (precisionProgram.pair scalarInputProgram))).pair
      ((eraseProgram.comp (selectedEntriesProgram false)).pair
        (eraseProgram.comp (selectedEntriesProgram true)))

noncomputable opaque blockProgram : Procedure blockInputCode (listCode entryCode) block :=
  QuantumRawExchange.fixedListProgram blockInputCode entryCode 3
    (fun k x => (blockWork x k,QuantumListPathProgram.bond (blockBondInput x) k))
    (fun k => (blockWorkProgram k).pair ((QuantumListPathProgram.bondProgram k).comp blockBondInputProgram))

noncomputable opaque indexedProgram :
    Procedure (prodCode unaryCode inputCode) blockInputCode indexed := by
  let i := Procedure.first unaryCode inputCode
  let x := Procedure.second unaryCode inputCode
  let p := (QuantumListPathStep.parametersProgram.comp stepInputProgram).comp x
  let xs := (selectedEntriesProgram true).comp x
  let e := (Procedure.listGet entryCode zeroEntry).comp ((Procedure.unaryToBits.comp i).pair xs)
  exact p.pair (i.pair e)

noncomputable opaque familyLengthProgram : Procedure inputCode unaryCode
    (fun x => (partition true x.2.2.2).length) :=
  (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength entryCode zeroEntry).comp
    (selectedEntriesProgram true)

noncomputable opaque familyTabProgram :
    Procedure (prodCode unaryCode inputCode) (listCode (listCode entryCode))
      (fun x => (List.range x.1).map (fun i => block (indexed (i,x.2)))) :=
  Procedure.tabulate (f := fun x i => block (indexed (i,x))) [] (blockProgram.comp indexedProgram)

noncomputable opaque familyInputProgram : Procedure inputCode (prodCode unaryCode inputCode)
    (fun x => ((partition true x.2.2.2).length,x)) :=
  familyLengthProgram.pair (Procedure.identity inputCode)

noncomputable opaque familyNestedProgram : Procedure inputCode (listCode (listCode entryCode))
    (fun x => (List.range (partition true x.2.2.2).length).map (fun i => block (indexed (i,x)))) :=
  (familyTabProgram.comp familyInputProgram).congrFun (by intro x; rfl)

noncomputable opaque familyProgram : Procedure inputCode (listCode entryCode) family :=
  (QuantumRawExchange.flattenProgram entryCode zeroEntry).comp familyNestedProgram

noncomputable opaque program : Procedure inputCode stateCode value :=
  (QuantumListPathStep.countProgram.comp stepInputProgram).pair
    ((QuantumListPathStep.constantProgram.comp stepInputProgram).pair
      ((Procedure.listAppend entryCode zeroEntry).comp
        ((selectedEntriesProgram false).pair familyProgram)))

end ContinuumCoulomb.QuantumListSchedule

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListRouteProgram
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumPortChainProgram.value_length _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal route lists accompanying the bond/work scheduler. Every new pair
is placed at the first two internal points of its selected route. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListRouteProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode QuantumListSchedule

noncomputable opaque filterProgram (b : Bool) :
    Procedure (listCode routedCode) (listCode routedCode)
      (fun xs => xs.filter (fun r => selected b r.1)) := by
  let single := (Procedure.listCons routedCode).comp ((Procedure.identity routedCode).pair
    (Procedure.constant routedCode (listCode routedCode) []))
  let bit := (QuantumListSchedule.selectedProgram b).comp
    (Procedure.first entryCode (listCode pairCode))
  let chunk := Procedure.conditional bit single
    (Procedure.constant routedCode (listCode routedCode) [])
  refine ((QuantumRawExchange.flattenProgram routedCode (zeroEntry,[])).comp
    (Procedure.listMap (zeroEntry,[]) [] chunk)).congrFun ?_
  intro xs
  induction xs with
  | nil => rfl
  | cons r rs ih =>
    dsimp only [Function.comp_apply] at ih
    cases h : selected b r.1 <;> simpa [h] using ih
noncomputable opaque selectedProgram (b : Bool) :
    Procedure inputCode (listCode routedCode) (selectedRoutes b) :=
  (filterProgram b).comp decoratedProgram
noncomputable opaque positionsProgram : Procedure inputCode (listCode pairCode) positions :=
  (Procedure.listAppend pairCode (0,0)).comp (oldPositionsProgram.pair
    ((QuantumRawExchange.flattenProgram pairCode (0,0)).comp
      ((Procedure.listMap (zeroEntry,[]) [] freshProgram).comp (selectedProgram true))))
noncomputable opaque pathsProgram : Procedure inputCode (listCode (listCode pairCode)) paths :=
  (Procedure.listAppend (listCode pairCode) []).comp
    (((Procedure.listMap (zeroEntry,[]) [] (Procedure.second entryCode (listCode pairCode))).comp
      (selectedProgram false)).pair
      ((QuantumRawExchange.flattenProgram (listCode pairCode) []).comp
        ((Procedure.listMap (zeroEntry,[]) [] pathBlockProgram).comp (selectedProgram true))))
noncomputable opaque program : Procedure inputCode stateCode value :=
  (QuantumListSchedule.program.comp (precisionProgram.pair scheduleProgram)).pair
    (positionsProgram.pair pathsProgram)

noncomputable opaque iterateProgram (k : ℕ) :
    Procedure inputCode stateCode (fun x => iterate x.1 k x.2) := by
  induction k with
  | zero => exact dataProgram
  | succ k ih => exact program.comp (precisionProgram.pair ih)

end ContinuumCoulomb.QuantumListRouteProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumInflatedListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The eightfold scaled route is an explicit list computation. Its loop
bound is eight times the input route length. -/

noncomputable section
namespace ContinuumCoulomb.QuantumInflatedListProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

noncomputable opaque pointProgram : Procedure inputCode pairCode point := by
  let k := Procedure.first Nat.bits (listCode pairCode)
  let xs := Procedure.second Nat.bits (listCode pairCode)
  let eight := Procedure.constant inputCode Nat.bits 8
  let index := Procedure.binaryDiv.comp (k.pair eight)
  let indexNext := Procedure.successor.comp index
  let get := Procedure.listGet pairCode (0,0)
  let p := QuantumRouteLeafCode.centerProgram.comp (get.comp (index.pair xs))
  let q := QuantumRouteLeafCode.centerProgram.comp (get.comp (indexNext.pair xs))
  let rest := Procedure.binaryMod.comp (k.pair eight)
  exact QuantumRouteCode.pointProgram.comp ((p.pair q).pair rest)

noncomputable opaque indexedProgram : Procedure (prodCode unaryCode (listCode pairCode))
    pairCode (fun x => point (x.1,x.2)) :=
  pointProgram.comp
    ((Procedure.unaryToBits.comp (Procedure.first unaryCode (listCode pairCode))).pair
      (Procedure.second unaryCode (listCode pairCode)))

noncomputable opaque tabProgram : Procedure (prodCode unaryCode (listCode pairCode))
    (listCode pairCode) (fun x => (List.range x.1).map (fun k => point (k,x.2))) :=
  Procedure.tabulate (f := fun xs k => point (k,xs)) (0,0) indexedProgram

noncomputable opaque program : Procedure (listCode pairCode) (listCode pairCode) value :=
  (tabProgram.comp (lengthProgram.pair (Procedure.identity (listCode pairCode)))).congrFun
    (by intro xs; rfl)

end ContinuumCoulomb.QuantumInflatedListProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumEvenListPieces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal reserved-leaf and tail arrays for an even route subdivision. -/

noncomputable section
namespace ContinuumCoulomb.QuantumEvenListPieces
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

noncomputable def pointProgram (k : ℕ) : Procedure (listCode pairCode) pairCode
    (fun xs => QuantumInflatedListProgram.point (k,xs)) :=
  QuantumInflatedListProgram.pointProgram.comp
    ((Procedure.constant (listCode pairCode) Nat.bits k).pair
      (Procedure.identity (listCode pairCode)))

noncomputable opaque freshProgram : Procedure (listCode pairCode) (listCode pairCode) fresh :=
  pairList (listCode pairCode) (pointProgram 1) leafProgram

noncomputable opaque pathsProgram : Procedure (listCode pairCode)
    (listCode (listCode pairCode)) paths := by
  let second := pairList (listCode pairCode) (pointProgram 0) (pointProgram 1)
  let third := (Procedure.listReverse pairCode (0,0)).comp
    ((Procedure.listDrop pairCode).comp
      ((Procedure.constant (listCode pairCode) Nat.bits 1).pair
        QuantumInflatedListProgram.program))
  exact (Procedure.listCons (listCode pairCode)).comp (freshProgram.pair
    ((Procedure.listCons (listCode pairCode)).comp (second.pair
      ((Procedure.listCons (listCode pairCode)).comp
        (third.pair (Procedure.constant (listCode pairCode) (listCode (listCode pairCode)) []))))))

end ContinuumCoulomb.QuantumEvenListPieces

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListMergeProgram
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumPortChainProgram.value_length _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal polynomial pair-table enumeration and rational accumulation for
canonical bond merging. The vertex count is represented in unary. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListMerge
open ExactQuantumFactoring.BitStackProgram MediatorListProgram QuantumRouteCode

noncomputable def pairsProgram : Procedure unaryCode (listCode pairCode) pairs := by
  let step := rowProgram.comp ((Procedure.second unaryCode unaryCode).pair
    (Procedure.unaryToBits.comp (Procedure.first unaryCode unaryCode)))
  let table := (Procedure.tabulate (f := fun n i => (List.range n).map (fun j => (i,j))) [] step).comp
    ((Procedure.identity unaryCode).pair (Procedure.identity unaryCode))
  exact ((QuantumRawExchange.flattenProgram pairCode (0,0)).comp table).congrFun (by
    intro n
    simp only [Function.comp_apply,pairs,List.product,List.flatMap_def,id_eq])

noncomputable def filterProgram :
    Procedure (prodCode (listCode pairCode) (listCode pairCode)) (listCode pairCode)
      (fun x => x.2.filter (fun p => decide (p ∈ x.1))) := by
  let key := Procedure.second (listCode pairCode) pairCode
  let keys := Procedure.first (listCode pairCode) pairCode
  let member := QuantumFiniteMembership.pairMemberProgram.comp (key.pair keys)
  let one := (Procedure.listCons pairCode).comp
    (key.pair (Procedure.constant _ (listCode pairCode) []))
  let chunk : Procedure (prodCode (listCode pairCode) pairCode) (listCode pairCode)
      (fun x => if x.2 ∈ x.1 then [x.2] else []) :=
    (Procedure.conditional member one (Procedure.constant _ (listCode pairCode) [])).congrFun (by
      intro x
      simp only [Function.comp_apply,decide_eq_true_eq])
  let chunks := Procedure.listMapWith (ea := listCode pairCode) (eb := pairCode)
    (ec := listCode pairCode) (f := fun keys p => if p ∈ keys then [p] else []) (0,0) [] chunk
  refine ((QuantumRawExchange.flattenProgram pairCode (0,0)).comp chunks).congrFun ?_
  intro x
  rcases x with ⟨keys,ps⟩
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    by_cases h : p ∈ keys <;> simpa [h] using ih

noncomputable def supportProgram : Procedure inputCode (listCode pairCode)
    (fun x => support x.1 x.2) :=
  filterProgram.comp
    (((Procedure.listMap zeroBond (0,0) orderedProgram).comp (Procedure.second _ _)).pair
      (pairsProgram.comp (Procedure.first _ _)))

noncomputable def valueProgram : Procedure inputCode (listCode bondCode)
    (fun x => value x.1 x.2) := by
  let xs := Procedure.first (listCode bondCode) pairCode
  let p := Procedure.second (listCode bondCode) pairCode
  let a := (Procedure.first Nat.bits Nat.bits).comp p
  let b := (Procedure.second Nat.bits Nat.bits).comp p
  let w := weightProgram.comp (p.pair xs)
  let entry := a.pair (b.pair w)
  exact (Procedure.listMapWith (ea := listCode bondCode) (eb := pairCode) (ec := bondCode)
    (f := fun xs p => (p.1,p.2,weight xs p)) (0,0) zeroBond entry).comp
      ((Procedure.second _ _).pair supportProgram)

end ContinuumCoulomb.QuantumListMerge

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumTaggedRouteProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Evaluate each candidate together with its finite permission bit. Keeping
that bit attached to the path preserves the exact catalog order during the
bounded search, including reversed paths. -/

noncomputable section
namespace ContinuumCoulomb.QuantumTaggedRouteProgram
open scoped Classical
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode
open QuantumRoutingTable

noncomputable opaque rayProgram (a : Fin 4) : Procedure inputCode (listCode taggedCode)
    (fun x => oriented (bodyPermitted x.1 (.ray x.2 a)) ((QMACellRouteBody.ray x.2 a).path)) :=
  bodyProgram (fun p => .ray p a) ((QuantumCellPathProgram.rayProgram a).comp _root_.OAI.ContinuumCoulomb.QuantumRoutingTable.cellProgram)
    ((rayAllowedProgram a).congrFun (by
      intro x
      apply Bool.eq_iff_iff.mpr
      rw [bodyPermitted_eq_true]
      exact ⟨fun h => ⟨h,trivial⟩,And.left⟩))

noncomputable opaque pairProgram (e : Fin 6) : Procedure inputCode (listCode taggedCode)
    (fun x => oriented (bodyPermitted x.1 (.pair x.2 e)) ((QMACellRouteBody.pair x.2 e).path)) :=
  bodyProgram (fun p => .pair p e) ((QuantumCellPathProgram.pairProgram e).comp _root_.OAI.ContinuumCoulomb.QuantumRoutingTable.cellProgram)
    ((pairAllowedProgram e).congrFun (by
      intro x
      apply Bool.eq_iff_iff.mpr
      rw [bodyPermitted_eq_true]
      exact ⟨fun h => ⟨h,trivial⟩,And.left⟩))

noncomputable opaque patchProgram (e : Fin 9) : Procedure inputCode (listCode taggedCode)
    (fun x => oriented (bodyPermitted x.1 (.patch x.2 e)) ((QMACellRouteBody.patch x.2 e).path)) :=
  bodyProgram (fun p => .patch p e) ((QuantumCellPathProgram.patchProgram e).comp _root_.OAI.ContinuumCoulomb.QuantumRoutingTable.cellProgram)
    ((patchAllowedProgram e).congrFun (by
      intro x
      apply Bool.eq_iff_iff.mpr
      rw [bodyPermitted_eq_true]
      exact ⟨fun h => ⟨h,trivial⟩,And.left⟩))

noncomputable opaque corridorProgram (a : Fin 4) (b c : Bool) :
    Procedure inputCode (listCode taggedCode)
      (fun x => oriented (bodyPermitted x.1 (.corridor x.2 a b c))
        ((QMACellRouteBody.corridor x.2 a b c).path)) :=
  bodyProgram (fun p => .corridor p a b c)
    ((QuantumCellPathProgram.corridorProgram a b c).comp _root_.OAI.ContinuumCoulomb.QuantumRoutingTable.cellProgram)
    ((Procedure.boolAnd.comp ((corridorAllowedProgram a b c).pair cellPositiveProgram)).congrFun (by
      intro x
      apply Bool.eq_iff_iff.mpr
      simp only [Function.comp_apply,Bool.and_eq_true,decide_eq_true_eq,bodyPermitted_eq_true]
      rfl))

noncomputable opaque corridorBlock (a : Fin 4) : Procedure inputCode (listCode taggedCode)
    (fun x => oriented (bodyPermitted x.1 (.corridor x.2 a false false))
        ((QMACellRouteBody.corridor x.2 a false false).path) ++
      oriented (bodyPermitted x.1 (.corridor x.2 a false true))
        ((QMACellRouteBody.corridor x.2 a false true).path) ++
      oriented (bodyPermitted x.1 (.corridor x.2 a true false))
        ((QMACellRouteBody.corridor x.2 a true false).path) ++
      oriented (bodyPermitted x.1 (.corridor x.2 a true true))
        ((QMACellRouteBody.corridor x.2 a true true).path)) :=
  append inputCode taggedCode (false,[]) (append inputCode taggedCode (false,[])
    (append inputCode taggedCode (false,[]) (corridorProgram a false false)
      (corridorProgram a false true)) (corridorProgram a true false)) (corridorProgram a true true)

noncomputable opaque cellProgram : Procedure inputCode (listCode taggedCode)
    (fun x => (qmaCellRoutes x.2).map (tagged x.1)) := by
  let rays := fixedFlat inputCode taggedCode (false,[]) 4 _ rayProgram
  let pairs := fixedFlat inputCode taggedCode (false,[]) 6 _ pairProgram
  let patches := fixedFlat inputCode taggedCode (false,[]) 9 _ patchProgram
  let corridors := fixedFlat inputCode taggedCode (false,[]) 4 _ corridorBlock
  exact (append inputCode taggedCode (false,[])
    (append inputCode taggedCode (false,[]) (append inputCode taggedCode (false,[]) rays pairs)
      patches) corridors).congrFun (by
    intro x
    simp only [qmaCellRoutes,qmaCellBodies,List.flatMap_def,List.map_flatten,List.map_append,
      List.map_map,List.ofFn_eq_map,List.map_cons,List.map_nil,List.flatten_cons,List.flatten_nil,
      List.flatten_append,List.flatten_flatten,
      Function.comp_def,tagged,oriented,QMACellRoute.path,Bool.false_eq_true,ite_false, if_false,ite_true, if_true,
      List.append_assoc,List.append_nil])

end ContinuumCoulomb.QuantumTaggedRouteProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRouteSelectorProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal 140-entry selector checks finite permissions and both physical
endpoints. No unbounded search or choice occurs in the resulting program. -/

noncomputable section
namespace ContinuumCoulomb.QuantumRouteSelectorProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode
open QuantumTaggedRouteProgram QuantumFiniteRouteSearch

noncomputable opaque candidatesProgram : Procedure inputCode (listCode taggedCode) candidates := by
  let table := Procedure.first QuantumRoutingTable.tableCode endsCode
  let ends := Procedure.second QuantumRoutingTable.tableCode endsCode
  let leftCell := QuantumCellPathProgram.pointCellProgram.comp
    ((Procedure.first pairCode pairCode).comp ends)
  let rightCell := QuantumCellPathProgram.pointCellProgram.comp
    ((Procedure.second pairCode pairCode).comp ends)
  let left := QuantumTaggedRouteProgram.cellProgram.comp (table.pair leftCell)
  let right := QuantumTaggedRouteProgram.cellProgram.comp (table.pair rightCell)
  exact ((Procedure.listAppend taggedCode (false,[])).comp (left.pair right)).congrFun (by
    intro x
    simp only [Function.comp_apply,candidates,qmaRouteCandidates,List.map_append])

noncomputable opaque program : Procedure inputCode (listCode pairCode) value :=
  chooseProgram.comp ((Procedure.second _ _).pair candidatesProgram)

end ContinuumCoulomb.QuantumRouteSelectorProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkGridInitial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The initial subdivision computes its row/column array from the actual
endpoint list, before the same fixed-round grid program is applied. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkGridProgram
open QuantumForkList MediatorListProgram ExactQuantumFactoring.BitStackProgram

noncomputable def prepareProgram : Procedure preparedCode inputCode prepare := by
  let init := Procedure.first initialInputCode (listCode QuantumRouteCode.pairCode)
  let cells := Procedure.second initialInputCode (listCode QuantumRouteCode.pairCode)
  let n := initialInputCount.comp init
  let bs := initialInputBonds.comp init
  let r := (Procedure.first ratCode
    (prodCode unaryCode (prodCode (listCode bondCode) ratCode))).comp init
  exact r.pair ((initialStateProgram.comp init).pair
    (initialCellsProgram.comp (n.pair (bs.pair cells))))

noncomputable def outputProgram (k : ℕ) : Procedure preparedCode cellsCode (output k) :=
  (runProgram k).comp prepareProgram

end ContinuumCoulomb.QuantumForkGridProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListSpatialPackage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Package the literal full fork graph with deterministic midpoint anchors.
The package keeps its actual spin indices, coefficients and scalar offset. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram
open scoped Classical

def spatialModel {rows width : ℕ} (s : State) (hs : ValidPorts s.1 s.2.2.2)
    (hb : SourceBondLists.bounded s.1 s.2.1) (hn : ∀ b ∈ s.2.1, b.1≠b.2.1)
    (cell : ℕ → QMAGridCell rows width) (A : ℕ)
    (hc : ∀ p, qmaCellMass (fun v : Fin s.1 => cell v.val) p ≤ A)
    (hd : ∀ v : Fin s.1, degree (fullList s) v.val ≤ 3)
    (hl : BondLocal (fullList s) cell CommonCell) : QMASpatialExchangeModel A (27*A) := by
  let G := fullGraph s hs hb hn
  let cells : Fin s.1 → QMAGridCell rows width := fun v => cell v.val
  let anchors := fun e => qmaGridMidpoint (cells (G.left e)) (cells (G.right e))
  have hg : ∀ e, QMAGridCellsNear (cells (G.left e)) (anchors e) ∧
      QMAGridCellsNear (cells (G.right e)) (anchors e) := by
    intro e
    obtain ⟨a,ha,hb⟩ := hl ((fullList s).get e) (List.get_mem _ e)
    exact qmaGridMidpoint_near _ _ a ha hb
  have hc' : ∀ p, (Finset.univ.filter (fun v => cells v=p)).card ≤ A := by
    intro p
    simpa only [qmaCellMass,Finset.card_filter] using hc p
  have hd' : ∀ v : Fin s.1, qmaGraphDegree G.left G.right v ≤ 3 := by
    intro v
    change qmaGraphDegree (SourceBondLists.bonds s.1 (fullList s)
      (fullList_bounded s hs hb)).left (SourceBondLists.bonds s.1 (fullList s)
      (fullList_bounded s hs hb)).right v ≤ 3
    exact (degree_eq_graph s.1 (fullList s) (fullList_bounded s hs hb) v) ▸ hd v
  exact qmaDegreeThreeSpatialModel G.left G.right G.distinct G.weight s.2.2.1
    cells anchors hc' hd' hg

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRoutingInputActual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The encoded cell/edge arrays evaluate to the actual buffered path of the
ordinal-slot spatial model. No arbitrary finite-fiber choice remains in this
part of the routing compiler. -/

noncomputable section
namespace ContinuumCoulomb.QuantumRoutingInputProgram
open QuantumRouteCode

def actualData {A B : ℕ} (M : QMASpatialExchangeModel A B) {m : ℕ}
    (labels : M.Term ≃ Fin m) : Data :=
  ((List.ofFn (QuantumOrdinalPlacement.coordinates M.cell),
    List.ofFn (QuantumOrdinalPlacement.coordinates (M.anchor ∘ labels.symm))),
    List.ofFn (fun i => ((M.left (labels.symm i)).val,(M.right (labels.symm i)).val)))

end ContinuumCoulomb.QuantumRoutingInputProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkRoutingData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal routing-input tape from the full fork state. Active-star bonds
are retained, and each anchor is the integer midpoint of its endpoint cells. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkRoutingData
open ExactQuantumFactoring.BitStackProgram QuantumForkList MediatorListProgram

noncomputable def activeProgram : Procedure groupsCode (listCode bondCode) activeBonds := by
  let count := ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength (listCode portCode) []
  let blocks := (Procedure.tabulate (f := fun gs i => starBonds i (groupAt gs i)) []
    starBondsProgram).comp (count.pair (Procedure.identity groupsCode))
  exact (QuantumRawExchange.flattenProgram bondCode (0,0,0)).comp blocks

noncomputable def fullProgram : Procedure stateCode (listCode bondCode) fullList :=
  (Procedure.listAppend bondCode (0,0,0)).comp
    (bondsProgram.pair (activeProgram.comp groupsProgram))

noncomputable def program : Procedure QuantumForkGridProgram.cellsCode
    QuantumRoutingInputProgram.dataCode value := by
  let state := Procedure.first stateCode (listCode QuantumRouteCode.pairCode)
  let cells := Procedure.second stateCode (listCode QuantumRouteCode.pairCode)
  let bonds := fullProgram.comp state
  let anchorWith := anchorProgram.comp
    ((Procedure.second (listCode QuantumRouteCode.pairCode) bondCode).pair
      (Procedure.first (listCode QuantumRouteCode.pairCode) bondCode))
  let anchors := (Procedure.listMapWith
    (f := fun cells b => anchor (b,cells)) (0,0,0) (0,0) anchorWith).comp (cells.pair bonds)
  let ends := (Procedure.listMap (0,0,0) (0,0) endpointProgram).comp bonds
  exact (cells.pair anchors).pair ends

end ContinuumCoulomb.QuantumForkRoutingData

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPortChainActual
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal port-chain program returns precisely the sites used by the
physical subdivision construction, including its two endpoint centers. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPortChainProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

def routed (A B : ℕ) (x : QuantumRoutingInputProgram.Input) : List Pair :=
  value (QuantumBufferedListProgram.path A B (QuantumRoutingInputProgram.value A B x))

noncomputable opaque routedProgram (A B : ℕ) :
    Procedure QuantumRoutingInputProgram.inputCode (listCode pairCode) (routed A B) :=
  program.comp (QuantumRoutingInputProgram.pathProgram A B)

def allRouted (A B : ℕ) (d : QuantumRoutingInputProgram.Data) : List (List Pair) :=
  (List.range d.2.length).map (fun i => routed A B (i,d))

noncomputable opaque allRoutedProgram (A B : ℕ) :
    Procedure QuantumRoutingInputProgram.dataCode (listCode (listCode pairCode))
      (allRouted A B) := by
  let edges : Procedure QuantumRoutingInputProgram.dataCode (listCode pairCode)
      (fun d => d.2) := Procedure.second
    (prodCode (listCode pairCode) (listCode pairCode)) (listCode pairCode)
  let n : Procedure QuantumRoutingInputProgram.dataCode unaryCode (fun d => d.2.length) :=
    (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength pairCode (0,0)).comp edges
  let tab : Procedure (prodCode unaryCode QuantumRoutingInputProgram.dataCode)
      (listCode (listCode pairCode))
      (fun x => (List.range x.1).map (fun i => routed A B (i,x.2))) :=
    Procedure.tabulate (f := fun d i => routed A B (i,d)) [] (routedProgram A B)
  exact (tab.comp (n.pair (Procedure.identity QuantumRoutingInputProgram.dataCode))).congrFun
    (by intro d; rfl)

@[simp] theorem allRouted_length (A B : ℕ) (d : QuantumRoutingInputProgram.Data) :
    (allRouted A B d).length = d.2.length := by
  simp only [allRouted,List.length_map,List.length_range]

end ContinuumCoulomb.QuantumPortChainProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRoutingFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal enumeration of every coarse route and source center. These are
the exact lists consumed by the finite crossing and permission tables. -/

noncomputable section
namespace ContinuumCoulomb.QuantumRoutingFamily
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode QuantumRoutingInputProgram

def placed (A B : ℕ) (x : Input) : Pair :=
  qmaBufferedCellPoint (9*B+3)
    (QuantumSpatialSlotProgram.fineSite A (x.1,x.2.1.1)) (17,17)

noncomputable opaque placedProgram (A B : ℕ) : Procedure inputCode pairCode (placed A B) := by
  let cells := (Procedure.first (listCode pairCode) (listCode pairCode)).comp
    ((Procedure.first (prodCode (listCode pairCode) (listCode pairCode))
      (listCode pairCode)).comp dataProgram)
  let fine := (QuantumSpatialSlotProgram.fineSiteProgram A).comp (indexProgram.pair cells)
  exact (QuantumEndpointListProgram.translateProgram B).comp
    (fine.pair (Procedure.constant inputCode pairCode (17,17)))

def positions (A B : ℕ) (d : Data) : List Pair :=
  (List.range d.1.1.length).map (fun i => placed A B (i,d))

noncomputable opaque positionsProgram (A B : ℕ) : Procedure dataCode (listCode pairCode)
    (positions A B) := by
  let cells : Procedure dataCode (listCode pairCode) (fun d => d.1.1) :=
    (Procedure.first (listCode pairCode) (listCode pairCode)).comp
    (Procedure.first (prodCode (listCode pairCode) (listCode pairCode)) (listCode pairCode))
  let count : Procedure dataCode unaryCode (fun d => d.1.1.length) :=
    (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength pairCode (0,0)).comp cells
  let tab : Procedure inputCode (listCode pairCode)
      (fun x => (List.range x.1).map (fun i => placed A B (i,x.2))) :=
    Procedure.tabulate (f := fun d i => placed A B (i,d)) (0,0) (placedProgram A B)
  exact (tab.comp (count.pair (Procedure.identity dataCode))).congrFun (by intro d; rfl)

def coarse (A B : ℕ) (d : Data) : List (List Pair) :=
  (List.range d.2.length).map (fun i =>
    QuantumBufferedListProgram.path A B (value A B (i,d)))

noncomputable opaque coarseProgram (A B : ℕ) : Procedure dataCode (listCode (listCode pairCode))
    (coarse A B) := by
  let edges : Procedure dataCode (listCode pairCode) (fun d => d.2) :=
    Procedure.second (prodCode (listCode pairCode) (listCode pairCode)) (listCode pairCode)
  let count : Procedure dataCode unaryCode (fun d => d.2.length) :=
    (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength pairCode (0,0)).comp edges
  let tab : Procedure inputCode (listCode (listCode pairCode))
      (fun x => (List.range x.1).map (fun i =>
        QuantumBufferedListProgram.path A B (value A B (i,x.2)))) :=
    Procedure.tabulate
      (f := fun d i => QuantumBufferedListProgram.path A B (value A B (i,d))) [] (pathProgram A B)
  exact (tab.comp (count.pair (Procedure.identity dataCode))).congrFun (by intro d; rfl)

def table (A B : ℕ) (d : Data) : QuantumPathTable.Input :=
  (positions A B d,coarse A B d)

noncomputable def tableProgram (A B : ℕ) :
    Procedure dataCode QuantumPathTable.inputCode (table A B) :=
  (positionsProgram A B).pair (coarseProgram A B)

end ContinuumCoulomb.QuantumRoutingFamily

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListInitialSpatial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A bounded-density local input list yields the actual degree-three
spatial output, with its full Hamiltonian and fixed density constant. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram
open scoped Classical

namespace SpatialInput
variable {rows width A D : ℕ} (I : SpatialInput rows width A D)

def model : QMASpatialExchangeModel (spatialDensity A D) (27*spatialDensity A D) :=
  (spatialModel I.state I.validPorts I.state_bounded I.state_noLoops I.cells (spatialDensity A D)
    I.state_density I.state_degree I.state_locality).withOrdinalSlots (Equiv.refl _)

theorem model_degree (v : Fin I.model.n) :
    qmaGraphDegree I.model.left I.model.right v ≤ 3 := by
  exact (degree_eq_graph I.state.1 (fullList I.state)
    (fullList_bounded I.state I.validPorts I.state_bounded) v) ▸ I.state_degree v

end SpatialInput
end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSpatialRoutingTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal initial/fork program supplies the same source-center and
coarse-path arrays used by the actual lattice crossing construction. -/

noncomputable section
namespace ContinuumCoulomb.QuantumSpatialRoutingTape
open QuantumForkList ExactQuantumFactoring.BitStackProgram

def value (A D : ℕ) (x : QuantumForkGridProgram.PreparedInput) : QuantumPathTable.Input :=
  QuantumRoutingFamily.table (spatialDensity A D) (27*spatialDensity A D)
    (QuantumForkRoutingData.value (QuantumForkGridProgram.output D x))

end ContinuumCoulomb.QuantumSpatialRoutingTape

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPortScheduleTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The computed port paths decorate the actual full bond list with its
remaining subdivision work. Erasing that work leaves the same Hamiltonian. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPortScheduleTape
open ExactQuantumFactoring.BitStackProgram MediatorListProgram QuantumRouteCode

abbrev Environment := List Bond × List (List Pair)
def environmentCode : Environment → List Bool :=
  prodCode (listCode bondCode) (listCode (listCode pairCode))
def queryCode : (ℕ × Environment) → List Bool := prodCode unaryCode environmentCode

def entry (x : ℕ × Environment) : QuantumListSchedule.Entry :=
  ((((x.2.2.drop x.1).headD []).length-1),(x.2.1.drop x.1).headD zeroBond)

noncomputable opaque entryProgram : Procedure queryCode QuantumListSchedule.entryCode entry := by
  let i := Procedure.unaryToBits.comp (Procedure.first unaryCode environmentCode)
  let env := Procedure.second unaryCode environmentCode
  let bs := (Procedure.first (listCode bondCode) (listCode (listCode pairCode))).comp env
  let ps := (Procedure.second (listCode bondCode) (listCode (listCode pairCode))).comp env
  let p := (Procedure.listGet (listCode pairCode) []).comp (i.pair ps)
  let len := (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength pairCode (0,0)).comp p
  let work := Procedure.unarySub.comp
    (len.pair (Procedure.constant queryCode unaryCode 1))
  let b := (Procedure.listGet bondCode zeroBond).comp (i.pair bs)
  exact work.pair b

def entries (x : Environment) : List QuantumListSchedule.Entry :=
  (List.range x.1.length).map (fun i => entry (i,x))

noncomputable opaque entriesProgram : Procedure environmentCode
    (listCode QuantumListSchedule.entryCode) entries := by
  let bs := Procedure.first (listCode bondCode) (listCode (listCode pairCode))
  let n := (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength bondCode zeroBond).comp bs
  let tab : Procedure queryCode (listCode QuantumListSchedule.entryCode)
      (fun x => (List.range x.1).map (fun i => entry (i,x.2))) :=
    Procedure.tabulate (f := fun x i => entry (i,x)) QuantumListSchedule.zeroEntry entryProgram
  exact (tab.comp (n.pair (Procedure.identity environmentCode))).congrFun (by intro x; rfl)

def value (A B : ℕ) (x : QuantumForkGridProgram.Cells) : QuantumListRouteProgram.State :=
  let d := QuantumForkRoutingData.value x
  ((x.1.1,x.1.2.2.1,entries (QuantumForkList.fullList x.1,QuantumRoutingFamily.coarse A B d)),
    (QuantumRoutingFamily.positions A B d).map qmaExpandedPoint,
    QuantumPortChainProgram.allRouted A B d)

noncomputable opaque program (A B : ℕ) : Procedure QuantumForkGridProgram.cellsCode
    QuantumListRouteProgram.stateCode (value A B) := by
  let s := Procedure.first QuantumForkList.stateCode (listCode pairCode)
  let n := QuantumForkList.countProgram.comp s
  let c := (Procedure.first ratCode QuantumForkList.groupsCode).comp
    ((Procedure.second (listCode bondCode) (prodCode ratCode QuantumForkList.groupsCode)).comp
      ((Procedure.second unaryCode
        (prodCode (listCode bondCode) (prodCode ratCode QuantumForkList.groupsCode))).comp s))
  let bs := QuantumForkRoutingData.fullProgram.comp s
  let d := QuantumForkRoutingData.program
  let ps := (QuantumRoutingFamily.coarseProgram A B).comp d
  let es := entriesProgram.comp (bs.pair ps)
  let positions := (Procedure.listMap (0,0) (0,0) QuantumPortChainProgram.centerProgram).comp
    ((QuantumRoutingFamily.positionsProgram A B).comp d)
  let paths := (QuantumPortChainProgram.allRoutedProgram A B).comp d
  exact (n.pair (c.pair es)).pair (positions.pair paths)

end ContinuumCoulomb.QuantumPortScheduleTape

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPackedSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Packing a finite exchange graph with a work counter retains its endpoints
and work exactly. This bridges the literal schedule to the geometric one. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPackedSchedule
open QuantumListSchedule
open scoped Classical

def layout (G : QMARationalExchangeGraph) {m : ℕ} (labels : G.Edge ≃ Fin m)
    (work : G.Edge → ℕ) {Γ : SimpleGraph (ℕ × ℕ)} (P : QMAPathEmbedding ⟨G,work⟩ Γ) :
    QuantumListRouteProgram.State :=
  (state G labels work,List.ofFn P.position,List.ofFn (fun i : Fin m =>
    (List.range (2*work (labels.symm i)+2)).map (P.point (labels.symm i))))

end ContinuumCoulomb.QuantumPackedSchedule

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSpatialPortProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal fixed-round realization of the computed spatial graph on its port
paths. The finite tape carries the actual spin positions throughout subdivision. -/

noncomputable section
namespace ContinuumCoulomb.QuantumSpatialPortProgram
open ExactQuantumFactoring.BitStackProgram QuantumForkList QuantumRouteCode

def initial (A D : ℕ) (x : QuantumForkGridProgram.PreparedInput) :
    QuantumListRouteProgram.State :=
  QuantumPortScheduleTape.value (spatialDensity A D) (27*spatialDensity A D)
    (QuantumForkGridProgram.output D x)

def value (A D : ℕ) (x : Input) : QuantumListRouteProgram.State :=
  QuantumListRouteProgram.iterate x.1 (rounds A D) (initial A D x.2)

noncomputable opaque initialProgram (A D : ℕ) :
    Procedure QuantumForkGridProgram.preparedCode QuantumListRouteProgram.stateCode
      (initial A D) :=
  (QuantumPortScheduleTape.program (spatialDensity A D) (27*spatialDensity A D)).comp
    (QuantumForkGridProgram.outputProgram D)

noncomputable opaque program (A D : ℕ) :
    Procedure inputCode QuantumListRouteProgram.stateCode (value A D) :=
  (QuantumListRouteProgram.iterateProgram (rounds A D)).comp
    ((Procedure.first ratCode QuantumForkGridProgram.preparedCode).pair
      ((initialProgram A D).comp (Procedure.second ratCode QuantumForkGridProgram.preparedCode)))

end ContinuumCoulomb.QuantumSpatialPortProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSpatialCrossingProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal composition from the prepared spatial input to the crossing
Hamiltonian, its physical positions, and the finite routing permission table. -/

noncomputable section
namespace ContinuumCoulomb.QuantumSpatialCrossingProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode
open QuantumForkList (spatialDensity)

abbrev Output := (QuantumListPathStep.Output × List Pair) × QuantumRoutingTable.Table
def outputCode : Output → List Bool :=
  prodCode (prodCode QuantumListPathStep.outputCode (listCode pairCode))
    QuantumRoutingTable.tableCode

def coarse (A D : ℕ) (x : Input) : QuantumPathTable.Input :=
  QuantumRoutingFamily.table (spatialDensity A D) (27*spatialDensity A D)
    (QuantumForkRoutingData.value (QuantumForkGridProgram.output D x.2))
def cells (A D : ℕ) (x : Input) : List Pair := QuantumDistinctCrossings.value (coarse A D x)
def table (A D : ℕ) (x : Input) : QuantumRoutingTable.Table := QuantumPathTable.compile (coarse A D x)
def oldPositions (A D : ℕ) (x : Input) : List Pair := (QuantumSpatialPortProgram.value A D x).2.1
def oldPacket (A D : ℕ) (x : Input) : QuantumListPathStep.Output :=
  let s := (QuantumSpatialPortProgram.value A D x).1
  (s.1,QuantumListSchedule.erase s.2.2,s.2.1)
def sites (A D : ℕ) (x : Input) : List QuantumCrossingListBlock.Sites :=
  QuantumCrossingSiteProgram.allSites (oldPositions A D x,cells A D x)
def crossingInput (A D : ℕ) (x : Input) : QuantumCrossingListLayer.Input :=
  QuantumCrossingSelectProgram.value (x.1,oldPacket A D x,sites A D x)
def positions (A D : ℕ) (x : Input) : List Pair :=
  QuantumCrossingPositionProgram.positions (cells A D x,oldPositions A D x)
def value (A D : ℕ) (x : Input) : Output :=
  ((QuantumCrossingListLayer.value (crossingInput A D x),positions A D x),table A D x)

noncomputable opaque coarseProgram (A D : ℕ) :
    Procedure inputCode QuantumPathTable.inputCode (coarse A D) :=
  (QuantumRoutingFamily.tableProgram (spatialDensity A D) (27*spatialDensity A D)).comp
    (QuantumForkRoutingData.program.comp ((QuantumForkGridProgram.outputProgram D).comp
      (Procedure.second ratCode QuantumForkGridProgram.preparedCode)))
noncomputable opaque cellsProgram (A D : ℕ) :
    Procedure inputCode (listCode pairCode) (cells A D) :=
  QuantumDistinctCrossings.program.comp (coarseProgram A D)
noncomputable opaque tableProgram (A D : ℕ) :
    Procedure inputCode QuantumRoutingTable.tableCode (table A D) :=
  QuantumPathTable.compileProgram.comp (coarseProgram A D)
noncomputable opaque oldPositionsProgram (A D : ℕ) :
    Procedure inputCode (listCode pairCode) (oldPositions A D) :=
  ((Procedure.first (listCode pairCode) (listCode (listCode pairCode))).comp
    (Procedure.second QuantumListSchedule.stateCode
      (prodCode (listCode pairCode) (listCode (listCode pairCode))))).comp
        (QuantumSpatialPortProgram.program A D)
noncomputable opaque oldPacketProgram (A D : ℕ) :
    Procedure inputCode QuantumListPathStep.outputCode (oldPacket A D) := by
  let s := (Procedure.first QuantumListSchedule.stateCode
    (prodCode (listCode pairCode) (listCode (listCode pairCode)))).comp
      (QuantumSpatialPortProgram.program A D)
  let n := (Procedure.first unaryCode
    (prodCode ratCode (listCode QuantumListSchedule.entryCode))).comp s
  let rest := (Procedure.second unaryCode
    (prodCode ratCode (listCode QuantumListSchedule.entryCode))).comp s
  let c := (Procedure.first ratCode (listCode QuantumListSchedule.entryCode)).comp rest
  let bs := QuantumListSchedule.eraseProgram.comp
    ((Procedure.second ratCode (listCode QuantumListSchedule.entryCode)).comp rest)
  exact n.pair (bs.pair c)
noncomputable opaque sitesProgram (A D : ℕ) :
    Procedure inputCode (listCode QuantumCrossingListBlock.sitesCode) (sites A D) :=
  QuantumCrossingSiteProgram.allSitesProgram.comp
    ((oldPositionsProgram A D).pair (cellsProgram A D))
noncomputable opaque crossingInputProgram (A D : ℕ) :
    Procedure inputCode QuantumCrossingListLayer.inputCode (crossingInput A D) :=
  QuantumCrossingSelectProgram.program.comp
    ((Procedure.first ratCode QuantumForkGridProgram.preparedCode).pair
      ((oldPacketProgram A D).pair (sitesProgram A D)))
noncomputable opaque positionsProgram (A D : ℕ) :
    Procedure inputCode (listCode pairCode) (positions A D) :=
  QuantumCrossingPositionProgram.positionsProgram.comp
    ((cellsProgram A D).pair (oldPositionsProgram A D))
noncomputable opaque program (A D : ℕ) : Procedure inputCode outputCode (value A D) :=
  ((QuantumCrossingListLayer.program.comp (crossingInputProgram A D)).pair
    (positionsProgram A D)).pair (tableProgram A D)

end ContinuumCoulomb.QuantumSpatialCrossingProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPlanarTapeProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Merge the physical crossing bonds and compute the short planar route
for every remaining pair of endpoints from the finite permission table. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPlanarTapeProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode MediatorListProgram

abbrev Input := QuantumSpatialCrossingProgram.Output
def inputCode : Input → List Bool := QuantumSpatialCrossingProgram.outputCode
abbrev Output := QuantumListPathStep.Output × (List Pair × List (List Pair))
def outputCode : Output → List Bool := prodCode QuantumListPathStep.outputCode
  (prodCode (listCode pairCode) (listCode (listCode pairCode)))

def merged (x : Input) : List Bond := QuantumListMerge.value x.1.1.1 x.1.1.2.1
def routeInput (x : Input) (e : Bond) : QuantumRouteSelectorProgram.Input :=
  (x.2,QuantumForkGridProgram.lookup x.1.2 e.1,QuantumForkGridProgram.lookup x.1.2 e.2.1)
def paths (x : Input) : List (List Pair) :=
  (merged x).map (fun e => QuantumRouteSelectorProgram.value (routeInput x e))
def value (x : Input) : Output := ((x.1.1.1,merged x,x.1.1.2.2),x.1.2,paths x)

noncomputable opaque packetProgram : Procedure inputCode QuantumListPathStep.outputCode
    (fun x => x.1.1) :=
  (Procedure.first QuantumListPathStep.outputCode (listCode pairCode)).comp
    (Procedure.first (prodCode QuantumListPathStep.outputCode (listCode pairCode))
      QuantumRoutingTable.tableCode)
noncomputable opaque positionsProgram : Procedure inputCode (listCode pairCode)
    (fun x => x.1.2) :=
  (Procedure.second QuantumListPathStep.outputCode (listCode pairCode)).comp
    (Procedure.first (prodCode QuantumListPathStep.outputCode (listCode pairCode))
      QuantumRoutingTable.tableCode)
noncomputable opaque tableProgram : Procedure inputCode QuantumRoutingTable.tableCode
    Prod.snd := Procedure.second _ _
noncomputable opaque nProgram : Procedure inputCode unaryCode (fun x => x.1.1.1) :=
  (Procedure.first unaryCode (prodCode (listCode bondCode) ratCode)).comp packetProgram
noncomputable opaque bondsProgram : Procedure inputCode (listCode bondCode)
    (fun x => x.1.1.2.1) :=
  ((Procedure.first (listCode bondCode) ratCode).comp
    (Procedure.second unaryCode (prodCode (listCode bondCode) ratCode))).comp packetProgram
noncomputable opaque constantProgram : Procedure inputCode ratCode (fun x => x.1.1.2.2) :=
  ((Procedure.second (listCode bondCode) ratCode).comp
    (Procedure.second unaryCode (prodCode (listCode bondCode) ratCode))).comp packetProgram
noncomputable opaque mergedProgram : Procedure inputCode (listCode bondCode) merged :=
  QuantumListMerge.valueProgram.comp (nProgram.pair bondsProgram)

noncomputable opaque routeInputProgram :
    Procedure (prodCode inputCode bondCode) QuantumRouteSelectorProgram.inputCode
      (fun x => routeInput x.1 x.2) := by
  let env := Procedure.first inputCode bondCode
  let e := Procedure.second inputCode bondCode
  let ps := positionsProgram.comp env
  let a := (Procedure.first Nat.bits (prodCode Nat.bits ratCode)).comp e
  let b := ((Procedure.first Nat.bits ratCode).comp
    (Procedure.second Nat.bits (prodCode Nat.bits ratCode))).comp e
  let get := Procedure.listGet pairCode (0,0)
  exact (tableProgram.comp env).pair ((get.comp (a.pair ps)).pair (get.comp (b.pair ps)))

noncomputable opaque routeProgram : Procedure (prodCode inputCode bondCode)
    (listCode pairCode) (fun x => QuantumRouteSelectorProgram.value (routeInput x.1 x.2)) :=
  QuantumRouteSelectorProgram.program.comp routeInputProgram

noncomputable opaque mapPathsProgram : Procedure (prodCode inputCode (listCode bondCode))
    (listCode (listCode pairCode))
    (fun x => x.2.map (fun e => QuantumRouteSelectorProgram.value (routeInput x.1 e))) :=
  Procedure.listMapWith (f := fun x e => QuantumRouteSelectorProgram.value (routeInput x e))
    zeroBond [] routeProgram

noncomputable opaque pathsProgram : Procedure inputCode (listCode (listCode pairCode)) paths :=
  (mapPathsProgram.comp ((Procedure.identity inputCode).pair mergedProgram)).congrFun
    (by intro x; rfl)

noncomputable opaque program : Procedure inputCode outputCode value :=
  (nProgram.pair (mergedProgram.pair constantProgram)).pair (positionsProgram.pair pathsProgram)

end ContinuumCoulomb.QuantumPlanarTapeProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumEvenTapeProgram
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.edges_length _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.lower_value _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.upper_value _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One literal even subdivision, with its reserved leaf and odd route tails. -/

noncomputable section
namespace ContinuumCoulomb.QuantumEvenTapeProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode MediatorListProgram

abbrev Input := ℚ × QuantumPlanarTapeProgram.Output
def inputCode : Input → List Bool := prodCode ratCode QuantumPlanarTapeProgram.outputCode
def stepInput (x : Input) : QuantumListPathStep.Input :=
  ((x.2.1.1,true,x.1,x.2.1.2.2),([],x.2.1.2.1))
def route (x : Input) (i : ℕ) : List Pair := (x.2.2.2.drop i).headD []
def blockInput (x : ℕ × Input) : QuantumListSchedule.BlockInput :=
  (QuantumListPathStep.parameters (stepInput x.2),x.1,
    4*((route x.2 x.1).length-1),(x.2.2.1.2.1.drop x.1).headD zeroBond)
def entries (x : Input) : List QuantumListSchedule.Entry :=
  ((List.range x.2.1.2.1.length).map (fun i => QuantumListSchedule.block (blockInput (i,x)))).flatten
def positions (x : Input) : List Pair :=
  x.2.2.1.map qmaLeafCenter++(x.2.2.2.map QuantumEvenListPieces.fresh).flatten
def paths (x : Input) : List (List Pair) := (x.2.2.2.map QuantumEvenListPieces.paths).flatten
def value (x : Input) : QuantumListRouteProgram.State :=
  ((QuantumListPathStep.count (stepInput x),QuantumListPathStep.constant (stepInput x),entries x),
    positions x,paths x)

noncomputable opaque precisionProgram : Procedure inputCode ratCode Prod.fst := Procedure.first _ _
noncomputable opaque dataProgram : Procedure inputCode QuantumPlanarTapeProgram.outputCode Prod.snd :=
  Procedure.second _ _
noncomputable opaque packetProgram : Procedure inputCode QuantumListPathStep.outputCode
    (fun x => x.2.1) := (Procedure.first _ _).comp dataProgram
noncomputable opaque geometryProgram : Procedure inputCode
    (prodCode (listCode pairCode) (listCode (listCode pairCode))) (fun x => x.2.2) :=
  (Procedure.second _ _).comp dataProgram
noncomputable opaque countProgram : Procedure inputCode unaryCode (fun x => x.2.1.1) :=
  (Procedure.first _ _).comp packetProgram
noncomputable opaque bondsProgram : Procedure inputCode (listCode bondCode) (fun x => x.2.1.2.1) :=
  ((Procedure.first (listCode bondCode) ratCode).comp
    (Procedure.second unaryCode (prodCode (listCode bondCode) ratCode))).comp packetProgram
noncomputable opaque constantProgram : Procedure inputCode ratCode (fun x => x.2.1.2.2) :=
  ((Procedure.second (listCode bondCode) ratCode).comp
    (Procedure.second unaryCode (prodCode (listCode bondCode) ratCode))).comp packetProgram
noncomputable opaque oldPositionsProgram : Procedure inputCode (listCode pairCode)
    (fun x => x.2.2.1) := (Procedure.first _ _).comp geometryProgram
noncomputable opaque oldPathsProgram : Procedure inputCode (listCode (listCode pairCode))
    (fun x => x.2.2.2) := (Procedure.second _ _).comp geometryProgram
noncomputable opaque stepInputProgram : Procedure inputCode QuantumListPathStep.inputCode stepInput :=
  (countProgram.pair ((Procedure.constant inputCode Procedure.boolCode true).pair
    (precisionProgram.pair constantProgram))).pair
      ((Procedure.constant inputCode (listCode bondCode) []).pair bondsProgram)

noncomputable opaque routeProgram : Procedure (prodCode unaryCode inputCode) (listCode pairCode)
    (fun x => route x.2 x.1) :=
  (Procedure.listGet (listCode pairCode) []).comp
    ((Procedure.unaryToBits.comp (Procedure.first unaryCode inputCode)).pair
      (oldPathsProgram.comp (Procedure.second unaryCode inputCode)))
noncomputable opaque workProgram : Procedure (prodCode unaryCode inputCode) unaryCode
    (fun x => 4*((route x.2 x.1).length-1)) :=
  Procedure.unaryMul.comp ((Procedure.constant _ unaryCode 4).pair
    (Procedure.unaryPred.comp
      ((ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength pairCode (0,0)).comp routeProgram)))
noncomputable opaque blockInputProgram : Procedure (prodCode unaryCode inputCode)
    QuantumListSchedule.blockInputCode blockInput := by
  let i := Procedure.first unaryCode inputCode
  let x := Procedure.second unaryCode inputCode
  let b := (Procedure.listGet bondCode zeroBond).comp
    ((Procedure.unaryToBits.comp i).pair (bondsProgram.comp x))
  let p := (QuantumListPathStep.parametersProgram.comp stepInputProgram).comp x
  exact p.pair (i.pair (workProgram.pair b))
noncomputable opaque blockProgram : Procedure (prodCode unaryCode inputCode)
    (listCode QuantumListSchedule.entryCode)
    (fun x => QuantumListSchedule.block (blockInput x)) :=
  QuantumListSchedule.blockProgram.comp blockInputProgram
noncomputable opaque entriesTabProgram : Procedure (prodCode unaryCode inputCode)
    (listCode (listCode QuantumListSchedule.entryCode))
    (fun x => (List.range x.1).map (fun i => QuantumListSchedule.block (blockInput (i,x.2)))) :=
  Procedure.tabulate (f := fun x i => QuantumListSchedule.block (blockInput (i,x))) [] blockProgram
noncomputable opaque bondCountProgram : Procedure inputCode unaryCode
    (fun x => x.2.1.2.1.length) :=
  (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength bondCode zeroBond).comp bondsProgram
noncomputable opaque entriesNestedProgram : Procedure inputCode
    (listCode (listCode QuantumListSchedule.entryCode))
    (fun x => (List.range x.2.1.2.1.length).map
      (fun i => QuantumListSchedule.block (blockInput (i,x)))) :=
  (entriesTabProgram.comp (bondCountProgram.pair (Procedure.identity inputCode))).congrFun
    (by intro x; rfl)
noncomputable opaque entriesProgram : Procedure inputCode
    (listCode QuantumListSchedule.entryCode) entries :=
  ((QuantumRawExchange.flattenProgram QuantumListSchedule.entryCode QuantumListSchedule.zeroEntry).comp
    entriesNestedProgram).congrFun (by intro x; rfl)

noncomputable opaque positionsProgram : Procedure inputCode (listCode pairCode) positions :=
  (Procedure.listAppend pairCode (0,0)).comp
    (((Procedure.listMap (0,0) (0,0) QuantumRouteLeafCode.centerProgram).comp oldPositionsProgram).pair
      ((QuantumRawExchange.flattenProgram pairCode (0,0)).comp
        ((Procedure.listMap [] [] QuantumEvenListPieces.freshProgram).comp oldPathsProgram)))
noncomputable opaque pathsProgram : Procedure inputCode (listCode (listCode pairCode)) paths :=
  (QuantumRawExchange.flattenProgram (listCode pairCode) []).comp
    ((Procedure.listMap [] [] QuantumEvenListPieces.pathsProgram).comp oldPathsProgram)
noncomputable opaque program : Procedure inputCode QuantumListRouteProgram.stateCode value :=
  (((QuantumListPathStep.countProgram.comp stepInputProgram).pair
    ((QuantumListPathStep.constantProgram.comp stepInputProgram).pair entriesProgram)).pair
      (positionsProgram.pair pathsProgram))

theorem erase_entries (x : Input) :
    QuantumListSchedule.erase (entries x)=QuantumListPathStep.bonds (stepInput x) := by
  unfold entries
  simp only [QuantumListSchedule.erase,List.map_flatten,List.map_map]
  change ((List.range x.2.1.2.1.length).map (fun i =>
    QuantumListSchedule.erase (QuantumListSchedule.block (blockInput (i,x))))).flatten=_
  simp_rw [QuantumListSchedule.erase_block]
  rfl

theorem value_valid (x : Input)
    (hb : SourceBondLists.bounded x.2.1.1 x.2.1.2.1) : QuantumListSchedule.Valid (value x).1 := by
  have hk : SourceBondLists.bounded x.2.1.1 ([] : List Bond) := by simp [SourceBondLists.bounded]
  have hkn : ∀ e ∈ ([] : List Bond), e.1≠e.2.1 := by simp
  constructor
  · change SourceBondLists.bounded (QuantumListPathStep.count (stepInput x))
      (QuantumListSchedule.erase (entries x))
    rw [erase_entries]
    exact QuantumListPathStep.bonds_bounded (stepInput x) hk hb
  · change ∀ e ∈ QuantumListSchedule.erase (entries x), e.1≠e.2.1
    rw [erase_entries]
    exact QuantumListPathStep.bonds_noLoops (stepInput x) hkn hb

end ContinuumCoulomb.QuantumEvenTapeProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumEvenTapeOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact three-entry order of the literal even-subdivision output. -/

noncomputable section
namespace ContinuumCoulomb.QuantumEvenTapeProgram
open QuantumListSchedule
open scoped Classical

abbrev Tags (x : Input) := Fin x.2.1.2.1.length × Fin 3
def tagValue (x : Input) (t : Tags x) : Entry :=
  (blockWork (blockInput (t.1.val,x)) t.2,
    QuantumListPathProgram.bond (blockBondInput (blockInput (t.1.val,x))) t.2)

theorem entries_nested (x : Input) : entries x=
    (List.ofFn (fun i : Fin x.2.1.2.1.length => block (blockInput (i.val,x)))).flatten := by
  apply congrArg List.flatten
  simpa only [List.length_range,List.getElem_range,Fin.val_cast] using
    (List.ofFn_getElem_eq_map (List.range x.2.1.2.1.length)
      (fun i => block (blockInput (i,x)))).symm

theorem entries_ofFn (x : Input) : entries x=
    List.ofFn (fun i : Fin (x.2.1.2.1.length*3) => tagValue x (finProdFinEquiv.symm i)) := by
  rw [ofFn_triples,entries_nested]
  rfl

theorem entries_length (x : Input) : (entries x).length=x.2.1.2.1.length*3 := by
  rw [entries_ofFn,List.length_ofFn]

def tagEquiv (x : Input) : Fin (entries x).length ≃ Tags x :=
  (finCongr (entries_length x)).trans finProdFinEquiv.symm

theorem tagEquiv_get (x : Input) (i : Fin (entries x).length) :
    (entries x).get i=tagValue x (tagEquiv x i) := by
  have hi : i.val<x.2.1.2.1.length*3 := by rw [← entries_length]; exact i.isLt
  have h := congrArg (fun xs : List Entry => xs[i.val]?) (entries_ofFn x)
  have hc : Fin.cast (entries_length x) i=⟨i.val,hi⟩ := Fin.ext rfl
  change (entries x).get i=tagValue x (finProdFinEquiv.symm (Fin.cast (entries_length x) i))
  rw [hc]
  simpa only [List.getElem?_eq_getElem i.isLt,List.getElem?_ofFn,dite_eq_left hi,
    Option.some.injEq,List.get_eq_getElem] using h

end ContinuumCoulomb.QuantumEvenTapeProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumEvenRouteLabels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit vertex and edge labels for the even subdivision of a planar route family. -/

noncomputable section
namespace ContinuumCoulomb.QuantumEvenRouteLabels
open MediatorGraph QuantumRouteCode
open scoped Classical

variable {G : QMARationalExchangeGraph} (P : QMAPlanarRouteData G)
    {m : ℕ} (labels : G.Edge ≃ Fin m)

def originalPath (i : Fin m) : List Pair :=
  (List.range (P.length (labels.symm i)+1)).map (P.point (labels.symm i))

end ContinuumCoulomb.QuantumEvenRouteLabels

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListLatticeProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal source serialization from the computed coordinate and bond tapes. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListLattice
open ExactQuantumFactoring.BitStackProgram MediatorListProgram QuantumRouteCode

noncomputable def packetProgram : Procedure inputCode QuantumLatticeSerialization.inputCode packet := by
  let ps := Procedure.first (listCode pairCode)
    (prodCode (listCode bondCode) QuantumLatticeSerialization.thresholdCode)
  let tail := Procedure.second (listCode pairCode)
    (prodCode (listCode bondCode) QuantumLatticeSerialization.thresholdCode)
  let xs := (Procedure.first (listCode bondCode) QuantumLatticeSerialization.thresholdCode).comp tail
  let t := (Procedure.second (listCode bondCode) QuantumLatticeSerialization.thresholdCode).comp tail
  let n := (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength pairCode (0,0)).comp ps
  let bonds := QuantumListMerge.valueProgram.comp (n.pair xs)
  let points := (Procedure.listMap (0,0) (0,0) coordinateProgram).comp ps
  exact points.pair (bonds.pair t)

noncomputable def program : Procedure inputCode binaryHeisenbergCodec.encode value :=
  QuantumLatticeSerialization.program.comp packetProgram

end ContinuumCoulomb.QuantumListLattice

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListRouteLattice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The final literal route tape is itself the serialized lattice source.
Its coordinate and edge order are the computed orders, and its exact scalar
offset is removed from both thresholds. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListRouteProgram
open QuantumListSchedule QuantumRouteCode MediatorListProgram
open ExactQuantumFactoring.BitStackProgram

noncomputable def latticeOutputProgram :
    Procedure (prodCode stateCode (prodCode ratCode ratCode)) binaryHeisenbergCodec.encode
      (fun x : State × (ℚ × ℚ) => latticeOutput x.1 x.2.1 x.2.2) :=
  QuantumListLattice.program.comp latticePacketProgram

end ContinuumCoulomb.QuantumListRouteProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFinalRoutingProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal fixed-round routing to the serialized square-lattice source. -/

noncomputable section
namespace ContinuumCoulomb.QuantumFinalRoutingProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode MediatorListProgram

def planar (A D : ℕ) (x : Input) : QuantumPlanarTapeProgram.Output :=
  QuantumPlanarTapeProgram.value (QuantumSpatialCrossingProgram.value A D x.1)
def even (A D : ℕ) (x : Input) : QuantumListRouteProgram.State :=
  QuantumEvenTapeProgram.value (x.1.1,planar A D x)
def routed (A D : ℕ) (x : Input) : QuantumListRouteProgram.State :=
  QuantumListRouteProgram.iterate x.1.1 rounds (even A D x)
def value (A D : ℕ) (x : Input) : BinaryHeisenberg :=
  QuantumListRouteProgram.latticeOutput (routed A D x) x.2.1 x.2.2

noncomputable opaque planarProgram (A D : ℕ) : Procedure inputCode
    QuantumPlanarTapeProgram.outputCode (planar A D) :=
  QuantumPlanarTapeProgram.program.comp
    ((QuantumSpatialCrossingProgram.program A D).comp spatialInputProgram)
noncomputable opaque evenProgram (A D : ℕ) : Procedure inputCode
    QuantumListRouteProgram.stateCode (even A D) :=
  QuantumEvenTapeProgram.program.comp (precisionProgram.pair (planarProgram A D))
noncomputable opaque routedProgram (A D : ℕ) : Procedure inputCode
    QuantumListRouteProgram.stateCode (routed A D) :=
  (QuantumListRouteProgram.iterateProgram rounds).comp (precisionProgram.pair (evenProgram A D))
noncomputable opaque program (A D : ℕ) : Procedure inputCode binaryHeisenbergCodec.encode
    (value A D) :=
  QuantumListRouteProgram.latticeOutputProgram.comp ((routedProgram A D).pair thresholdsProgram)

end ContinuumCoulomb.QuantumFinalRoutingProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumEvenTapeGeometry
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal even tape has the canonical reserved-leaf geometry, up to
its explicit vertex and triple-edge ordering. -/

noncomputable section
namespace ContinuumCoulomb.QuantumEvenTapeGeometry
open QuantumRouteCode QuantumListSchedule MediatorGraph
open scoped Classical

variable {G : QMARationalExchangeGraph} (P : QMAPlanarRouteData G)
    {m : ℕ} (labels : G.Edge ≃ Fin m) (N : ℚ)

def input : QuantumEvenTapeProgram.Input :=
  (N,((G.n,QuantumListGraph.packed G labels,G.constant),
    List.ofFn P.position,List.ofFn (QuantumEvenRouteLabels.originalPath P labels)))

theorem input_valid : Valid (QuantumEvenTapeProgram.value (input P labels N)).1 :=
  QuantumEvenTapeProgram.value_valid _ (QuantumListGraph.packed_bounded G labels)

theorem count_eq : (QuantumEvenTapeProgram.value (input P labels N)).1.1=G.n+m*2 := by
  change G.n+(QuantumListGraph.packed G labels).length*2=G.n+m*2
  simp only [QuantumListGraph.packed,List.length_ofFn]

theorem bonds_length : (input P labels N).2.1.2.1.length=m := by
  exact List.length_ofFn

def tripleEquiv : Fin (QuantumEvenTapeProgram.entries (input P labels N)).length ≃
      Fin m × Fin 3 :=
  (QuantumEvenTapeProgram.tagEquiv (input P labels N)).trans
    (Equiv.prodCongr (finCongr (bonds_length P labels N)) (Equiv.refl _))

def vertex : Fin (QuantumEvenTapeProgram.value (input P labels N)).1.1 ≃
    Fin (P.toEven.schedule N).graph.n :=
  (finCongr (count_eq P labels N)).trans (QuantumEvenRouteLabels.vertex labels)

def edge : (schedule (QuantumEvenTapeProgram.value (input P labels N)).1
    (input_valid P labels N)).graph.Edge ≃ (P.toEven.schedule N).graph.Edge :=
  (tripleEquiv P labels N).trans (QuantumEvenRouteLabels.edgeEquiv labels)

theorem route_eq (i : Fin m) : QuantumEvenTapeProgram.route (input P labels N) i.val=
    QuantumEvenRouteLabels.originalPath P labels i := by
  unfold QuantumEvenTapeProgram.route input
  rw [List.headD_eq_head?_getD,List.head?_drop,List.getElem?_ofFn]
  simp only [dite_eq_left i.isLt,Option.getD_some]

theorem source_eq (i : Fin m) :
    QuantumListSchedule.blockBondInput
      (QuantumEvenTapeProgram.blockInput (i.val,input P labels N))=
        (QuantumListPathStep.parameters (QuantumEvenTapeProgram.stepInput (input P labels N)),
          i.val,(G.left (labels.symm i)).val,(G.right (labels.symm i)).val,G.weight (labels.symm i)) := by
  unfold blockBondInput QuantumEvenTapeProgram.blockInput input QuantumListGraph.packed
  rw [List.headD_eq_head?_getD,List.head?_drop,List.getElem?_ofFn]
  simp only [dite_eq_left i.isLt,Option.getD_some]

theorem entry_tag (e : Fin (QuantumEvenTapeProgram.entries (input P labels N)).length) :
    (QuantumEvenTapeProgram.entries (input P labels N)).get e=
      (blockWork (QuantumEvenTapeProgram.blockInput
        ((tripleEquiv P labels N e).1.val,input P labels N)) (tripleEquiv P labels N e).2,
       QuantumListPathProgram.bond (blockBondInput (QuantumEvenTapeProgram.blockInput
        ((tripleEquiv P labels N e).1.val,input P labels N))) (tripleEquiv P labels N e).2) :=
  QuantumEvenTapeProgram.tagEquiv_get _ e

theorem literal_left (e : Fin (QuantumEvenTapeProgram.entries (input P labels N)).length) :
    finCongr (count_eq P labels N)
      ((schedule (QuantumEvenTapeProgram.value (input P labels N)).1
        (input_valid P labels N)).graph.left e)=tagLeft labels (tripleEquiv P labels N e) := by
  apply Fin.ext
  change ((QuantumEvenTapeProgram.entries (input P labels N)).get e).2.1=_
  rw [entry_tag]
  generalize tripleEquiv P labels N e=t
  rcases t with ⟨i,k⟩
  rw [source_eq]
  fin_cases k <;> simp [QuantumListPathProgram.bond,QuantumListPathProgram.left,tagLeft,
    QuantumListPathStep.parameters,QuantumEvenTapeProgram.stepInput,input,old_val,fresh_val]

theorem literal_right (e : Fin (QuantumEvenTapeProgram.entries (input P labels N)).length) :
    finCongr (count_eq P labels N)
      ((schedule (QuantumEvenTapeProgram.value (input P labels N)).1
        (input_valid P labels N)).graph.right e)=tagRight (G := G) (tripleEquiv P labels N e) := by
  apply Fin.ext
  change ((QuantumEvenTapeProgram.entries (input P labels N)).get e).2.2.1=_
  rw [entry_tag]
  generalize tripleEquiv P labels N e=t
  rcases t with ⟨i,k⟩
  rw [source_eq]
  fin_cases k <;> simp [QuantumListPathProgram.bond,QuantumListPathProgram.right,tagRight,
    QuantumListPathStep.parameters,QuantumEvenTapeProgram.stepInput,input,fresh_val]

theorem literal_work (e : Fin (QuantumEvenTapeProgram.entries (input P labels N)).length) :
    (schedule (QuantumEvenTapeProgram.value (input P labels N)).1
      (input_valid P labels N)).work e=
        QuantumEvenRouteLabels.work P labels (tripleEquiv P labels N e) := by
  change ((QuantumEvenTapeProgram.entries (input P labels N)).get e).1=_
  rw [entry_tag]
  generalize tripleEquiv P labels N e=t
  rcases t with ⟨i,k⟩
  change (if k=2 then 4*((QuantumEvenTapeProgram.route (input P labels N) i.val).length-1)-1
      else 0)=_
  rw [route_eq]
  simp only [QuantumEvenRouteLabels.originalPath,List.length_map,List.length_range,
    Nat.add_sub_cancel,QuantumEvenRouteLabels.work]

def relabel : QMAPathRelabeling
    (schedule (QuantumEvenTapeProgram.value (input P labels N)).1 (input_valid P labels N))
    (P.toEven.schedule N) where
  vertex := vertex P labels N
  edge := edge P labels N
  left e := (congrArg (QuantumEvenRouteLabels.vertex labels)
    (literal_left P labels N e)).trans (tag_left P labels N _)
  right e := (congrArg (QuantumEvenRouteLabels.vertex labels)
    (literal_right P labels N e)).trans (tag_right P labels N _)
  work e := (literal_work P labels N e).trans
    (QuantumEvenRouteLabels.work_eq P labels _).symm

def embedding : QMAPathEmbedding
    (schedule (QuantumEvenTapeProgram.value (input P labels N)).1 (input_valid P labels N)) :=
  (relabel P labels N).symm.transport (P.toEven.embedding N)

theorem entry_count : (QuantumEvenTapeProgram.entries (input P labels N)).length=m*3 := by
  rw [QuantumEvenTapeProgram.entries_length,bonds_length]

end ContinuumCoulomb.QuantumEvenTapeGeometry

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPaddedTableProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed-width algebraic coefficient tables, with exact normalization of
the padded words. Each local arity at most six uses a fixed finite program. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPaddedTable
open QuantumAlgebraicScalar QuantumFixedPauli
open ExactQuantumFactoring.BitStackProgram
open scoped Classical

attribute [local instance] OAI.ContinuumCoulomb.QuantumPaddedTable.finDecision
noncomputable opaque coefficientProgram (n m : ℕ) (w : Fin (n+m) → Fin 4) :
    Procedure matrixCode realCode (fun xs => coefficient n m xs w) := by
  by_cases h : Even (qmaPauliYCount (QuantumPaddedPauli.restrictWord n m w))
  · exact (realMulProgram.comp
      ((Procedure.constant matrixCode realCode (realRat (((4:ℚ)^m)⁻¹))).pair
        (realCoefficientProgram n (QuantumPaddedPauli.restrictWord n m w)))).congrFun
          (by intro xs; simp only [coefficient,h,ite_true, if_true,Function.comp_apply])
  · exact (Procedure.constant matrixCode realCode (realRat 0)).congrFun
      (by intro xs; simp only [coefficient,h,ite_false, if_false])

end ContinuumCoulomb.QuantumPaddedTable

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPaddedSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal padded history table has the same polynomial scalar budget
as the supported expansion, and its rational samples approximate the actual
full-space history energy. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPaddedHistory
open QuantumAlgebraicScalar QuantumFixedPauli QuantumAlgebraicHistory
open scoped BigOperators Classical

section ScalarTable

attribute [local instance] OAI.ContinuumCoulomb.QuantumPaddedHistory.finDecision
def scalar (c : QMACircuit) (hT : 0 < c.gates.length) (p : Term c) : RealScalar :=
  QuantumPaddedTable.coefficient (QuantumOrderedSupport.sites c hT p.1).length
    (6-(QuantumOrderedSupport.sites c hT p.1).length)
    (matrixData (orderedTable c hT p.1))
    (widthIndex _ (QuantumOrderedSupport.sites_length c hT p.1) p.2)

end ScalarTable

def sampledWeight (k : ℕ) (c : QMACircuit) (hT : 0 < c.gates.length) (p : Term c) : ℚ :=
  sample k (scalar c hT p)

end ContinuumCoulomb.QuantumPaddedHistory

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPaddedLabelProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed-arity local history packets: sparse numeric labels and sampled
algebraic coefficients share exactly the same fixed Pauli-word order. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPaddedLabelProgram
open QuantumAlgebraicScalar QuantumFixedPauli QuantumPaddedHistory
open QuantumOrderedLabelData
open ExactQuantumFactoring.BitStackProgram
open scoped Classical

noncomputable def labelsProgram (n m : ℕ) (w : Fin (n+m) → Fin 4) :
    Procedure (listCode Nat.bits) labelsCode (labels n m w) :=
  QuantumRawExchange.fixedListProgram (listCode Nat.bits) labelCode n _ (fun i =>
    ((Procedure.listGet Nat.bits 0).comp
      ((Procedure.constant (listCode Nat.bits) Nat.bits i.val).pair
        (Procedure.identity (listCode Nat.bits)))).pair
      (Procedure.constant (listCode Nat.bits) Nat.bits
        (QuantumPaddedPauli.paddedWord n m w i).val))

noncomputable opaque entryProgram (n m : ℕ) (w : Fin (n+m) → Fin 4) :
    Procedure inputCode QuantumOrderedLabelFamily.entryCode (entry n m w) :=
  ((labelsProgram n m w).comp indicesProgram).pair
    (sampleProgram.comp (precisionProgram.pair
      ((QuantumPaddedTable.coefficientProgram n m w).comp matrixProgram)))

noncomputable def packetProgram (n m : ℕ) :
    Procedure inputCode (listCode QuantumOrderedLabelFamily.entryCode) (packet n m) :=
  (QuantumRawExchange.fixedListProgram inputCode QuantumOrderedLabelFamily.entryCode
    (Fintype.card (Fin (n+m) → Fin 4))
    (fun i x => entry n m ((Fintype.equivFin (Fin (n+m) → Fin 4)).symm i) x)
    (fun i => entryProgram n m ((Fintype.equivFin (Fin (n+m) → Fin 4)).symm i))).congrFun
      (by intro x; simp only [packet,enumerate,List.map_ofFn,Function.comp_def])

noncomputable opaque uniformProgram : Procedure inputCode
    (listCode QuantumOrderedLabelFamily.entryCode) uniformPacket := by
  let count := Procedure.unaryToBits.comp
    ((ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength Nat.bits 0).comp indicesProgram)
  let test (n : ℕ) := Procedure.binaryEq.comp
    (count.pair (Procedure.constant inputCode Nat.bits n))
  exact (Procedure.conditional (test 0) (packetProgram 0 6)
    (Procedure.conditional (test 1) (packetProgram 1 5)
    (Procedure.conditional (test 2) (packetProgram 2 4)
    (Procedure.conditional (test 3) (packetProgram 3 3)
    (Procedure.conditional (test 4) (packetProgram 4 2)
    (Procedure.conditional (test 5) (packetProgram 5 1) (packetProgram 6 0))))))).congrFun
      (by intro x; simp only [uniformPacket,Function.comp_apply,id_eq,decide_eq_true_eq])

end ContinuumCoulomb.QuantumPaddedLabelProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPaddedLabelTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal concatenation of fixed-width history packets is an exact
enumeration of the actual padded history family.  The local pattern order is
allowed to depend on the support width; its explicit bijection is retained. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPaddedLabelProgram
open QuantumAlgebraicScalar QuantumFixedPauli QuantumPaddedHistory
open scoped Classical

attribute [local instance] OAI.ContinuumCoulomb.QuantumPaddedLabelProgram.tableFinDecision
def sourceInput (k : ℕ) (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c)) : Input :=
  (k,QuantumOrderedSupport.encodedSites c hT a,
    matrixData (QuantumAlgebraicHistory.orderedTable c hT a))

def sourceEntries (k : ℕ) (c : QMACircuit) (hT : 0 < c.gates.length) :
    List QuantumOrderedLabelFamily.Entry :=
  (List.ofFn (fun i : Fin (QuantumOrderedSourceIndex.referenceCount c) =>
    uniformPacket (sourceInput k c hT (QuantumOrderedSourceIndex.reference c i)))).flatten

def sourceTerms (c : QMACircuit) (hT : 0 < c.gates.length) :
    Fin (QuantumOrderedSourceIndex.referenceCount c*QuantumOrderedSourceIndex.patternCount) ≃ Term c :=
  finProdFinEquiv.symm.trans (Equiv.prodShear (QuantumOrderedSourceIndex.reference c)
    (fun i =>
      let a := QuantumOrderedSourceIndex.reference c i
      let hn := QuantumOrderedSupport.sites_length c hT a
      (packetPatterns _ hn).trans (widthIndex _ hn).symm))

def sourceWord (c : QMACircuit) (hT : 0 < c.gates.length) (p : Term c) :
    QuantumOrderedSupport.Qubit c → Fin 4 := word c hT p

end ContinuumCoulomb.QuantumPaddedLabelProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Natural cell lookups for the actual sparse history.  The reference
lookup uses the same time-grouped descriptors as the sampled Hamiltonian. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryCells
open QuantumHistoryDescriptors QuantumOrderedSourceIndex

def referenceCell (c : QMACircuit) (i : ℕ) : ℕ × ℕ :=
  gateCell c (timeValue (qmaSparseCircuit c) (orderedAt (qmaSparseCircuit c) i))

def qubitCell (c : QMACircuit) (j : ℕ) : ℕ × ℕ :=
  let s := qmaSparseCircuit c
  let refs := referenceWork s+1
  if j < refs then referenceCell c j else
  let k := j-refs
  if k < s.gates.length+2 then gateCell c (min (k-1) (s.gates.length-1)) else
    let w := k-(s.gates.length+2)
    (w/(c.work+1),w%(c.work+1))

def termCell (c : QMACircuit) (i : ℕ) : ℕ × ℕ :=
  let refs := referenceWork (qmaSparseCircuit c)+1
  referenceCell c (if i < refs then i else i-refs)

def qubitCells (c : QMACircuit) : List (ℕ × ℕ) :=
  (List.range (qubitCount (qmaSparseCircuit c))).map (qubitCell c)

def referenceCells (c : QMACircuit) : List (ℕ × ℕ) :=
  (List.range (referenceCount (qmaSparseCircuit c))).map (termCell c)

def value (c : QMACircuit) : QuantumOrderedCellProgram.State :=
  (qubitCells c,QuantumOrderedCellProgram.anchors patternCount (referenceCells c))

end ContinuumCoulomb.QuantumHistoryCells

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPropagationSupport
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal, duplicate-free five-site propagation support.  Lookup in its
encoded labels agrees with the zero extension used by the actual local core. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPropagationSupport
open QuantumHistoryBitProgram QuantumHistoryDiagonal QuantumOrderedSupport
open scoped Classical

theorem sites_finset (c : QMACircuit) (t : Fin c.gates.length) :
    (sites c t).toFinset=qmaPropagationSites c t := by
  rw [← propagationSites_finset c t]; ext x; simp [sites]

def supportEquiv (c : QMACircuit) (t : Fin c.gates.length) :
    Fin (sites c t).length ≃ {q // q∈qmaPropagationSites c t} :=
  (List.Nodup.getEquiv (sites c t) (sites_nodup c t)).trans
    (Equiv.subtypeEquivRight (fun q => by
      have he := congrArg (fun S : Finset (QMACircuitQubit c) => q∈S) (sites_finset c t)
      exact List.mem_toFinset.symm.trans (Iff.of_eq he)))

end ContinuumCoulomb.QuantumPropagationSupport

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryDeltaProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A polynomial exact-arithmetic program for the propagation delta entry.
Only equality scans depend on circuit size; the matrix arity stays local. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryDelta
open ExactQuantumFactoring.BitStackProgram QuantumAlgebraicScalar
open QuantumHistoryDiagonal QuantumCircuitCode QuantumHistoryDescriptors

noncomputable opaque program : Procedure inputCode scalarCode
    (fun x : Input => entry x.1 x.2.1.2 x.2.2) := by
  let zero := Procedure.constant inputCode scalarCode (rat 0)
  let one := Procedure.constant inputCode scalarCode (rat 1)
  let first := Procedure.conditional flippedProgram one zero
  let second := mulProgram.comp
    ((Procedure.conditional sameClockProgram one zero).pair gateEntryProgram)
  exact (Procedure.conditional guardProgram
    (subProgram.comp (first.pair second)) zero).congrFun (by
      intro x
      simp only [entry,Function.comp_apply]
      simp only [apply_ite rat])

end ContinuumCoulomb.QuantumHistoryDelta

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPropagationTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact fixed-size propagation tables and their adjoint-product.  The
largest table has five qubits, independently of the circuit work register. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPropagationTable
open ExactQuantumFactoring.BitStackProgram QuantumAlgebraicScalar QuantumFixedPauli
open QuantumAlgebraicHistory QuantumCircuitCode
open scoped Classical

noncomputable opaque entryProgram (n : ℕ) (s t : Fin n → Fin 2) :
    Procedure inputCode scalarCode (fun x => table n x s t) :=
  (QuantumHistoryDelta.program.comp (entryInputProgram n s t)).congrFun
    (by intro x; rfl)

noncomputable def tableProgram (n : ℕ) :
    Procedure inputCode matrixCode (fun x => matrixData (table n x)) :=
  QuantumFixedMatrix.dataProgram (β := Fin n → Fin 2) inputCode (table n)
    (QuantumPropagationTable.entryProgram n)

noncomputable def gramProgram (n : ℕ) : Procedure inputCode matrixCode
    (fun x => matrixData (matMul (adjoint (table n x)) (table n x))) :=
  ((QuantumFixedMatrix.gramProgram (Fin n → Fin 2)).comp
    (QuantumPropagationTable.tableProgram n)).congrFun
    (by intro x; exact QuantumFixedMatrix.gramData_matrixData (table n x))

def supportBasisEquiv (c : QMACircuit) (t : Fin c.gates.length) :
    (Fin (QuantumPropagationSupport.sites c t).length → Fin 2) ≃
      QMASupportBasis (qmaPropagationSites c t) :=
  (QuantumPropagationSupport.supportEquiv c t).arrowCongr (Equiv.refl (Fin 2))

end ContinuumCoulomb.QuantumPropagationTable

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPropagationOrder
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual ordered support has its reference bit first, followed by
the duplicate-free propagation support in its literal source order. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPropagationOrder
open QuantumOrderedSupport
open scoped Classical

theorem sites_eq (c : QMACircuit) (hT : 0 < c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1)) (t : Fin c.gates.length)
    (ht : qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i=term c t) :
    sites c hT (.inl i)=.inl i :: (QuantumPropagationSupport.sites c t).map Sum.inr := by
  change ((.inl i :: (distributedSites c (qmaFirstUseTime c)
    (qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i)).map Sum.inr) : List (Qubit c)).dedup=_
  rw [ht]
  change ((.inl i :: (propagationSites c t).map Sum.inr) : List (Qubit c)).dedup=_
  rw [List.dedup_cons_of_notMem (by simp),List.dedup_map_of_injective Sum.inr_injective]
  rfl

theorem length_eq (c : QMACircuit) (hT : 0 < c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1)) (t : Fin c.gates.length)
    (ht : qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i=term c t) :
    (sites c hT (.inl i)).length=(QuantumPropagationSupport.sites c t).length+1 := by
  simp only [sites_eq c hT i t ht,List.length_cons,List.length_map]

def firstIndex (c : QMACircuit) (hT : 0 < c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1)) (t : Fin c.gates.length)
    (ht : qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i=term c t) :
    Fin (sites c hT (.inl i)).length :=
  ⟨0,by rw [length_eq c hT i t ht]; omega⟩

def nextIndex (c : QMACircuit) (hT : 0 < c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1)) (t : Fin c.gates.length)
    (ht : qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i=term c t)
    (j : Fin (QuantumPropagationSupport.sites c t).length) :
    Fin (sites c hT (.inl i)).length :=
  ⟨j.val+1,by rw [length_eq c hT i t ht]; omega⟩

def referenceBit (c : QMACircuit) (hT : 0 < c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1)) (t : Fin c.gates.length)
    (ht : qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i=term c t)
    (s : Fin (sites c hT (.inl i)).length → Fin 2) : Fin 2 :=
  s (firstIndex c hT i t ht)

def localBits (c : QMACircuit) (hT : 0 < c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1)) (t : Fin c.gates.length)
    (ht : qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i=term c t)
    (s : Fin (sites c hT (.inl i)).length → Fin 2) :
    Fin (QuantumPropagationSupport.sites c t).length → Fin 2 :=
  fun j => s (nextIndex c hT i t ht j)

end ContinuumCoulomb.QuantumPropagationOrder

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPropagationSampler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal local propagation tables after adding the single reference bit.
The arity is fixed in each program; no ambient spin configurations are scanned. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPropagationSampler
open QuantumAlgebraicScalar QuantumAlgebraicHistory QuantumFixedPauli
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode
open scoped Classical

noncomputable opaque coefficientProgram : Procedure inputCode scalarCode
    (fun x => rat (coefficient x.1)) := by
  let c := Procedure.first circuitCode (prodCode Nat.bits (listCode Nat.bits))
  let work := Procedure.unaryToBits.comp (workProgram.comp c)
  let time := Procedure.unaryToBits.comp (QuantumHistoryDescriptors.timeProgram.comp c)
  let const (n : ℕ) := Procedure.constant inputCode Nat.bits n
  let inner := Procedure.binaryAdd.comp
    ((Procedure.binaryMul.comp ((const 14).pair (Procedure.successor.comp work))).pair (const 8))
  let n := Procedure.binaryMul.comp (inner.pair time)
  exact (ratProgram.comp (Procedure.natToRat.comp n)).congrFun (by
    intro x
    simp only [coefficient,Function.comp_apply,id_eq,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one,
      Nat.succ_eq_add_one])

noncomputable opaque oneReferenceProgram (a b : Fin 2) :
    Procedure scalarCode scalarCode (oneReference a b) := by
  let cr := Procedure.constant scalarCode scalarCode (identity a b)
  let ci := Procedure.constant scalarCode scalarCode (QuantumFixedPauli.pauli 2 a b)
  let minusI := Procedure.constant scalarCode scalarCode (neg imaginary)
  exact (addProgram.comp
    ((mulProgram.comp (cr.pair realPartProgram)).pair
      (mulProgram.comp (minusI.pair (mulProgram.comp (ci.pair imagPartProgram)))))).congrFun
        (by intro x; rfl)

noncomputable opaque entryProgram (m : ℕ) (s t : Fin (m+1) → Fin 2) :
    Procedure inputCode scalarCode (fun x => table m x s t) := by
  let core := (QuantumFixedPauli.entryProgram (fun j : Fin m => s j.succ)
    (fun j : Fin m => t j.succ)).comp (QuantumPropagationTable.gramProgram m)
  let scaled := mulProgram.comp (coefficientProgram.pair core)
  exact ((oneReferenceProgram (s 0) (t 0)).comp scaled).congrFun (by
    intro x
    simp only [Function.comp_apply,table,entry_matrixData])

noncomputable def tableProgram (m : ℕ) : Procedure inputCode matrixCode
    (fun x => matrixData (table m x)) :=
  QuantumFixedMatrix.dataProgram (β := Fin (m+1) → Fin 2) inputCode (table m)
    (QuantumPropagationSampler.entryProgram m)

noncomputable def tableListProgram (n : ℕ) : Procedure inputCode matrixCode (tableList n) := by
  cases n with
  | zero =>
    exact Procedure.constant inputCode matrixCode
      (matrixData (fun _ _ : Fin 0 → Fin 2 => rat 0))
  | succ m => exact QuantumPropagationSampler.tableProgram m

def basisEquiv (c : QMACircuit) (hT : 0 < c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1)) (t : Fin c.gates.length)
    (ht : qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i=QuantumPropagationOrder.term c t) :
    (Fin (QuantumOrderedSupport.sites c hT (.inl i)).length → Fin 2) ≃
      (Fin ((QuantumPropagationSupport.sites c t).length+1) → Fin 2) :=
  (finCongr (QuantumPropagationOrder.length_eq c hT i t ht)).arrowCongr (Equiv.refl _)

end ContinuumCoulomb.QuantumPropagationSampler

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumReferenceEdgeTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact local tables for the reference-chain edges.  Their only nontrivial
entry is the fixed two-spin expression (I-Y tensor Y)/2. -/

noncomputable section
namespace ContinuumCoulomb.QuantumReferenceEdgeTable
open QuantumAlgebraicScalar QuantumAlgebraicHistory QuantumHistoryDiagonal
open QuantumHistoryBitProgram QuantumFixedPauli
open ExactQuantumFactoring.BitStackProgram
open scoped Classical

noncomputable opaque entryProgram (n : ℕ) (s t : Fin n → Fin 2) :
    Procedure inputCode scalarCode (fun x => table n x s t) := by
  let index := Procedure.first Nat.bits (listCode Nat.bits)
  let evaluate (p : Procedure inputCode Nat.bits (fun x => x.1)) :=
    (matrixEntryProgram (QuantumFixedPauli.pauli 2)).comp
      (readPairProgram.comp (p.pair (dataProgram n s t)))
  let left := evaluate index
  let right := (matrixEntryProgram (QuantumFixedPauli.pauli 2)).comp
    (readPairProgram.comp ((Procedure.successor.comp index).pair (dataProgram n s t)))
  exact (mulProgram.comp ((Procedure.constant inputCode scalarCode (rat (1/2))).pair
    (subProgram.comp ((Procedure.constant inputCode scalarCode (identity s t)).pair
      (mulProgram.comp (left.pair right)))))).congrFun (by
    intro x
    simp only [table,Function.comp_apply,readPair,matrixEntry,Nat.succ_eq_add_one,bit_val])

noncomputable def tableProgram (n : ℕ) : Procedure inputCode matrixCode
    (fun x => matrixData (table n x)) :=
  QuantumFixedMatrix.dataProgram (β := Fin n → Fin 2) inputCode (table n)
    (QuantumReferenceEdgeTable.entryProgram n)

end ContinuumCoulomb.QuantumReferenceEdgeTable

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryTableProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Total local-table dispatcher for the literal history order.  Its seven
arity templates are fixed; only descriptor and short-label reads vary. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryTableProgram
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode QuantumHistoryDescriptors
open QuantumAlgebraicScalar QuantumFixedPauli
open scoped Classical

noncomputable opaque descriptorProgram : Procedure inputCode descriptorCode
    (fun x => orderedAt x.1 x.2.1) :=
  orderedAtProgram.comp (circuitProgram.pair indexProgram)

noncomputable opaque localTableProgram (n : ℕ) : Procedure inputCode matrixCode (localTable n) := by
  let diagonal := (QuantumHistoryDiagonal.tableProgram n).comp
    (circuitProgram.pair (descriptorProgram.pair labelsProgram))
  let time := (Procedure.second Nat.bits Nat.bits).comp descriptorProgram
  let propagation := (QuantumPropagationSampler.tableListProgram n).comp
    (circuitProgram.pair (time.pair ((Procedure.listTail Nat.bits).comp labelsProgram)))
  let edge := (QuantumReferenceEdgeTable.tableProgram n).comp
    ((Procedure.binarySub.comp (indexProgram.pair cutoffProgram)).pair labelsProgram)
  let localTest := Procedure.binaryLt.comp (indexProgram.pair cutoffProgram)
  let tag := (Procedure.first Nat.bits Nat.bits).comp descriptorProgram
  let diagonalTest := Procedure.binaryLt.comp
    (tag.pair (Procedure.constant inputCode Nat.bits 4))
  exact (Procedure.conditional localTest
    (Procedure.conditional diagonalTest diagonal propagation) edge).congrFun (by
      intro x
      simp only [localTable,Function.comp_apply,decide_eq_true_eq])

noncomputable opaque tableProgram : Procedure inputCode matrixCode table := by
  let count := Procedure.unaryToBits.comp
    ((ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength Nat.bits 0).comp labelsProgram)
  let test (n : ℕ) := Procedure.binaryEq.comp
    (count.pair (Procedure.constant inputCode Nat.bits n))
  exact (Procedure.conditional (test 0) (localTableProgram 0)
    (Procedure.conditional (test 1) (localTableProgram 1)
    (Procedure.conditional (test 2) (localTableProgram 2)
    (Procedure.conditional (test 3) (localTableProgram 3)
    (Procedure.conditional (test 4) (localTableProgram 4)
    (Procedure.conditional (test 5) (localTableProgram 5) (localTableProgram 6))))))).congrFun
      (by intro x; simp only [table,Function.comp_apply,id_eq,decide_eq_true_eq])

end ContinuumCoulomb.QuantumHistoryTableProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistorySamplerProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal polynomial generation of all sampled history packets.  The
runtime list is indexed by the unary number of source terms, not Hilbert-space
dimension; each local matrix uses one of seven fixed arity programs. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistorySamplerProgram
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode QuantumHistoryDescriptors
open QuantumAlgebraicScalar QuantumFixedPauli
open scoped Classical

noncomputable opaque packetProgram : Procedure (prodCode unaryCode inputCode)
    (listCode QuantumOrderedLabelFamily.entryCode) (fun x => packet x.2 x.1) := by
  let i := Procedure.unaryToBits.comp (Procedure.first unaryCode inputCode)
  let x := Procedure.second unaryCode inputCode
  let k := (Procedure.first unaryCode circuitCode).comp x
  let c := (Procedure.second unaryCode circuitCode).comp x
  let labels := supportLabelsProgram.comp (c.pair i)
  let matrix := QuantumHistoryTableProgram.tableProgram.comp (c.pair (i.pair labels))
  exact QuantumPaddedLabelProgram.uniformProgram.comp (k.pair (labels.pair matrix))

attribute [local instance] OAI.ContinuumCoulomb.QuantumHistorySamplerProgram.finDecision
noncomputable opaque program : Procedure inputCode
    (listCode QuantumOrderedLabelFamily.entryCode) entries := by
  let c := Procedure.second unaryCode circuitCode
  let nested := (Procedure.tabulate (f := fun x i => packet x i) [] packetProgram).comp
    ((countProgram.comp c).pair (Procedure.identity inputCode))
  exact ((QuantumRawExchange.flattenProgram QuantumOrderedLabelFamily.entryCode ([],0)).comp
    nested).congrFun (by
      intro x
      simp only [Function.comp_apply,id_eq,entries]
      apply congrArg List.flatten
      simpa only [List.length_range,List.getElem_range,Fin.val_cast] using
        (List.ofFn_getElem_eq_map (List.range (QuantumOrderedSourceIndex.referenceCount x.2))
          (packet x)).symm)

end ContinuumCoulomb.QuantumHistorySamplerProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedLabelCompile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal six-local sparse-word compiler followed by the rational
four-spin compiler.  Its only input is a precision, a unary qubit count,
and the ordered rational sparse-word list. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedLabelCompile
open ExactQuantumFactoring.BitStackProgram QuantumOrderedLabelFamily
open QuantumOrderedLabelTable
open scoped Classical

noncomputable opaque labelEntriesProgram : Procedure inputCode (listCode entryCode)
    labelEntries :=
  (Procedure.second unaryCode (listCode entryCode)).comp
    QuantumOrderedLabelPipeline.outputProgram

noncomputable opaque rawEntriesProgram : Procedure inputCode
    (listCode QuantumRawExchange.rawCode) rawEntries :=
  Procedure.comp (f := labelEntries) (g := classify) classifyProgram labelEntriesProgram

noncomputable opaque outputCountProgram : Procedure inputCode unaryCode outputCount :=
  (Procedure.first unaryCode (listCode entryCode)).comp QuantumOrderedLabelPipeline.outputProgram

noncomputable opaque outputProgram : Procedure inputCode
    (prodCode (listCode MediatorListProgram.bondCode) ratCode) output := by
  let input : Procedure inputCode QuantumRawExchange.scheduleCode rawInput :=
    outputCountProgram.pair
      ((Procedure.unaryToBits.comp precisionProgram).pair rawEntriesProgram)
  exact QuantumRawExchange.compileProgram.comp input

end ContinuumCoulomb.QuantumOrderedLabelCompile

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPaddedLabelEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual padded history packets, followed by the literal local and
four-spin compiler, have total full-space error at most nine over N. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPaddedLabelProgram
open QuantumPaddedHistory QuantumOrderedSourceIndex
open scoped Classical

def historyInput (c : QMACircuit) (hT : 0 < c.gates.length) (N : ℕ) :
    QuantumOrderedLabelFamily.Input :=
  (N,qubitCount c,sourceEntries (QuantumAlgebraicHistory.samplePrecision c N) c hT)

def historyOutput (c : QMACircuit) (hT : 0 < c.gates.length) (N : ℕ) :=
  QuantumOrderedLabelCompile.output (historyInput c hT N)

def historyQubits (c : QMACircuit) (hT : 0 < c.gates.length) (N : ℕ) : ℕ :=
  QuantumOrderedLabelCompile.qubitCount (historyInput c hT N)

end ContinuumCoulomb.QuantumPaddedLabelProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryPrecisionProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The prescribed sampling precision is computed in unary.  Composition
with the checked local sampler yields the actual early raw exchange compiler. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryPrecisionProgram
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode QuantumAlgebraicHistory

noncomputable opaque prepareProgram : Procedure inputCode QuantumOrderedLabelFamily.inputCode prepare :=
  inverseErrorProgram.pair ((sourceQubitsProgram.comp circuitProgram).pair
    (QuantumHistorySamplerProgram.program.comp (precisionProgram.pair circuitProgram)))

noncomputable opaque outputProgram : Procedure inputCode
    (prodCode (listCode MediatorListProgram.bondCode) ratCode) output :=
  QuantumOrderedLabelCompile.outputProgram.comp prepareProgram

noncomputable opaque outputCountProgram : Procedure inputCode unaryCode
    (fun x => QuantumOrderedLabelCompile.outputCount (prepare x)) :=
  QuantumOrderedLabelCompile.outputCountProgram.comp prepareProgram

noncomputable opaque physicalQubitsProgram : Procedure inputCode unaryCode physicalQubits :=
  (Procedure.unaryMul.comp ((Procedure.constant inputCode unaryCode 4).pair
    outputCountProgram)).congrFun (fun x => (physicalQubits_eq x).symm)

end ContinuumCoulomb.QuantumHistoryPrecisionProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSweepCellProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A polynomial program for the exact sweep tag list.  Only unary width
and the actual gate-list length control list generation. -/

noncomputable section
namespace ContinuumCoulomb.QuantumSweepCells
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode

noncomputable opaque repeatProgram : Procedure (listCode Nat.bits) (listCode Nat.bits)
    repeatColumns := by
  let n := Procedure.identity Nat.bits
  let nil := Procedure.constant Nat.bits (listCode Nat.bits) []
  let one := (Procedure.listCons Nat.bits).comp (n.pair nil)
  let two := (Procedure.listCons Nat.bits).comp (n.pair one)
  let three := (Procedure.listCons Nat.bits).comp (n.pair two)
  exact ((QuantumRawExchange.flattenProgram Nat.bits 0).comp
    (Procedure.listMap 0 [] three)).congrFun (by intro xs; rfl)

noncomputable opaque rowColumnsProgram : Procedure stageInputCode (listCode Nat.bits)
    (fun x => rowColumns x.2.1 (x.1-1-x.2.2.1) x.2.2.2) := by
  let rows := Procedure.first Nat.bits (prodCode unaryCode (prodCode Nat.bits gateCode))
  let tail := Procedure.second Nat.bits (prodCode unaryCode (prodCode Nat.bits gateCode))
  let width := (Procedure.first unaryCode (prodCode Nat.bits gateCode)).comp tail
  let rest := (Procedure.second unaryCode (prodCode Nat.bits gateCode)).comp tail
  let start := (Procedure.first Nat.bits gateCode).comp rest
  let gate := (Procedure.second Nat.bits gateCode).comp rest
  let order := Procedure.binarySub.comp
    ((Procedure.binarySub.comp (rows.pair
      (Procedure.constant stageInputCode Nat.bits 1))).pair start)
  let wb := Procedure.unaryToBits.comp width
  let xs := columnsProgram.comp (width.pair order)
  let cut := rowCutProgram.comp (wb.pair (order.pair gate))
  let front := repeatProgram.comp (takeProgram.comp (cut.pair xs))
  let back := repeatProgram.comp ((Procedure.listDrop Nat.bits).comp (cut.pair xs))
  let arrival := sweepIndexProgram.comp (wb.pair (order.pair
    (Procedure.binarySub.comp (cut.pair (Procedure.constant stageInputCode Nat.bits 1)))))
  let center := (Procedure.listCons Nat.bits).comp
    (arrival.pair (Procedure.constant stageInputCode (listCode Nat.bits) []))
  let first := (Procedure.listAppend Nat.bits 0).comp (front.pair center)
  exact (Procedure.listAppend Nat.bits 0).comp (first.pair back)

noncomputable opaque rowCellsProgram : Procedure stageInputCode (listCode pairCode)
    (fun x => rowCells x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  let tail := Procedure.second Nat.bits (prodCode unaryCode (prodCode Nat.bits gateCode))
  let rest := (Procedure.second unaryCode (prodCode Nat.bits gateCode)).comp tail
  let start := (Procedure.first Nat.bits gateCode).comp rest
  exact (Procedure.listMapWith (f := fun i j => (i,j)) 0 (0,0)
    (Procedure.identity pairCode)).comp (start.pair rowColumnsProgram)

noncomputable opaque sweepCellsProgram : Procedure sweepInputCode (listCode pairCode)
    (fun x => sweepCells x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  let rest := Procedure.second Nat.bits (prodCode unaryCode (prodCode Nat.bits (listCode gateCode)))
  let tail := (Procedure.second unaryCode (prodCode Nat.bits (listCode gateCode))).comp rest
  let gates := (Procedure.second Nat.bits (listCode gateCode)).comp tail
  let env := Procedure.second unaryCode sweepInputCode
  let index := Procedure.unaryToBits.comp (Procedure.first unaryCode sweepInputCode)
  let rows := (Procedure.first Nat.bits (prodCode unaryCode
    (prodCode Nat.bits (listCode gateCode)))).comp env
  let er := (Procedure.second Nat.bits (prodCode unaryCode
    (prodCode Nat.bits (listCode gateCode)))).comp env
  let width := (Procedure.first unaryCode (prodCode Nat.bits (listCode gateCode))).comp er
  let et := (Procedure.second unaryCode (prodCode Nat.bits (listCode gateCode))).comp er
  let start := (Procedure.first Nat.bits (listCode gateCode)).comp et
  let gs := (Procedure.second Nat.bits (listCode gateCode)).comp et
  let gate := (Procedure.listGet gateCode (.hadamard 0)).comp (index.pair gs)
  let stage := rowCellsProgram.comp (rows.pair (width.pair
    ((Procedure.binaryAdd.comp (start.pair index)).pair gate)))
  let table := Procedure.tabulate (f := fun (x : SweepInput) i =>
    rowCells x.1 x.2.1 (x.2.2.1+i) (readGate x.2.2.2 i)) [] stage
  exact ((QuantumRawExchange.flattenProgram pairCode (0,0)).comp
    (table.comp ((gateLengthProgram.comp gates).pair
      (Procedure.identity sweepInputCode)))).congrFun (by
        intro x
        simp only [Function.comp_apply,id_eq,sweepCells,List.flatMap_def])

noncomputable opaque valueProgram : Procedure circuitCode (listCode pairCode) value := by
  let c := nearestCircuitProgram
  let gs := gatesProgram.comp c
  let rows := Procedure.unaryToBits.comp (gateLengthProgram.comp gs)
  exact sweepCellsProgram.comp (rows.pair (workProgram.pair
    ((Procedure.constant circuitCode Nat.bits 0).pair gs)))

end ContinuumCoulomb.QuantumSweepCells

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryCellProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial generation of the exact ordered history cell arrays.  All
list loops are bounded by unary circuit counts; coordinate arithmetic is
binary. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryCells
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode QuantumHistoryDescriptors
open QuantumOrderedCellProgram QuantumRouteCode

noncomputable opaque gateCellProgram : Procedure inputCode pairCode
    (fun x => gateCell x.1 x.2) :=
  (Procedure.listGet pairCode (0,0)).comp
    ((Procedure.second circuitCode Nat.bits).pair
      (QuantumSweepCells.valueProgram.comp (Procedure.first circuitCode Nat.bits)))

noncomputable opaque referenceCellProgram : Procedure inputCode pairCode
    (fun x => referenceCell x.1 x.2) := by
  let c := Procedure.first circuitCode Nat.bits
  let i := Procedure.second circuitCode Nat.bits
  let sparse := sparseCircuitProgram.comp c
  let descriptor := orderedAtProgram.comp (sparse.pair i)
  let time := timeValueProgram.comp (sparse.pair descriptor)
  exact gateCellProgram.comp (c.pair time)

noncomputable opaque qubitCellProgram : Procedure inputCode pairCode
    (fun x => qubitCell x.1 x.2) := by
  let c := Procedure.first circuitCode Nat.bits
  let j := Procedure.second circuitCode Nat.bits
  let sparse := sparseCircuitProgram.comp c
  let refs := Procedure.successor.comp (referenceWorkProgram.comp sparse)
  let time := Procedure.unaryToBits.comp (timeProgram.comp sparse)
  let two := Procedure.constant inputCode Nat.bits 2
  let one := Procedure.constant inputCode Nat.bits 1
  let cutoff := Procedure.binaryAdd.comp (time.pair two)
  let k := Procedure.binarySub.comp (j.pair refs)
  let before := Procedure.binarySub.comp (k.pair one)
  let last := Procedure.binarySub.comp (time.pair one)
  let clock := Procedure.conditional (Procedure.binaryLe.comp (before.pair last)) before last
  let work := Procedure.binarySub.comp (k.pair cutoff)
  let modulus := Procedure.successor.comp (Procedure.unaryToBits.comp (workProgram.comp c))
  let coords := (Procedure.binaryDiv.comp (work.pair modulus)).pair
    (Procedure.binaryMod.comp (work.pair modulus))
  exact (Procedure.conditional (Procedure.binaryLt.comp (j.pair refs)) referenceCellProgram
    (Procedure.conditional (Procedure.binaryLt.comp (k.pair cutoff))
      (gateCellProgram.comp (c.pair clock)) coords)).congrFun (by
        intro x
        simp only [qubitCell,Function.comp_apply,id_eq,decide_eq_true_eq,min_def])

noncomputable opaque termCellProgram : Procedure inputCode pairCode
    (fun x => termCell x.1 x.2) := by
  let c := Procedure.first circuitCode Nat.bits
  let i := Procedure.second circuitCode Nat.bits
  let refs := Procedure.successor.comp (referenceWorkProgram.comp (sparseCircuitProgram.comp c))
  let index := Procedure.conditional (Procedure.binaryLt.comp (i.pair refs)) i
    (Procedure.binarySub.comp (i.pair refs))
  exact (referenceCellProgram.comp (c.pair index)).congrFun (by
    intro x
    simp only [termCell,Function.comp_apply,decide_eq_true_eq])

noncomputable def qubitEntryProgram :
    Procedure (prodCode unaryCode circuitCode) pairCode
      (fun x => qubitCell x.2 x.1) :=
  qubitCellProgram.comp ((Procedure.second unaryCode circuitCode).pair
    (Procedure.unaryToBits.comp (Procedure.first unaryCode circuitCode)))

noncomputable def termEntryProgram :
    Procedure (prodCode unaryCode circuitCode) pairCode
      (fun x => termCell x.2 x.1) :=
  termCellProgram.comp ((Procedure.second unaryCode circuitCode).pair
    (Procedure.unaryToBits.comp (Procedure.first unaryCode circuitCode)))

noncomputable opaque qubitCellsProgram : Procedure circuitCode (listCode pairCode) qubitCells :=
  ((Procedure.tabulate (f := fun c i => qubitCell c i) (0,0) qubitEntryProgram).comp
    ((QuantumHistoryPrecisionProgram.sourceQubitsProgram.comp sparseCircuitProgram).pair
      (Procedure.identity circuitCode))).congrFun (by intro c; rfl)

noncomputable opaque referenceCellsProgram :
    Procedure circuitCode (listCode pairCode) referenceCells :=
  ((Procedure.tabulate (f := fun c i => termCell c i) (0,0) termEntryProgram).comp
    ((QuantumHistorySamplerProgram.countProgram.comp sparseCircuitProgram).pair
      (Procedure.identity circuitCode))).congrFun (by intro c; rfl)

noncomputable opaque valueProgram : Procedure circuitCode stateCode value :=
  (qubitCellsProgram.pair ((anchorsProgram 4096).comp referenceCellsProgram)).congrFun (by
    intro c
    simp only [value,Function.comp_apply,patternCount_eq])

end ContinuumCoulomb.QuantumHistoryCells

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryFork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual history compiler produces a bounded loop-free exchange list.
Its initial subdivision and ordered fork rounds preserve the full-space
ground energy with the accumulated explicit error. -/

noncomputable section
namespace ContinuumCoulomb
open MediatorGraph QuantumRawExchange
open scoped BigOperators Classical

namespace QuantumPaddedLabelProgram
open QuantumPaddedHistory QuantumOrderedSourceIndex QuantumForkList

def forkState (c : QMACircuit) (hT : 0 < c.gates.length) (N D : ℕ) : State :=
  iterate (N:ℚ) D (initial (historyQubits c hT N) (historyOutput c hT N).1
    (historyOutput c hT N).2 (N:ℚ))

end QuantumPaddedLabelProgram
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryIncidence
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The sparse verifier history has uniformly bounded site incidence, even
with all 4096 padded Pauli patterns retained. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryIncidence
open QuantumOrderedIncidence
open scoped BigOperators Classical

theorem sparse_reference_bound (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates ≠ []) :
    Bounded (QuantumOrderedSupport.sites (qmaSparseCircuit c) hT) 576 := by
  intro q
  let ss : QMAReferenceTerm (qmaHistoryReferenceWork (qmaSparseCircuit c)) →
      Finset (QuantumOrderedSupport.Qubit (qmaSparseCircuit c)) :=
    fun a => (QuantumOrderedSupport.sites (qmaSparseCircuit c) hT a).toFinset
  have hlocal : ∀ a, ∀ j ∈ ss a,
      QMAGridCellsNear (qmaOrderedQubitCell c hT j) (qmaOrderedTermCell c hT a) := by
    intro a j hj
    apply qmaOrderedHistoryModel_spatial c hc hT hne a j
    exact (QuantumOrderedSupport.sites_finset (qmaSparseCircuit c) hT a) ▸ hj
  have h := qmaGrid_incidence_bound (qmaOrderedQubitCell c hT) (qmaOrderedTermCell c hT)
    ss hlocal (qmaOrderedTermCell_fiber_card c hT hne) q
  have hm (a : QMAReferenceTerm (qmaHistoryReferenceWork (qmaSparseCircuit c))) :
      q ∈ QuantumOrderedSupport.sites (qmaSparseCircuit c) hT a ↔ q ∈ ss a :=
    List.mem_toFinset.symm
  have he : count (QuantumOrderedSupport.sites (qmaSparseCircuit c) hT) q =
      (Finset.univ.filter (fun a : QMAReferenceTerm
        (qmaHistoryReferenceWork (qmaSparseCircuit c)) =>
          q ∈ ss a)).card := by
    rw [count,Finset.card_filter]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : q ∈ QuantumOrderedSupport.sites (qmaSparseCircuit c) hT a
    · rw [ite_eq_left ha,ite_eq_left ((hm a).mp ha)]
    · rw [ite_eq_right ha,ite_eq_right (mt (hm a).mpr ha)]
  exact he.trans_le (h.trans (by norm_num : 9*64 ≤ 576))

theorem sparse_padded_bound (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates ≠ []) :
    Bounded (fun p : QuantumPaddedHistory.Term (qmaSparseCircuit c) =>
      QuantumOrderedSupport.sites (qmaSparseCircuit c) hT p.1) 2359296 := by
  have h := padded_bound (ν := Fin 6 → Fin 4)
    (QuantumOrderedSupport.sites (qmaSparseCircuit c) hT)
    (sparse_reference_bound c hc hT hne)
  simp only [Fintype.card_fun,Fintype.card_fin] at h
  have hn : 4^6*576=2359296 := by norm_num
  rw [hn] at h
  exact h

end ContinuumCoulomb.QuantumHistoryIncidence

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistorySpatial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual sparse verifier history has a fixed-density, degree-three
spatial exchange output. Its energy is that of the literal fork compiler. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistorySpatial
open QuantumPaddedHistory QuantumOrderedSourceIndex QuantumPaddedLabelProgram
open QuantumForkList
open scoped Classical

theorem padded_anchor_density (c : QMACircuit)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates ≠ [])
    (p : QMAGridCell (qmaNearestCircuit c).gates.length c.work) :
    (Finset.univ.filter (fun a : Term (qmaSparseCircuit c) =>
      qmaOrderedTermCell c hT a.1=p)).card ≤ 4096*64 := by
  rw [qmaProductFilter_card (β := Fin 6 → Fin 4) (fun a => qmaOrderedTermCell c hT a=p)]
  simp only [Fintype.card_fun,Fintype.card_fin]
  exact Nat.mul_le_mul_left _ (qmaOrderedTermCell_fiber_card c hT hne p)

def input (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates ≠ []) (N : ℕ) :
    SpatialInput (qmaNearestCircuit c).gates.length c.work rawDensity historyDegree := by
  change SpatialInput _ _ (4*(45+3717*(4096*64))) (6+22*(12544*2359296))
  exact QuantumOrderedOutputSpatial.input (qubits (qmaSparseCircuit c))
    (sourceTerms (qmaSparseCircuit c) hT)
    (fun p : Term (qmaSparseCircuit c) => QuantumOrderedSupport.sites (qmaSparseCircuit c) hT p.1)
    (sourceWord (qmaSparseCircuit c) hT)
    (sampledWeight (QuantumAlgebraicHistory.samplePrecision (qmaSparseCircuit c) N)
      (qmaSparseCircuit c) hT)
    (fun p => QuantumOrderedSupport.sites_length (qmaSparseCircuit c) hT p.1)
    (fun p => QuantumOrderedSupport.sites_nodup (qmaSparseCircuit c) hT p.1)
    (qmaOrderedQubitCell c hT) (fun p => qmaOrderedTermCell c hT p.1)
    (by intro p; simpa only [Finset.filter_congr_decidable] using qmaOrderedQubitCell_fiber_card c hT hne p)
    (by intro p; simpa only [Finset.filter_congr_decidable] using padded_anchor_density c hT hne p)
    (fun p i hi => qmaOrderedHistoryModel_spatial c hc hT hne p.1 i
      ((QuantumOrderedSupport.sites_finset (qmaSparseCircuit c) hT p.1) ▸
        List.mem_toFinset.mpr hi))
    (by decide) (QuantumHistoryIncidence.sparse_padded_bound c hc hT hne) N

def model (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates ≠ []) (N : ℕ) := (input c hc hT hne N).model

theorem model_degree (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates ≠ []) (N : ℕ)
    (v : Fin (model c hc hT hne N).n) :
    qmaGraphDegree (model c hc hT hne N).left (model c hc hT hne N).right v ≤ 3 :=
  (input c hc hT hne N).model_degree v

end ContinuumCoulomb.QuantumHistorySpatial

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryLattice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual sparse verifier compiler, through the specified planar lattice.
The final precision pays for every early and routing error; the scalar offset
is removed from both thresholds exactly. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistorySpatial
open QuantumPaddedLabelProgram QuantumForkList QuantumAlgebraicHistory
open scoped Classical

-- Keep the fixed density symbolic; expanding it as a numeral is unnecessary.
attribute [local irreducible] spatialDensity

def latticePrecision (c : QMACircuit) : ℕ := finalPrecision totalRounds (qmaSparseCircuit c)

end ContinuumCoulomb.QuantumHistorySpatial

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryRawCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The computed cell array has the exact physical-spin order of the raw
history compiler, including all six mediator layers and the four-spin blocks. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryCells
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode QuantumOrderedSourceIndex
open QuantumOrderedLabelTable QuantumOrderedSpatialComplete

def rawCells (c : QMACircuit) : List (ℕ × ℕ) := QuantumOrderedRawCells.value (value c)

noncomputable opaque rawCellsProgram : Procedure circuitCode
    (listCode QuantumRouteCode.pairCode) rawCells :=
  QuantumOrderedRawCells.program.comp valueProgram

end ContinuumCoulomb.QuantumHistoryCells

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistorySpatialProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal sampled history and its row/column labels are combined into
the exact prepared input of the fixed-round fork compiler. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistorySpatialProgram
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode
open QuantumHistoryPrecisionProgram

def sparseInput (x : Input) : Input := (x.1,qmaSparseCircuit x.2)

noncomputable opaque sparseInputProgram : Procedure inputCode inputCode sparseInput :=
  inverseErrorProgram.pair (sparseCircuitProgram.comp circuitProgram)

def initialInput (x : Input) : QuantumForkList.InitialInput :=
  ((x.1:ℚ),physicalQubits (sparseInput x),output (sparseInput x))

noncomputable opaque initialInputProgram : Procedure inputCode
    QuantumForkList.initialInputCode initialInput :=
  (Procedure.natToRat.comp (Procedure.unaryToBits.comp inverseErrorProgram)).pair
    ((physicalQubitsProgram.comp sparseInputProgram).pair
      (outputProgram.comp sparseInputProgram))

def prepared (x : Input) : QuantumForkGridProgram.PreparedInput :=
  (initialInput x,QuantumHistoryCells.rawCells x.2)

noncomputable opaque cellsProgram : Procedure inputCode
    (listCode QuantumRouteCode.pairCode) (QuantumHistoryCells.rawCells ∘ Prod.snd) :=
  @Procedure.comp Input QMACircuit (List QuantumRouteCode.Pair)
    inputCode circuitCode (listCode QuantumRouteCode.pairCode)
    Prod.snd QuantumHistoryCells.rawCells QuantumHistoryCells.rawCellsProgram circuitProgram

noncomputable opaque preparedProgram : Procedure inputCode
    QuantumForkGridProgram.preparedCode prepared := by
  refine (@Procedure.pair Input QuantumForkList.InitialInput (List QuantumRouteCode.Pair)
    inputCode QuantumForkList.initialInputCode (listCode QuantumRouteCode.pairCode)
    initialInput (QuantumHistoryCells.rawCells ∘ Prod.snd)
    initialInputProgram cellsProgram).congrFun ?_
  intro x
  simp only [prepared,Function.comp_apply]

end ContinuumCoulomb.QuantumHistorySpatialProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPreparedCircuit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The particular sparse, nonempty circuit used by the history reduction,
with its literal program and unchanged verifier acceptance probability. -/

noncomputable section
namespace ContinuumCoulomb
open ExactQuantumFactoring.BitStackProgram
open BinaryEncoding

theorem qmaPreparedCircuit_wellFormed (c : QMACircuit) (hc : c.WellFormed) :
    (qmaPreparedCircuit c).WellFormed :=
  qmaSparseCircuit_wellFormed _ (qmaNonemptyCircuit_wellFormed c hc)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryPreparedProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The nonempty circuit, final unary precision, exact history cells and
rational promise thresholds are assembled without semantic input oracles. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryPreparedProgram
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode

def precision (c : QMACircuit) : ℕ :=
  QuantumHistorySpatial.latticePrecision (qmaNonemptyCircuit c)

def time (c : QMACircuit) : ℕ := (qmaPreparedCircuit c).gates.length

noncomputable opaque timeProgram : Procedure circuitCode unaryCode time :=
  QuantumHistoryDescriptors.timeProgram.comp preparedCircuitProgram

noncomputable opaque precisionProgram : Procedure circuitCode unaryCode precision :=
  ((QuantumAlgebraicHistory.finalPrecisionProgram QuantumHistorySpatial.totalRounds).comp
    timeProgram).congrFun (by
      intro c
      simp only [precision,QuantumHistorySpatial.latticePrecision,
        QuantumAlgebraicHistory.finalPrecision,time,qmaPreparedCircuit,Function.comp_apply])

def scheduled (c : QMACircuit) : QuantumHistorySpatialProgram.Input :=
  (precision c,qmaNonemptyCircuit c)

noncomputable opaque scheduledProgram : Procedure circuitCode
    QuantumHistorySpatialProgram.inputCode scheduled :=
  precisionProgram.pair nonemptyProgram

def prepared (c : QMACircuit) : QuantumForkGridProgram.PreparedInput :=
  QuantumHistorySpatialProgram.prepared (scheduled c)

noncomputable opaque preparedProgram : Procedure circuitCode
    QuantumForkGridProgram.preparedCode prepared :=
  QuantumHistorySpatialProgram.preparedProgram.comp scheduledProgram

def thresholds (c : QMACircuit) : ℚ × ℚ :=
  (QuantumAlgebraicHistory.xzYesThreshold (qmaPreparedCircuit c),
    QuantumAlgebraicHistory.xzNoThreshold (qmaPreparedCircuit c))

noncomputable opaque thresholdTimeProgram : Procedure circuitCode ratCode
    (fun c => ((time c+1:ℕ):ℚ)) :=
  Procedure.natToRat.comp (Procedure.unaryToBits.comp
    (Procedure.unarySuccessor.comp timeProgram))

noncomputable opaque lowerProgram : Procedure circuitCode ratCode
    (fun c => (thresholds c).1) := by
  let denominator := Procedure.ratMul.comp
    ((Procedure.constant circuitCode ratCode 20).pair thresholdTimeProgram)
  exact (Procedure.ratDiv.comp
    ((Procedure.constant circuitCode ratCode 7).pair denominator)).congrFun (by
      intro c
      simp only [thresholds,QuantumAlgebraicHistory.xzYesThreshold,time,
        Function.comp_apply,Nat.cast_add,Nat.cast_one])

noncomputable opaque upperProgram : Procedure circuitCode ratCode
    (fun c => (thresholds c).2) := by
  let denominator := Procedure.ratMul.comp
    ((Procedure.constant circuitCode ratCode 60).pair thresholdTimeProgram)
  exact (Procedure.ratDiv.comp
    ((Procedure.constant circuitCode ratCode 23).pair denominator)).congrFun (by
      intro c
      simp only [thresholds,QuantumAlgebraicHistory.xzNoThreshold,time,
        Function.comp_apply,Nat.cast_add,Nat.cast_one])

noncomputable opaque thresholdsProgram : Procedure circuitCode
    (prodCode ratCode ratCode) thresholds :=
  (lowerProgram.pair upperProgram).congrFun (by intro c; rfl)

def finalInput (c : QMACircuit) : FinalInput :=
  (((precision c:ℚ),prepared c),thresholds c)

noncomputable opaque rationalPrecisionProgram : Procedure circuitCode ratCode
    (fun c => (precision c:ℚ)) :=
  Procedure.natToRat.comp (Procedure.unaryToBits.comp precisionProgram)

noncomputable opaque finalInputProgram : Procedure circuitCode finalInputCode finalInput :=
  (rationalPrecisionProgram.pair preparedProgram).pair thresholdsProgram

end ContinuumCoulomb.QuantumHistoryPreparedProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPreparedVerifier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual verifier generator followed by the sparse-circuit compiler.
The unary size certificate is computed from the original input and retained
through the arbitrary given generator before its binary registers are parsed. -/

noncomputable section
namespace ContinuumCoulomb
open Turing ExactQuantumFactoring.BitStackProgram BinaryEncoding

namespace QuantumVerifier

noncomputable def generateUnary (V : QuantumVerifier) :
    TM2ComputableInPolyTime (id : BitString → List Bool)
      QuantumCircuitCode.circuitCode V.generate := by
  let prefixed := TM2Composition.computable (prefixProgram V).toTM2
    (QuantumUnaryPrefix.computable V.uniform)
  let parsed := TM2Composition.computable prefixed QuantumCircuitCode.boundedInput.toTM2
  have he : QuantumCircuitCode.cap ∘
      ((fun x : ℕ × BitString => (x.1,V.generate x.2)) ∘
        (fun x : BitString => (V.size.eval x.length,x))) = V.generate := by
    funext x
    exact QuantumCircuitCode.cap_eq_of_wellFormed _ _ (V.wellFormed x)
      (by
        change (V.generate x).work ≤ V.size.eval x.length
        have hh := V.size_bound x
        omega)
  change TM2ComputableInPolyTime id QuantumCircuitCode.circuitCode
    (QuantumCircuitCode.cap ∘
      ((fun x : ℕ × BitString => (x.1,V.generate x.2)) ∘
        (fun x : BitString => (V.size.eval x.length,x)))) at parsed
  rw [he] at parsed
  exact parsed

end QuantumVerifier
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistorySourceProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete literal circuit-to-source map, including nonempty padding,
sampling precision, fork and route programs, and rational thresholds. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistorySourceProgram
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode BinaryEncoding

def value : QMACircuit → BinaryHeisenberg :=
  QuantumFinalRoutingProgram.value QuantumHistorySpatial.rawDensity
    QuantumPaddedLabelProgram.historyDegree ∘ QuantumHistoryPreparedProgram.finalInput

noncomputable opaque inputProgram : Procedure circuitCode
    QuantumFinalRoutingProgram.inputCode QuantumHistoryPreparedProgram.finalInput := by
  rw [← inputCode_eq]
  exact QuantumHistoryPreparedProgram.finalInputProgram

noncomputable opaque program : Procedure circuitCode binaryHeisenbergCodec.encode value :=
  @Procedure.comp QMACircuit QuantumFinalRoutingProgram.Input BinaryHeisenberg
    circuitCode QuantumFinalRoutingProgram.inputCode binaryHeisenbergCodec.encode
    QuantumHistoryPreparedProgram.finalInput
    (QuantumFinalRoutingProgram.value QuantumHistorySpatial.rawDensity
      QuantumPaddedLabelProgram.historyDegree)
    (QuantumFinalRoutingProgram.program QuantumHistorySpatial.rawDensity
      QuantumPaddedLabelProgram.historyDegree) inputProgram

noncomputable def certificate : Turing.TM2ComputableInPolyTime circuitCode
    binaryHeisenbergCodec.encode value := program.toTM2

def fromVerifier (V : QuantumVerifier) : BitString → BinaryHeisenberg := value ∘ V.generate

noncomputable def fromVerifier_uniform (V : QuantumVerifier) :
    Turing.TM2ComputableInPolyTime (id : BitString → List Bool)
      binaryHeisenbergCodec.encode (fromVerifier V) :=
  TM2Composition.computable V.generateUnary certificate

end ContinuumCoulomb.QuantumHistorySourceProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumScheduleCrossingGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Match the complete literal crossing packet to the canonical port crossing
geometry. The input schedule and the crossing cells may have arbitrary orders. -/

noncomputable section
namespace ContinuumCoulomb.QuantumScheduleCrossingGeometry
open QuantumCrossingSelectProgram QuantumCrossingListLayer
open scoped Classical

variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)
    (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D)
    (s : QuantumListSchedule.State) (hs : QuantumListSchedule.Valid s)
    (E : QMAPathRelabeling (QuantumListSchedule.schedule s hs) (P.schedule.iterate N D))
    {r : ℕ} (cell : Fin r ≃ Fin P.crossingCells.card)

def layer : QMARationalCrossingLayer r :=
  computedLayer ((QuantumListSchedule.graph s hs).crossingSelection
    (site P N hD s hs E cell) (site_injective P N hD s hs E cell)) (Equiv.refl _)

def input : QuantumCrossingListLayer.Input :=
  QuantumCrossingSelectProgram.value (N,(s.1,QuantumListSchedule.erase s.2.2,s.2.1),
    List.ofFn (encodedSites (site P N hD s hs E cell)))

def vertex : Fin (actualGraph (layer P N hD s hs E cell) N (Equiv.refl _)).n ≃
    Fin (P.crossingOutput N hD).n :=
  (actualVertex (layer P N hD s hs E cell) N (Equiv.refl _)).trans
    ((layer P N hD s hs E cell).vertexRelabel (P.portCrossingSelection N hD).layer E.vertex cell)

end ContinuumCoulomb.QuantumScheduleCrossingGeometry

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSpatialCrossingGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The computed crossing cells and terminal scans use exactly the physical
port geometry, with finite permutations accounting for their output order. -/

noncomputable section
namespace ContinuumCoulomb.QuantumSpatialCrossingProgram
open QuantumForkList QuantumRouteCode
open scoped Classical

variable {rows width A D : ℕ} (I : SpatialInput rows width A D)
    (hA : 0 < spatialDensity A D) (N : ℚ)

def edgeList := List.ofFn (fun e : I.model.Term => e)

theorem length_bound (e : I.model.Term) :
    (I.model.portRouteData hA I.model_degree).length e ≤
      QuantumSpatialPortProgram.rounds A D := by
  rw [← QuantumSpatialPortProgram.rounds_eq]
  exact I.model.bufferedPath_length I.model_degree e

end ContinuumCoulomb.QuantumSpatialCrossingProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryRoutedEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full-space history comparison and verifier implications for the
literal circuit-to-lattice output, including empty-circuit preparation. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistorySourceProgram
open QuantumHistorySpatial QuantumHistoryPreparedProgram QuantumPaddedLabelProgram
open QuantumAlgebraicHistory

def routedState (c : QMACircuit) : QuantumListRouteProgram.State :=
  QuantumFinalRoutingProgram.routed rawDensity historyDegree (finalInput c)

end ContinuumCoulomb.QuantumHistorySourceProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPlanarTapeSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual merged planar tape and the canonical crossing graph have
the same unordered edges, with an explicit finite edge equivalence. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPlanarTapeGeometry
open QuantumPlanarTapeProgram
open scoped Classical

def rawGraph (x : Input) (hb : SourceBondLists.bounded x.1.1.1 x.1.1.2.1)
    (hn : ∀ e ∈ x.1.1.2.1, e.1 ≠ e.2.1) : QMARationalExchangeGraph :=
  QuantumListGraph.ofBonds x.1.1.1 x.1.1.2.1 x.1.1.2.2 hb hn

def graph (x : Input) (hn : ∀ e ∈ x.1.1.2.1, e.1 ≠ e.2.1) : QMARationalExchangeGraph :=
  QuantumListGraph.ofBonds x.1.1.1 (merged x) x.1.1.2.2
    (QuantumListMerge.bounded _ _) (QuantumListMerge.noLoops hn)

theorem graph_source (x : Input) (hb : SourceBondLists.bounded x.1.1.1 x.1.1.2.1)
    (hn : ∀ e ∈ x.1.1.2.1, e.1 ≠ e.2.1) (e : (graph x hn).Edge) :
    ∃ f : (rawGraph x hb hn).Edge,
      s((graph x hn).left e,(graph x hn).right e) =
        s((rawGraph x hb hn).left f,(rawGraph x hb hn).right f) := by
  obtain ⟨b,hb',hpair⟩ := QuantumListMerge.value_edge_source x.1.1.1 x.1.1.2.1
    (List.get_mem (merged x) e)
  obtain ⟨f,hf⟩ := List.mem_iff_get.mp hb'
  refine ⟨f,fin_pair_eq ?_⟩
  change s(((merged x).get e).1,((merged x).get e).2.1) =
    s((x.1.1.2.1.get f).1,(x.1.1.2.1.get f).2.1)
  rwa [hf]

theorem graph_target (x : Input) (hb : SourceBondLists.bounded x.1.1.1 x.1.1.2.1)
    (hn : ∀ e ∈ x.1.1.2.1, e.1 ≠ e.2.1) (f : (rawGraph x hb hn).Edge) :
    ∃ e : (graph x hn).Edge,
      s((graph x hn).left e,(graph x hn).right e) =
        s((rawGraph x hb hn).left f,(rawGraph x hb hn).right f) := by
  obtain ⟨b,hb',hpair⟩ := QuantumListMerge.value_edge_target hb (List.get_mem x.1.1.2.1 f)
  obtain ⟨e,he⟩ := List.mem_iff_get.mp hb'
  refine ⟨e,fin_pair_eq ?_⟩
  change s(((QuantumListMerge.value x.1.1.1 x.1.1.2.1).get e).1,
    ((QuantumListMerge.value x.1.1.1 x.1.1.2.1).get e).2.1) =
    s((x.1.1.2.1.get f).1,(x.1.1.2.1.get f).2.1)
  rwa [he]

theorem graph_simple (x : Input) (hn : ∀ e ∈ x.1.1.2.1, e.1 ≠ e.2.1) :
    (graph x hn).Simple := by
  intro e f hef
  have h := QuantumListMerge.value_simple hn e f hef
  constructor
  · rintro ⟨hl,hr⟩
    exact h.1 ⟨congrArg Fin.val hl,congrArg Fin.val hr⟩
  · rintro ⟨hl,hr⟩
    exact h.2 ⟨congrArg Fin.val hl,congrArg Fin.val hr⟩

section Canonical
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)
    (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D) (x : Input)
    (hb : SourceBondLists.bounded x.1.1.1 x.1.1.2.1)
    (hn : ∀ e ∈ x.1.1.2.1, e.1 ≠ e.2.1)
    (vertex : Fin x.1.1.1 ≃ Fin (P.crossingOutput N hD).n)
    (forward : ∀ e : (rawGraph x hb hn).Edge, ∃ f : (P.crossingOutput N hD).Edge,
      s(vertex ((rawGraph x hb hn).left e),vertex ((rawGraph x hb hn).right e)) =
        s((P.crossingOutput N hD).left f,(P.crossingOutput N hD).right f))
    (backward : ∀ f : (P.crossingOutput N hD).Edge, ∃ e : (rawGraph x hb hn).Edge,
      s(vertex ((rawGraph x hb hn).left e),vertex ((rawGraph x hb hn).right e)) =
        s((P.crossingOutput N hD).left f,(P.crossingOutput N hD).right f))

include forward in
theorem canonical_source (e : (graph x hn).Edge) :
    ∃ f : (P.crossingOutput N hD).merge.Edge,
      s(vertex ((graph x hn).left e),vertex ((graph x hn).right e)) =
        s((P.crossingOutput N hD).merge.left f,(P.crossingOutput N hD).merge.right f) := by
  obtain ⟨a,ha⟩ := graph_source x hb hn e
  obtain ⟨b,hb'⟩ := forward a
  obtain ⟨f,hf⟩ := (P.crossingOutput N hD).merge_unordered_target b
  exact ⟨f,(qmaUnorderedPair_map vertex ha).trans (hb'.trans hf.symm)⟩

include backward in
theorem canonical_target (f : (P.crossingOutput N hD).merge.Edge) :
    ∃ e : (graph x hn).Edge,
      s(vertex ((graph x hn).left e),vertex ((graph x hn).right e)) =
        s((P.crossingOutput N hD).merge.left f,(P.crossingOutput N hD).merge.right f) := by
  obtain ⟨b,hb'⟩ := (P.crossingOutput N hD).merge_unordered_source f
  obtain ⟨a,ha⟩ := backward b
  obtain ⟨e,he⟩ := graph_target x hb hn a
  exact ⟨e,(qmaUnorderedPair_map vertex he).trans (ha.trans hb'.symm)⟩

def edge : (graph x hn).Edge ≃ (P.crossingOutput N hD).merge.Edge :=
  QuantumEndpointRelabel.edge vertex (graph_simple x hn) (P.crossingOutput N hD).merge_simple
    (canonical_source P N hD x hb hn vertex forward)
    (canonical_target P N hD x hb hn vertex backward)

theorem edge_endpoints (e : (graph x hn).Edge) :
    s(vertex ((graph x hn).left e),vertex ((graph x hn).right e)) =
      s((P.crossingOutput N hD).merge.left (edge P N hD x hb hn vertex forward backward e),
        (P.crossingOutput N hD).merge.right (edge P N hD x hb hn vertex forward backward e)) :=
  QuantumEndpointRelabel.chooseEdge_spec
    (G := (P.crossingOutput N hD).merge) (H := graph x hn) vertex
    (canonical_source P N hD x hb hn vertex forward) e

end Canonical
end ContinuumCoulomb.QuantumPlanarTapeGeometry

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPlanarTapeGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The emitted planar tape is the exact coordinate and path array of a
bounded planar family, in its literal merged-edge order. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

namespace QuantumPlanarTapeGeometry
open QuantumPlanarTapeProgram QuantumRouteCode

section Geometry
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)
    (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D) (x : Input)
    (hb : SourceBondLists.bounded x.1.1.1 x.1.1.2.1)
    (hn : ∀ e ∈ x.1.1.2.1, e.1 ≠ e.2.1)
    (vertex : Fin x.1.1.1 ≃ Fin (P.crossingOutput N hD).n)
    (forward : ∀ e : (rawGraph x hb hn).Edge, ∃ f : (P.crossingOutput N hD).Edge,
      s(vertex ((rawGraph x hb hn).left e),vertex ((rawGraph x hb hn).right e)) =
        s((P.crossingOutput N hD).left f,(P.crossingOutput N hD).right f))
    (backward : ∀ f : (P.crossingOutput N hD).Edge, ∃ e : (rawGraph x hb hn).Edge,
      s(vertex ((rawGraph x hb hn).left e),vertex ((rawGraph x hb hn).right e)) =
        s((P.crossingOutput N hD).left f,(P.crossingOutput N hD).right f))
    (havoid : ∀ i : P.Interior, ∀ v, P.cell i ≠ P.position v)
    (hpositive : ∀ v, 0 < (P.position v).1 ∧ 0 < (P.position v).2)

def route : QMAPlanarRouteData (graph x hn) :=
  P.selectorPlanarRoute (H := graph x hn) N hD havoid vertex (edge P N hD x hb hn vertex forward backward)
    (edge_endpoints P N hD x hb hn vertex forward backward) hpositive

end Geometry
end QuantumPlanarTapeGeometry
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

def graph (s : ℕ) (d : BinaryHeisenberg) (hd : d.Valid) :
    Bonds (output s d).vertices (graphEdgeCount s d hd) :=
  (finalGraph (sourceFamily s d hd) (sourceBound s d) (size d^s)).castSites
    (by simpa only [BinaryHeisenberg.toSource] using (vertices_eq s d hd).symm)

end ContinuumCoulomb.SourcePositiveProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceGraphIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual contact-site enumeration and the finite Hubbard graph use
one common electron index. Relabeling changes no bond or coordinate order. -/

noncomputable section
namespace ContinuumCoulomb.SourcePositiveProgram
open MediatorIteration ContactMediator SourceMetadataProgram

theorem rawSiteCount (s : ℕ) (d : BinaryHeisenberg) (hd : d.Valid) :
    (geometricSource s d hd).vertices+(geometricSource s d hd).edges*2+
      (geometricSource s d hd).edges*2*2+
        ((geometricSource s d hd).edges*2+(geometricSource s d hd).edges*2*2)*2 =
      (output s d).vertices := by
  simpa only [geometricSource,SourceNormalizedSpectrum.lattice,BinaryHeisenberg.toSource]
    using (vertices_eq s d hd).symm

def siteEquiv (s : ℕ) (d : BinaryHeisenberg) (hd : d.Valid) :
    GlobalSite (geometricSource s d hd) ≃ Fin (output s d).vertices :=
  finCongr (rawSiteCount s d hd)

@[irreducible] def indexedGraph (s : ℕ) (d : BinaryHeisenberg) (hd : d.Valid) {m : ℕ}
    (hm : (output s d).vertices=m+1) : Bonds (m+1) (graphEdgeCount s d hd) :=
  (graph s d hd).castSites hm

def indexedSites (s : ℕ) (d : BinaryHeisenberg) (hd : d.Valid) {m : ℕ}
    (hm : (output s d).vertices=m+1) : GlobalSite (geometricSource s d hd) ≃ Fin (m+1) :=
  (siteEquiv s d hd).trans (finCongr hm)

end ContinuumCoulomb.SourcePositiveProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceUnitCoulomb
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal source-to-unit-Coulomb packaging. The physical nuclei and the
full affine threshold pair use the same calibrated sites, amplification,
mesh and exact rational slab dimensions. -/

namespace ContinuumCoulomb.SourceUnitCoulomb
open ExactQuantumFactoring.BitStackProgram

noncomputable def input (rho C : ℕ) (ε c : ℚ) (s p h k A B q r : ℕ)
    (d : BinaryHeisenberg) : AffinePhysicalOutput.Input :=
  (SourceNuclearProgram.input rho C ε c s p h k A B r d,
    SourcePhysicalThreshold.input rho C ε c s p h k A B q d)

noncomputable def value (rho C U F K : ℕ) (ε c : ℚ) (s p h k A B q r : ℕ)
    (d : BinaryHeisenberg) : UnitCoulomb :=
  AffinePhysicalOutput.value rho U F K (input rho C ε c s p h k A B q r d)

noncomputable opaque inputProgram (rho C : ℕ) (ε c : ℚ) (s p h k A B q r : ℕ) :
    Procedure binaryHeisenbergCodec.encode AffinePhysicalOutput.inputCode
      (input rho C ε c s p h k A B q r) :=
  (SourceNuclearProgram.inputProgram rho C ε c s p h k A B r).pair
    (SourcePhysicalThreshold.inputProgram rho C ε c s p h k A B q)

noncomputable opaque program (rho C U F K : ℕ) (ε c : ℚ) (s p h k A B q r : ℕ) :
    Procedure binaryHeisenbergCodec.encode unitCoulombCodec.encode
      (value rho C U F K ε c s p h k A B q r) :=
  (AffinePhysicalOutput.program rho U F K).comp (inputProgram rho C ε c s p h k A B q r)

end ContinuumCoulomb.SourceUnitCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourcePhysicalPromise
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Promise transfer for the literal physical thresholds. The retained
source margin absorbs the finite, continuum, and scalar-evaluation errors. -/

noncomputable section
namespace ContinuumCoulomb.SourcePhysicalThreshold

def exactSourceEnergy (rho C : ℕ) (eps c : ℚ) (s p h k A B q : ℕ)
    (d : BinaryHeisenberg) (v : ℝ) : ℝ :=
  let x := input rho C eps c s p h k A B q d
  CenteredPhysicalThreshold.actualOffset rho x.1 +
    (CenteredPhysicalThreshold.amplification rho x.1.1.1 : ℝ) *
      ((x.2.1 : ℝ)^2 * (SourcePositiveProgram.energy (SourcePositiveProgram.output s d) -
        (x.2.2.2.sum : ℝ)) - v)

end ContinuumCoulomb.SourcePhysicalThreshold

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceHubbardEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite-spin and scalar-offset identities for the literal source
bond list. These identify the Hubbard center with the computed threshold center. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb
open MediatorIteration HubbardGlobal

namespace SourcePhysicalThreshold

def exactHubbardEnergy (rho C : ℕ) (eps c : ℚ) (s p h k A B q : ℕ)
    (d : BinaryHeisenberg) {m r : ℕ} (u : Fin (m+1) → CoulombPairSum.Point)
    (F : Bonds (m+1) r) (t : Fin r → ℝ) : ℝ :=
  let x := input rho C eps c s p h k A B q d
  CenteredPhysicalThreshold.actualOffset rho x.1 +
    (SourceNuclearProgram.amplification rho k d : ℝ)*
      (hubbardFermionBottom m (localizedCoulombProfile (GaussianFrequency.frequency rho) 0)
        (localizedOffsiteCoulomb (GaussianFrequency.frequency rho)
          (fun i => PlanarForcingProgram.position (u i))) F.left F.right t -
      CoulombPairSum.exactTotal (GaussianFrequency.frequency rho) u)

end SourcePhysicalThreshold
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceIndexedSites
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal nuclear program's planar sites, expressed in the same
index type as its finite Hubbard graph. -/

noncomputable section
namespace ContinuumCoulomb.SourceNuclearProgram
open SourceMetadataProgram ContactMediator

def contactSpacing (c : ℚ) (k : ℕ) (d : BinaryHeisenberg) : ℚ :=
  AutomaticCalibration.spacing c k (CalibrationMesh.base (SourceContactProgram.size d))

def contactLengths (rho C : ℕ) (eps c : ℚ) (s p k A B : ℕ)
    (d : BinaryHeisenberg) (hd : d.Valid) : GlobalEdge (geometricSource s d hd) → ℚ :=
  CalibratedContactProgram.graphLengths rho eps c k A B
    (CalibrationMesh.base (SourceContactProgram.size d))
    (PrefactorCalibration.precision C (SourceContactProgram.size d^p))
    (geometricSource s d hd)
    (PrefactorSourceContactProgram.weights (CalibrationMesh.prefactor rho) s d hd)

def rawSites (rho C : ℕ) (eps c : ℚ) (s p h k A B : ℕ)
    (d : BinaryHeisenberg) (hd : d.Valid) : GlobalSite (geometricSource s d hd) → ℚ×ℚ :=
  ContactCalibratedGeometry.position (geometricSource s d hd) (SourceContactProgram.size d^h)
    (contactSpacing c k d) (contactLengths rho C eps c s p k A B d hd)

def indexedCoordinates (rho C : ℕ) (eps c : ℚ) (s p h k A B : ℕ)
    (d : BinaryHeisenberg) (hd : d.Valid) {m : ℕ}
    (hm : (SourcePositiveProgram.output s d).vertices=m+1) : Fin (m+1) → ℚ×ℚ :=
  fun i => rawSites rho C eps c s p h k A B d hd
    ((SourcePositiveProgram.indexedSites s d hd hm).symm i)

end ContinuumCoulomb.SourceNuclearProgram

end

end OAI
end


